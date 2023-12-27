import z3
import wlang.ast
import argparse
import sys

def lessthanequal(op):
    return op == '<='

def greaterthanequal(op):
    return op == '>='

def lessthan(op):
    return op == '<'

def equal(op):
    return op == '='

def checkadd(node):
    return node.op == '+'

def checksubtract(node):
    return node.op == '-'

def checkmulti(node):
    return node.op == '*'

def checknot(node):
    return node.op == 'not'

def checkand(node):
    return node.op == 'and'
    
def check_int_const(node):
    return isinstance(node, wlang.ast.IntConst)

def check_bool_const(node):
    return isinstance(node, wlang.ast.BoolConst)

def check_int_var(node):
    return isinstance(node, wlang.ast.IntVar)

def check_relexp(node):
    return isinstance(node, wlang.ast.RelExp)
    
def check_bexp(node):
    return isinstance(node, wlang.ast.BExp)
    
def check_aexp(node):
    return isinstance(node, wlang.ast.AExp)

class DartState:
    def __init__(self, solver=None):
        self.concrete_state = {}
        self.symbolic_state = {} 
        self.path_constraints = []  
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

    def fork(self):
        new_state = DartState()
        new_state.concrete_state = self.concrete_state.copy()
        new_state.symbolic_state = self.symbolic_state.copy()
        new_state.path_constraints = self.path_constraints.copy()
        return new_state

    def add_condition(self, constraint):
        self.path_constraints.append(constraint)

    def is_it_unsat(self):
        return self._solver.check() == z3.unsat


class DartExec(wlang.ast.AstVisitor):
    def __init__(self):
        self.loop_bound = 10

    def run(self, ast, state):
        if not state.is_it_unsat():
            result = self.visit(ast, state=state)
            if result is not None:
                yield result

    def visit_IfStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        cond_val = self.compute(node.cond, state)
        cond_id = id(node.cond)

        sym_cond = state.symbolic_state.get(cond_id, z3.BoolVal(cond_val))

        then_state, else_state = state.fork(), state.fork()
        then_state.add_condition(sym_cond)
        else_state.add_condition(z3.Not(sym_cond))

        if cond_val:
            new_state = self.visit(node.then_stmt, state=then_state)
            if new_state != None:
                state.concrete_state.update(new_state.concrete_state)
                state.symbolic_state.update(new_state.symbolic_state)
                kwargs['state'] = state
        else:
            if node.has_else():
                new_state = self.visit(node.else_stmt, state=else_state)
                if new_state != None:
                    state.concrete_state.update(new_state.concrete_state)
                    state.symbolic_state.update(new_state.symbolic_state)
                    kwargs['state'] = state

    def visit_AsgnStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        var_name = node.lhs.name
        state.symbolic_state[str(var_name)] = z3.FreshInt(str(var_name))
        state.concrete_state[str(var_name)] = self.compute(node.rhs, state)
        return state

    def visit_BExp(self, node, *args, **kwargs):
        state = kwargs['state']
        return self.compute_bexp(node, state)

    def visit_RelExp(self, node, *args, **kwargs):
        state = kwargs['state']
        lhs = self.compute(node.arg(0), state)
        rhs = self.compute(node.arg(1), state)
        return self.compute_rexp(node.op, lhs, rhs)

    def visit_IntVar(self, node, *args, **kwargs):
        state = kwargs['state']
        var_name = node.name
        if var_name in state.concrete_state:
            return state.concrete_state[var_name]
        return state.symbolic_state[var_name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return node.val

    def visit_IntConst(self, node, *args, **kwargs):
        return node.val

    def visit_AssertStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        cond = self.visit(node.cond, *args, **kwargs)
        if self.compute(node.cond, st) == False:
            new_state = st.fork()
            new_state.add_condition(cond)
            st.mk_error()
        else:
            st.add_condition(cond)
        return st    

    def visit_AssumeStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        cond = self.visit(node.cond, *args, **kwargs)
        print("chak")
        print(node.cond)
        if self.compute(node.cond, st) == False:
            new_state = st.fork()
            new_state.add_condition(cond)
            st.mk_error()
        else:
            st.add_condition(cond)
        return st    

    def visit_HavocStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        for var_name in node.vars:
            state.symbolic_state[str(var_name)] = z3.Int(str(var_name))
            # set variable to some concrete value in concrete state
            state.concrete_state[str(var_name)] = 0

    def visit_StmtList(self, node, *args, **kwargs):
        for stmt in node.stmts:
            self.visit(stmt, state = kwargs['state'])

    def visit_WhileStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        upper_bound_iterations = 10
        loop_condition = self.compute(node.cond, state)
        loop_place = state.fork()
        current_iteration=0
        while self.compute(node.cond, state) and current_iteration < upper_bound_iterations:
            current_iteration += 1
            self.visit(node.body, state=loop_place)
            loop_condition = self.compute(node.cond, loop_place)

        if loop_place != None:
            state.concrete_state.update(loop_place.concrete_state)
            state.symbolic_state.update(loop_place.symbolic_state)

        if current_iteration >= upper_bound_iterations:
            print("iterations done")
    
    def compute(self, node, state):
        if check_int_const(node):
            return node.val
        elif check_bool_const(node):
            return node.val
        elif check_int_var(node):
            return state.concrete_state[node.name]
        elif check_relexp(node):
            lhs = self.compute(node.arg(0), state)
            rhs = self.compute(node.arg(1), state)
            return self.compute_rexp(node.op, lhs, rhs)
        elif check_bexp(node):
            return self.compute_bexp(node, state)
        return self.compute_aexp(node, state)
        
    def compute_rexp(self, op, lhs, rhs):
        if lessthanequal(op):
            return lhs <= rhs
        elif lessthan(op):
            return lhs < rhs
        elif equal(op):
            return lhs == rhs
        elif greaterthanequal(op):
            return lhs >= rhs
        return lhs > rhs

    def compute_bexp(self, node, state):
        if checknot(node):
            return not self.compute(node.args[0], state)
        elif checkand(node):
            return all(self.compute(arg, state) for arg in node.args)
        return any(self.compute(arg, state) for arg in node.args)

    def compute_aexp(self, node, state):
        if check_aexp(node):
            if checkadd(node):
                first = node.args[0]
                second = node.args[1]
                return self.compute(second, state) + self.compute(first, state)
            elif checksubtract(node):
                first = node.args[0]
                second = node.args[1]
                return self.compute(first, state) - self.compute(second, state)
            elif checkmulti(node):
                first = node.args[0]
                second = node.args[1]
                return self.compute(second, state) * self.compute(first, state)
            first = node.args[0]
            second = node.args[1]
            return self.compute(first, state) / self.compute(second, state)


def _parse_args():
    parser = argparse.ArgumentParser(description='Concolic Execution')
    parser.add_argument('in_file', type=str, help='Input file with program code')
    parser.add_argument('--loop_bound', type=int, default=10, help='Loop bound (default: 10)')
    return parser.parse_args()


def main():
    args = _parse_args()
    ast = wlang.ast.parse_file(args.in_file)
    initial_state = DartState()
    concolic_executor = DartExec()
    concolic_executor.loop_bound = args.loop_bound

    final_state = concolic_executor.run(ast, state=initial_state)

    if not final_state:
        print('failed execution before final state')


if __name__ == '__main__':
    sys.exit(main())
