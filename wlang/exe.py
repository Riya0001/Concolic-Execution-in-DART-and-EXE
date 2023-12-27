# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conds:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

from functools import reduce
import sys
import wlang.ast
import io 
import z3

from . import ast, int

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


class ExeState(object):
    def __init__(self, solver=None):
        self.env = dict()
        self.path = list()
        self.conc = dict()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()
        self._is_error = False

    def add_pc(self, *exp):
        self.path.extend(exp)
        self._solver.append(exp)

    def mk_error(self):
        self._is_error = True

    def is_sat(self):
        return self._solver.check() == z3.sat

    def pick_concerete(self):
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.env.items():
            self.conc[k] = model.eval(v)
            self.conc[k] = self.conc[k].as_long() if z3.is_int_value(self.conc[k]) else 0

        return st

    def fork(self):
        child = ExeState()
        child.env = dict(self.env)
        child.conc = dict(self.conc)
        child.add_pc(*self.path)

        return (self, child)

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()

    
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

class ExeExec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        return self.visit(ast, state=state)

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if lessthanequal(node.op):
            return lhs <= rhs
        elif lessthan(node.op):
            return lhs < rhs
        elif equal(node.op):
            return lhs == rhs
        elif greaterthanequal(node.op):
            return lhs >= rhs
        return lhs > rhs
    
    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        if checknot(node):
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids[0])
        fn = None
        base = None
        if checkand(node):
            fn = lambda x, y: z3.And(x,y)
            base = z3.BoolVal(True)
        else:
            fn = lambda x, y: z3.Or(x,y)
            base = z3.BoolVal(False)
        assert fn is not None
        return reduce(fn, kids, base)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if checkadd(node):
            fn = lambda x, y: x + y

        elif checksubtract(node):
            fn = lambda x, y: x - y

        elif checkmulti(node):
            fn = lambda x, y: x * y

        else:
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return [kwargs['state']]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        print(kwargs['state'])
        return [kwargs['state']]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        exp = self.visit(node.rhs, *args, **kwargs)
        kwargs['state'].env[node.lhs.name] = exp
        kwargs['state'].conc[node.lhs.name] = self.compute(node.rhs,kwargs['state'])
        return [kwargs['state']]

    def visit_IfStmt(self, node, *args, **kwargs):
        final_states = []
        cond = self.visit(node.cond, *args, **kwargs)
        highlighter = kwargs['state']._solver.check(self.compute(node.cond, kwargs['state'])) == z3.sat
        then_path,else_path = kwargs['state'].fork()
        then_path.add_pc(cond)
        else_path.add_pc(z3.Not(cond))
        if highlighter:
            if then_path.is_sat() :
                final_states.extend(self.visit(node.then_stmt, state=then_path))
            else_path.pick_concerete()    
            if else_path.is_sat():
                final_states.extend(self.visit(node.else_stmt, state=else_path) if node.has_else() else [else_path])
        else :
            if else_path.is_sat():
                final_states.extend(self.visit(node.else_stmt, state=else_path) if node.has_else() else [else_path])   
            then_path.pick_concerete()
            if then_path.is_sat() :
                final_states.extend(self.visit(node.then_stmt, state=then_path))
        return final_states

    def visit_WhileStmt(self, node, *args, **kwargs):
       iteration_number = 0
       output_final = []
       all_states = [kwargs['state']]
       while(iteration_number < 10):
            iteration_number += 1
            updated_all_states = []
            for state in all_states:
                cond = self.visit(node.cond, state=state) 
                highlighter = kwargs['state']._solver.check(cond) == z3.sat
                loop_state,end_state = state.fork()
                loop_state.add_pc(cond)
                end_state.add_pc(z3.Not(cond))
                if highlighter:
                    if loop_state.is_sat():
                        updated_all_states.extend(self.visit(node.body, state=loop_state))
                    end_state.pick_concerete()
                    if end_state.is_sat():
                        output_final.append(end_state)
                else :
                    if end_state.is_sat():
                        output_final.append(end_state)
                    loop_state.pick_concerete()
                    if loop_state.is_sat():
                        updated_all_states.extend(self.visit(node.body, state=loop_state))
            all_states = updated_all_states
       return output_final

    def visit_AssertStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        true_state,false_state = kwargs['state'].fork()
        updated_state = []

        true_state.add_pc(cond)
        if  true_state.is_sat():
            true_state.pick_concerete()
            updated_state.append(true_state)

        false_state.add_pc(z3.Not(cond))
        if false_state.is_sat():
            print("Assertion Failed")
            false_state.mk_error()

        return updated_state

    def visit_AssumeStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        state.add_pc(self.visit(node.cond, *args, **kwargs))
        if state.is_sat():
            state.pick_concerete()
            return [state]
        return []    

    def visit_HavocStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        for var in node.vars:
            state.env[var.name] = z3.FreshInt(var.name)
            state.conc[var.name] = z3.IntVal("0")
        return [state]

    def visit_StmtList(self, node, *args, **kwargs):
        currStates = [kwargs['state']]
        for stmt in node.stmts:
            updated_states = []
            for state in currStates:
                updated_states.extend(self.visit(stmt, state=state))
            currStates = updated_states
        return currStates
    
    def compute(self, node, state):
        if check_int_const(node):
            return node.val
        elif check_bool_const(node):
            return node.val
        elif check_int_var(node):
            if isinstance(state.conc[node.name], z3.IntNumRef):
                return state.conc[node.name].as_long()
            else:
                return state.conc[node.name]
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
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = ExeState()
    sym = ExeExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic found')
            print(out)
        print('[symexec]: number of states is', count)
    return 0


if __name__ == '__main__':
    sys.exit(main())