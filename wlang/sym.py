# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import sys

import io 

from . import ast, int
from functools import reduce
import z3

class SymState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concerete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState()
        child.env = dict(self.env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

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

class SymExec(ast.AstVisitor):
    def _init_(self):
        pass

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
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
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs
        # raise error if operator is invalid
        assert False


    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids[0])

        elif node.op == "and":
            return z3.And(*kids)
        elif node.op == "or":
            return z3.Or(*kids)

        assert False

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if node.op == "+":
            fn = lambda x, y: x + y

        elif node.op == "-":
            fn = lambda x, y: x - y

        elif node.op == "*":
            fn = lambda x, y: x * y

        elif node.op == "/":
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return [kwargs['state']]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        return [kwargs['state']]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        exp = self.visit(node.rhs, *args, **kwargs)
        var = node.lhs.name
        st = kwargs['state']
        if var not in st.env:
            st.env[var] = z3.FreshInt(var)
        st.env[var] = exp
        return [st]

    def visit_IfStmt(self, node, *args, **kwargs):
        res = []
        cond = self.visit(node.cond, *args, **kwargs)
        st = kwargs['state']

        st1, st2 = st.fork()
        st1.add_pc(cond)
        st2.add_pc(z3.Not(cond))
        if not st1.is_empty():
            res.extend(self.visit(node.then_stmt, state = st1))

        if not st2.is_empty():
            if node.has_else():
                res.extend(self.visit(node.else_stmt, state=st2))
            else:
                res.extend([st2])
        return res

    def visit_WhileStmt(self, node, *args, **kwargs):
                st = kwargs['state']
                temp = []
   
                cond = self.visit (node.cond, * args, ** kwargs)
                st0, st1 = st.fork()
   
                #when loop is never executed
                st0.add_pc(z3.Not(cond))
   
                #when loop is executed atleast once
                st1.add_pc(cond)
   
                #when loop is never executed, simply return
                if not st0.is_empty():
                    temp.extend([st0])
                    return temp
   
                #loop is executed atleast once
                before_loop = [st1]  
                additional_states=[]
                #loop first iteration on all the previous states
                for item in before_loop:
                    st = self.visit(node.body, state = item)
                    additional_states.extend(st)
                before_loop = additional_states
           
                #loop iterations from 1 to 10, total 11 iterations to handle case
                #  if loop never breaks and store the states after 10 executions
                for index in range(1,11):  
                    after_loop = []
                    additional_states = after_loop         
                    for item in before_loop:    
                        cond = self.visit(node.cond, state = item)

                        st0_cond, st1_cond = item.fork()

                        #loop breaks in this iteration
                        st0_cond.add_pc(z3.Not(cond))
                        if not st0_cond.is_empty():
                            temp.extend([st0_cond])
                            return temp
               
                        st1_cond.add_pc(cond)
                        #loop executes in this iteration as well
                        st = self.visit(node.body, state = st1_cond)
                        additional_states.extend(st)

                        after_loop = additional_states
                    before_loop = after_loop
                #if loop never breaks extend all the states
                temp.extend(before_loop)
                return temp

    def visit_AssertStmt(self, node, *args, **kwargs):
         # Don't forget to print an error message if an assertion might be violated
     
        cond = self.visit (node.cond, * args, ** kwargs)
        st0, st1 = kwargs['state'].fork()
        st1.add_pc(cond)
        st0.add_pc(z3.Not(cond))

        if not st0.is_empty():
            print("if ", st0.pick_concerete())
            st0.mk_error()
            print("Assertion will fail for\n", st1)
        st0.pick_concerete()

        if st1.is_empty():
            return []
        return [st1]

    def visit_AssumeStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        st = kwargs['state']
        st.add_pc(cond)
        if st.is_empty():
            return []
        return [st]

    def visit_HavocStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        for var in node.vars:
            st.env [var.name] = z3.FreshInt (var.name)
        return [st]

    def visit_StmtList(self, node, *args, **kwargs):
        st1 = [kwargs['state']]
        for stmt in node.stmts:
            st2 = []
            for state in st1:
                st = self.visit(stmt, state = state)
                st2.extend(st)
            st1 = st2
        return st1

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
    st = SymState()
    sym = SymExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0

if __name__ == '__main__':
    sys.exit(main())
