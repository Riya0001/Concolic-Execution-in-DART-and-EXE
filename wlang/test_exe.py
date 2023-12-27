import unittest
import wlang.ast
import wlang.exe

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

import unittest

from . import ast, sym , exe
import sys


class TestSym (unittest.TestCase):

    def test_one(self):
        prg1 = "havoc x; assume x > 10; assert x > 15; y:=x+2; if y>0 then x:=0"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    def test_longer_than_30_sec(self):
        prg1 = "a:=999999; while true do{ if a>0 then while true do { x:=3+1 ; havoc z; y:=9; if y>x then z:=x*y else d:=y-z} else while true do {cc:=1}; p:=10/x; q:=10-4; if q<0 then b:=2 else c:=3 }"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),0)

    def test_two(self):
        prg1 = "x:=3+1; y:=9; if y>x then z:=x*y else d:=y-z; p:=10/x; q:=10-4; if q<0 then b:=2 else c:=3"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    def test_while_1(self):
        prg1 = "x:=3+1; while x<0 do {c:=0}"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    def test_while_2(self):
        prg1 = "x:=3+1; while x>3 do {x:=0}"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    def test_while_3(self):
        prg1 = "x:=10+1; while x>0 do {x:=x-1}"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),0)

    def test_incorrect_op3(self):
        try:
            ae1 = ast.AExp(['+'], [ast.IntConst("11"), ast.IntConst("2")])
            ae2 = ast.AExp(['-'], [ast.IntConst("90"), ast.IntConst("30")])
            Ast = ast.RelExp(ae1, ["$"], ae2)
            engine = wlang.exe.ExeExec()
            st = wlang.exe.ExeState()
            engine.run(Ast, state=st)
        except:
            pass
   
    def test_incorrect_op(self):
        try:
            Ast = ast.AExp(['$'], [ast.IntConst("11"), ast.IntConst("90")])
            engine = wlang.exe.ExeExec()
            st = wlang.exe.ExeState()
            engine.run(Ast, state=st)
        except:
            pass


    def test_three(self):
        prg1 = "x:=1; y:=9; if x<5 then y:=0; if y<=0 then assert y=0; if x>=4 then assert x=0"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    # assert does not satisfy
    def test_four(self):
        prg1 = "x:=1; y:=8;assert x<=y"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    # assume does not satisfy
    def test_five(self):
        prg1 = "x:=1; assume x<0"
        ast1 = ast.parse_string(prg1)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),0)

    # test if, skip
    def test_skipStatement(self):
        prg = "x:=1; if x>0 then skip else y:=2"
        ast1 = ast.parse_string(prg)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    def test_incorrect_op2(self):
        try:
            ae1 = ast.AExp(['+'], [ast.IntConst("11"), ast.IntConst("2")])
            ae2 = ast.AExp(['-'], [ast.IntConst("90"), ast.IntConst("30")])
            Ast = ast.BExp(["$"], [ae1,ae2])
            engine = wlang.exe.ExeExec()
            st = wlang.exe.ExeState()
            out = [s for s in engine.run(Ast, st)]
        except:
            pass

    # test print
    def test_print(self):
        prg = "x := 10; print_state"
        ast1 = ast.parse_string(prg)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    # test print
    def test_not(self):
        prg = "x := 7; y := 10; if not (y=15) then z:=10 else w:=0"
        ast1 = ast.parse_string(prg)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    # test print
    def test_and_or(self):
        prg = "q := 1; p := 6; if p*q = 6 and p = 6 then  y := p + 1 else d := 1; if q<0 or p=6 then c:=0"
        ast1 = ast.parse_string(prg)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    # test print
    def test_bool(self):
        prg = "if true then q:=1"
        ast1 = ast.parse_string(prg)
        engine = wlang.exe.ExeExec()
        st = wlang.exe.ExeState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out),1)

    def test_mainExecution(self):
        argument = "wlang/test1.prg"
        sys.argv = [exe, argument]
        exe.main()


    # def test_undeclared_var(self):
    #     try:
    #         prg = "x:=2; assert y=2"
    #         ast1 = ast.parse_string(prg)
    #         engine = wlang.exe.ExeExec()
    #         st = wlang.exe.ExeState()
    #         out = [s for s in engine.run(ast1, st)]
    #         self.assertEquals(len(out), 1)
    #     except:
    #         pass
    #     self.assertTrue(1)

