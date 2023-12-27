import unittest
import wlang.ast
import wlang.dart
import sys


class TestDartExec(unittest.TestCase):
    def test_assert(self):
        prg1 = "z := 1; assert z < 0"
        ast1 = wlang.ast.parse_string(prg1)
        exe = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_state = exe.run(ast1, state=start_state)
        self.assertTrue(end_state)

    def test_havoc(self):
        prg2 = "havoc x, y; if x > y then x := x * 2 else y := x /2; assert x > y"
        ast2 = wlang.ast.parse_string(prg2)
        exe = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_state = exe.run(ast2, state=start_state)
        self.assertTrue(end_state)

    def test_while(self):
        prg3 = "x:=5; y:=x==5 and true; while x > 0 do x := x - 1; assert x = 0"
        ast3 = wlang.ast.parse_string(prg3)
        exe = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_state = exe.run(ast3, state=start_state)
        self.assertTrue(end_state)

    def test_and(self):
        prg1 = "x := 1; y:=0 assert x > y and y==0"
        ast1 = wlang.ast.parse_string(prg1)
        exe = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe.run(ast1, state=start_state)
        self.assertTrue(end_states)
        for end_state in end_states:
            x_value = end_state.concrete_state.get("x")
            self.assertEqual(x_value, 1)

    def test_branching(self):
        try:
            prg1 = "havoc p; x:=5; y:=2; z:=10; if x > 0 or y=2 then y := x + 1 else y := x - 1; assert y > z"
            ast1 = wlang.ast.parse_string(prg1)
            exe = wlang.dart.DartExec()
            start_state = wlang.dart.DartState()
            end_states = exe.run(ast1, state=start_state)

            for end_state in end_states:
                if end_state is not None:
                    x_value = end_state.concrete_state.get("x")
                    y_value = end_state.concrete_state.get("y")
                    z_value = end_state.concrete_state.get("z")
                    self.assertIsNotNone(x_value)
                    self.assertIsNotNone(y_value)
                    self.assertIsNotNone(z_value)
        except:
            pass

    def test_fail_assumption(self):
        prg1 = "havoc p; x:=5; assert x<0"
        ast1 = wlang.ast.parse_string(prg1)
        exe = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe.run(ast1, state=start_state)

    def test_incorrect_op3(self):
        try:
            ae1 = wlang.ast.AExp(['+'], [wlang.ast.IntConst("11"), wlang.ast.IntConst("2")])
            ae2 = wlang.ast.AExp(['-'], [wlang.ast.IntConst("90"), wlang.ast.IntConst("30")])
            Ast = wlang.ast.RelExp(ae1, ["$"], ae2)
            engine = wlang.dart.DartExec()
            st = wlang.dart.DartState()
            engine.run(Ast, state=st)
        except:
            pass
   
    def test_incorrect_op(self):
        try:
            Ast = wlang.ast.AExp(['$'], [wlang.ast.IntConst("11"), wlang.ast.IntConst("90")])
            engine = wlang.dart.DartExec()
            st = wlang.dart.DartState()
            engine.run(Ast, state=st)
        except:
            pass

    def test_loop_assert(self):
        prg1 = "x := 0; y:=x-1; z:=x*y; while x < 5  do x := x + 1; if true then assert x >= 5"
        ast1 = wlang.ast.parse_string(prg1)
        exe = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe.run(ast1, state=start_state)
        for end_state in end_states:
            x_value = end_state.concrete_state.get("x")
            self.assertIsNotNone(x_value)
            self.assertEqual(x_value, 5)

    def test_then_stmt(self):
        prg = "x:=5; if x <= 10 and x=5 then x := x + 2"
        ast = wlang.ast.parse_string(prg)
        exe_executor = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe_executor.run(ast, state=start_state)
        for end_state in end_states:
            if end_state is not None:
                self.assertIsNotNone(end_state.concrete_state.get("x"))
                self.assertGreater(end_state.concrete_state.get("x"), -2)

    def test_bool(self):
        prg = "x:=0; if not (x < 0) then assert x >= 0"
        ast = wlang.ast.parse_string(prg)
        exe_executor = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe_executor.run(ast, state=start_state)

        for end_state in end_states:
            if end_state is not None:
                self.assertIsNotNone(end_state.concrete_state.get("x"))
                self.assertGreaterEqual(end_state.concrete_state.get("x"), 0)

    def test_rel(self):
        prg = "x:=0; if x < 12 and x < 9 then assert x < 11"
        ast = wlang.ast.parse_string(prg)
        exe_executor = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe_executor.run(ast, state=start_state)
        for end_state in end_states:
            if end_state is not None:
                self.assertIsNotNone(end_state.concrete_state.get("x"))

    def test_int(self):
        prg = "havoc x; assert x = x; x:=2; if x<0 then y:=2 else y:=3"
        ast = wlang.ast.parse_string(prg)
        exe_executor = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe_executor.run(ast, state=start_state)

    def test_bool_const(self):
        prg = "assert true;x:=4; assert 4=x"
        ast = wlang.ast.parse_string(prg)
        exe_executor = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe_executor.run(ast, state=start_state)

    def test_int_const(self):
        prg = "assert 5 = 5"
        ast = wlang.ast.parse_string(prg)
        exe_executor = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe_executor.run(ast, state=start_state)

    def test_assume_stmt(self):
        prg = "x:=5; assume x >= 0; assert x >= 0"
        ast = wlang.ast.parse_string(prg)
        exe = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe.run(ast, state=start_state)
        for end_state in end_states:
            if end_state is not None:
             self.assertIsNotNone(end_state.concrete_state.get("x"))

    def test_assume_stmt1(self):
        prg = "x:=5; assume x <= 0"
        ast = wlang.ast.parse_string(prg)
        exe = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()
        end_states = exe.run(ast, state=start_state)

    def test_divide(self):
        prg = "x := 10; y := x / 2"
        ast = wlang.ast.parse_string(prg)
        int_var_node = wlang.ast.IntVar(name="x")
        exe_executor = wlang.dart.DartExec()
        start_state = wlang.dart.DartState()

        end_states = exe_executor.run(ast, state=start_state)
        for end_state in end_states:
            if end_state is not None:
                self.assertIsNotNone(end_state.concrete_state.get("y"))
                self.assertEqual(end_state.concrete_state.get("y"), 5)

    def test_mainExecution(self):
        argument = "wlang/test1.prg"
        sys.argv = [wlang.dart.__file__, argument]
        wlang.dart.main()

if __name__ == '__main__':
    unittest.main()
