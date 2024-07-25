
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Aesop

def valid_bf_prog (prog : List Char) (depth : Nat := 0) : Bool :=
match prog, depth with
| [], n => n = 0
| '>'::t, n => valid_bf_prog t n
| '<'::t, n => valid_bf_prog t n
| '+'::t, n => valid_bf_prog t n
| '-'::t, n => valid_bf_prog t n
| '.'::t, n => valid_bf_prog t n
| ','::t, n => valid_bf_prog t n
| '['::t, n => valid_bf_prog t (n+1)
| ']'::t, n => n > 0 ∧ valid_bf_prog t (n-1)
| _::_, _ => False

def valid_bf_prog' (prog : String) : Bool :=
  valid_bf_prog prog.data

example (s : String) : valid_bf_prog' s -> s.data.count '[' = s.data.count ']' := by
  sorry

#eval valid_bf_prog' "++[>++<-]"
#eval valid_bf_prog' "++[>++<]"
#eval valid_bf_prog' "++[>++<]++"
#eval valid_bf_prog' "++[>++<]++[>++<]"

structure Machine where
  tape : List Nat
  tape_pos : Fin tape.length
  --Set of instruction characters
  prog : List Char
  --Program counter, halt is when prog_pos = prog.length
  prog_pos : Fin (prog.length + 1)
  --Stack of loop positions
  stack : List (Fin prog.length)
  output : List Char
  input : List Char


lemma a_lt_b_imp_a_pred_lt_b (a b : Nat) : a < b -> a - 1 < b := by
  intro H
  cases a
  . trivial
  . simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    omega

--Step function, returns the new machine state after executing the current instruction
-- def Machine.step (m : Machine) : Machine :=
--   if H : m.prog_pos.val < m.prog.length then --End of program
--     match m.prog.get ⟨m.prog_pos.val, H⟩ with
--     | '>' => {m with
--       tape := m.tape ++ [0],
--       tape_pos := ⟨m.tape_pos.val + 1, by simp [m.tape_pos.isLt, Nat.add_lt_add_right]⟩,
--       prog_pos := ⟨m.prog_pos.val + 1, by simp [H, Nat.add_lt_add_right]⟩}
--     | '<' => {m with
--       tape_pos := ⟨m.tape_pos.val - 1, by simp [a_lt_b_imp_a_pred_lt_b]⟩,
--       prog_pos := ⟨m.prog_pos.val + 1, by simp [H, Nat.add_lt_add_right]⟩}
--     | '+' => {m with
--       tape := m.tape.set m.tape_pos ((m.tape.get m.tape_pos) + 1),
--       tape_pos := ⟨m.tape_pos, by simp [List.length_set]⟩,
--       prog_pos := ⟨m.prog_pos.val + 1, by simp [H, Nat.add_lt_add_right]⟩}
--     | '-' => {m with
--       tape := m.tape.set m.tape_pos ((m.tape.get m.tape_pos) - 1),
--       tape_pos := ⟨m.tape_pos, by simp [List.length_set]⟩,
--       prog_pos := ⟨m.prog_pos.val + 1, by simp [H, Nat.add_lt_add_right]⟩}
--     | '.' => {m with
--       output := m.output.append [Char.ofNat (m.tape.get m.tape_pos)],
--       prog_pos := ⟨m.prog_pos.val + 1, by simp [H, Nat.add_lt_add_right]⟩}
--     | ',' => {m with
--       tape := m.tape.set m.tape_pos (m.input.headD (Char.ofNat (m.tape.get m.tape_pos))).toNat,
--       tape_pos := ⟨m.tape_pos, by simp [List.length_set]⟩,
--       input := m.input.tailD []
--       prog_pos := ⟨m.prog_pos.val + 1, by simp [H, Nat.add_lt_add_right]⟩}
--     | '[' =>
--     -- if m.tape.get m.tape_pos = 0 then
--     --   let loop_end := m.stack.headD ⟨0, by simp⟩
--     --   {m with
--     --   stack := m.stack.tailD [],
--     --   prog_pos := ⟨loop_end.val + 1, by simp [H, Nat.add_lt_add_right]⟩}
--     -- else
--     --   {m with
--     --   stack := m.stack.append [m.prog_pos],
--     --   prog_pos := ⟨m.prog_pos.val + 1, by simp [H, Nat.add_lt_add_right]⟩}


--     | _ => m
--   else
--     m

--BF hello world program
def HelloWorld : String := "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.+++++++..+++.>++.<<+++++++++++++++.>.+++.------.--------.>+.>."
