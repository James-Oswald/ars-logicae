import Mathlib.Tactic.Basic

example (a : α) (Q : α -> Prop)
(H1 : ∀(X : α -> Prop), (X a) -> (∀ (y : α), y ≠ a -> ¬X y))
(H2 : Q a) : ∃ (Z : α -> Prop), ¬ ∃(x y : α), x ≠ y ∧ Z x ∧ Z y := by
have T1 := H1 Q H2
exists Q
intro ⟨w1, w2, T2⟩
by_cases C : (w2 =a)
. case pos =>
  have T3 := T1 w1
  rw [<-C] at T3
  apply Not.elim (T3 T2.left) T2.right.left
. case neg =>
  have T3 := T1 w2
  simp [C] at T3
  apply Not.elim T3 T2.right.right


example [i : Nonempty α] (T D N: α -> α  -> α -> Prop) (f g : α -> α)
(H1 : ∀x y, ∃ z, T (f x) y z)
(H2 : ∀x y z, T x y z -> ¬(D x y z ∨ N z y x)) :
∃x y, ¬(∀z, N z (g y) (f (g x))) := by
  have a : α := Classical.choice i
  have T1 := H1 (g a) (g a)
  have ⟨w, T1⟩ := T1
  have T2 := H2 (f (g a)) (g a) w
  have T3 := T2 T1
  simp [not_or] at T3
  have T4 := T3.right
  exists a, a
  intro C
  have T5 := C w
  contradiction
