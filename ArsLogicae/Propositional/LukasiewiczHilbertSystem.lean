
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases

import ArsLogicae.Propositional.Language
import ArsLogicae.Propositional.Semantics

/-!
This file contains the most basic propositional proof system,
Lukasiewicz's style of Hilbert Calcus with 3 axioms and modus ponens.
-/

/--
`PL.HLProof Γ φ` or `Γ T⊢ʰₚₗ φ` is the `Type` of proofs of φ from Γ in
a Łukasiewicz style Hilbert system. Proofs are defined inducively with the
following 5 constructors.
-/
inductive PL.HProof (Γ : Multiset PL) : PL -> Type
/-- If φ is in Γ, then φ is provable from Γ. --/
| assumption {φ : PL} : φ ∈ Γ -> PL.HProof Γ φ
/-- If φ takes the form of any axiom 1, it is provable from Γ --/
| ax1 {φ ψ : PL} : PL.HProof Γ (φ →ₒ (ψ →ₒ φ))
| ax2 {φ ψ χ : PL} : PL.HProof Γ ((φ →ₒ (ψ →ₒ χ)) →ₒ ((φ →ₒ ψ) →ₒ (φ →ₒ χ)))
| ax3 {φ ψ : PL} : PL.HProof Γ ((¬ₒφ →ₒ ¬ₒψ) →ₒ (ψ →ₒ φ))
/--
If φ is provable from Γ and φ →ₒ ψ is provable from Γ,
then ψ is provable from Γ
-/
| mp {φ ψ : PL} : PL.HProof Γ φ -> PL.HProof Γ (φ →ₒ ψ) -> PL.HProof Γ ψ

notation:43 Γ "T⊢ʰₚₗ" φ => PL.HProof Γ φ
notation:43 "T⊢ʰₚₗ" φ => PL.HProof ∅ φ


/-
If we can construct a proof than a proof exists.
-/
theorem PL.HLProof.exists : (Γ T⊢ʰₚₗ φ) → ∃(_ : Γ T⊢ʰₚₗ φ), True := by
  intro H
  exact ⟨H, trivial⟩

/-
inducively define the provability predicate to
depend on the existance of a proof of φ from Γ.
-/
inductive PL.hprov (Γ : Multiset PL) : PL -> Prop :=
| intro {φ : PL} : Nonempty (Γ T⊢ʰₚₗ φ) -> PL.hprov Γ φ

notation:43 Γ "⊢ʰₚₗ" φ => PL.hprov Γ φ
notation:43 Γ "⊬ʰₚₗ" φ => ¬PL.hprov Γ φ
notation:43 "⊢ʰₚₗ" φ => PL.hprov ∅ φ
notation:43 "⊬ʰₚₗ" φ => ¬PL.hprov ∅ φ

/-
Given a proof of φ from Γ, we derive that φ is provable from Γ.
-/
@[simp]
theorem PL.hprov_of_hproof: (Γ T⊢ʰₚₗ φ) -> (Γ ⊢ʰₚₗ φ) := by
  intro H
  apply PL.hprov.intro
  rw [<-exists_true_iff_nonempty]
  exact PL.HLProof.exists H

/-
If we have that φ is provable from Γ, then the type of
proofs of φ from Γ is `Nonempty`. This allows us to
use the axiom of choice to extract an arbitrary proof of a
fact merely from us knowing that it is provable.
-/
theorem PL.HProof.nonempty: (Γ ⊢ʰₚₗ φ) -> Nonempty (Γ T⊢ʰₚₗ φ) := by
  intro H1
  cases H1
  assumption

instance {H : (Γ ⊢ʰₚₗ φ)} : Nonempty (Γ T⊢ʰₚₗ φ) := PL.HProof.nonempty H

/-
Use classical.choice to create a proof from a proof of provability.
-/
noncomputable def PL.hproof_of_hprov: (Γ ⊢ʰₚₗ φ) -> (Γ T⊢ʰₚₗ φ) := by
  intro H
  exact Classical.choice (PL.HProof.nonempty H)

/-
Using classical.choice, anything provable from a proof is provable
from provability.
-/
theorem PL.hproof_imp_p_imp_hprov_imp_p {p : Prop} :
((Γ T⊢ʰₚₗ φ) → p) → ((Γ ⊢ʰₚₗ φ) → p) := by
  intro H1
  intro H2
  exact H1 (PL.hproof_of_hprov H2)


-- # Derived axioms for Hilbert style proof system

theorem PL.h_prov_implies_self (φ : PL) : Γ ⊢ʰₚₗ φ →ₒ φ := by
  apply PL.hprov_of_hproof
  have ψ : PL := Inhabited.default
  have H1 : Γ T⊢ʰₚₗ (φ →ₒ ((ψ →ₒ φ) →ₒ φ)) := PL.HProof.ax1
  have H2 : Γ T⊢ʰₚₗ (φ →ₒ ((ψ →ₒ φ) →ₒ φ)) →ₒ ((φ →ₒ (ψ →ₒ φ)) →ₒ (φ →ₒ φ)) :=
    PL.HProof.ax2
  have H3 : Γ T⊢ʰₚₗ ((φ →ₒ (ψ →ₒ φ)) →ₒ (φ →ₒ φ)) :=
    PL.HProof.mp H1 H2
  have H4 : Γ T⊢ʰₚₗ (φ →ₒ (ψ →ₒ φ)) := PL.HProof.ax1
  have H5 : Γ T⊢ʰₚₗ (φ →ₒ φ) := PL.HProof.mp H4 H3
  exact H5

/-! # Proof Sizes -/

/--
The size of a proof is the number of leafs in the proof tree +
applications of the modus ponens rule.
-/
def PL.HProof.size : (Γ T⊢ʰₚₗ φ) → ℕ
| PL.HProof.mp p1 p2 => 1 + PL.HProof.size p1 + PL.HProof.size p2
| _ => 1

/--
A proof never has a size of 0
-/
theorem PL.HProof.size_nonzero : PL.HProof.size P ≠ 0 := by
  cases P
  repeat {simp [PL.HProof.size]}

/-! # Deduction theorem -/

/--
In the proof system, if φ holds under Γ, then φ →ₒ ψ holds under Γ.
-/
lemma PL.h_if_intro: (Γ ⊢ʰₚₗ φ) -> (Γ ⊢ʰₚₗ ψ →ₒ φ) := by
  intro H
  have H1 : Γ T⊢ʰₚₗ φ := PL.hproof_of_hprov H
  have H2 : Γ T⊢ʰₚₗ (φ →ₒ (ψ →ₒ φ)) := PL.HProof.ax1
  have H3 : Γ T⊢ʰₚₗ (ψ →ₒ φ) := PL.HProof.mp H1 H2
  exact PL.hprov_of_hproof H3

/--
Version of `PL.h_if_intro` that takes a proof instead of provability.
-/
def PL.hp_if_intro: (Γ T⊢ʰₚₗ φ) -> (Γ ⊢ʰₚₗ ψ →ₒ φ) :=
  PL.h_if_intro ∘ PL.hprov_of_hproof

/--
The Deduction Theorem for Hilbert style proof systems.
-/
theorem PL.deduction_theorem : ((φ ::ₘ Γ) ⊢ʰₚₗ ψ) → (Γ ⊢ʰₚₗ φ →ₒ ψ) := by
  intro H
  have H : (φ ::ₘ Γ) T⊢ʰₚₗ ψ := PL.hproof_of_hprov H
  induction H
  . case assumption A H2 =>
    simp only [Multiset.mem_cons] at H2
    cases H2
    . case inl H3 =>
      rw [<-H3]
      exact h_prov_implies_self A
    . case inr H3 := PL.hp_if_intro (PL.HProof.assumption H3)
  . case ax1 A B := PL.hp_if_intro PL.HProof.ax1
  . case ax2 A B C := PL.hp_if_intro PL.HProof.ax2
  . case ax3 A B := PL.hp_if_intro PL.HProof.ax3
  . case mp A B C D IH1 IH2 =>
    have IH3 := hproof_of_hprov (IH1 (hprov_of_hproof C))
    have IH4 := hproof_of_hprov (IH2 (hprov_of_hproof D))
    apply hprov_of_hproof
    exact PL.HProof.mp IH3 (PL.HProof.mp IH4 (@PL.HProof.ax2 Γ φ A B))


theorem PL.hprov_lem : (Γ ⊢ʰₚₗ φ ∨ₒ ¬ₒφ) := by
  sorry

theorem PL.not_hprov : (Γ ⊬ʰₚₗφ) -> (Γ ⊢ʰₚₗ ¬ₒφ) := by
  sorry

/-
Hilbert style proof system is sound with respect to the truth functional semantics
of propositional logic.
-/
theorem PL.sound (φ : PL) : (⊢ʰₚₗ φ) → (⊨ₚₗ φ) := by
  intros H v
  have p := PL.hproof_of_hprov H
  induction p
  . case assumption A =>
    aesop --Trivial contradiction
  . case ax1 A B =>
    simp [PL.sat_implies]
    tauto
  . case ax2 A B C =>
    simp [PL.sat_implies]
    tauto
  . case ax3 A B =>
    simp [PL.sat_implies]
    by_contra
    tauto
  . case mp _ IH =>
    simp [PL.sat_implies] at IH;
    tauto



theorem PL.complete (φ : PL) : (⊨ₚₗ φ) → (⊢ʰₚₗ φ) := by
  sorry
