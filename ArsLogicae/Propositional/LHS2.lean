

import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases

import ArsLogicae.Propositional.Language
import ArsLogicae.Propositional.Semantics
import ArsLogicae.ProofSystem

/--
Prototypically in hilbert systems, proofs have NO context
A proof of a statement φ is inducitvely defined to either
require that the φ is an axiom or can be derived from the
axioms via a chain of MP applicaions.
-/
inductive LHSProof : PL -> Type
/-- If φ takes the form of any axiom, then this is a proof of φ --/
| ax1 {φ ψ : PL} : LHSProof (φ →ₒ (ψ →ₒ φ))
| ax2 {φ ψ χ : PL} : LHSProof ((φ →ₒ (ψ →ₒ χ)) →ₒ ((φ →ₒ ψ) →ₒ (φ →ₒ χ)))
| ax3 {φ ψ : PL} : LHSProof ((¬ₒφ →ₒ ¬ₒψ) →ₒ (ψ →ₒ φ))
/--
If we have a proof of φ and a proof of φ →ₒ ψ, this is a proof of ψ
-/
| mp {φ ψ : PL} : LHSProof φ -> LHSProof (φ →ₒ ψ) -> LHSProof ψ


instance : ProofSystem PL LHSProof := by constructor; rfl





def LHSProv (φ : PL) : Prop := Nonempty (LHSProof φ)

notation:43 "T⊢ʰₚₗ" φ => LHSProof φ
notation:43 "⊬ʰₚₗ" φ => ¬LHSProof φ

/--
The concequence relation is defined in terms of provability
-/
inductive LHSConsequence (Γ : Multiset PL) : PL -> Prop
/-- If φ is in Γ, then φ is provable from Γ. --/
| assumption {φ : PL} : φ ∈ Γ -> LHSConsequence Γ φ
/--
If we have a proof of a state
--/
| tautology {φ : PL} : LHSProof φ -> LHSConsequence Γ φ


notation:43 Γ "⊢ʰₚₗ" φ => LHSConsequence Γ φ
notation:43 Γ "⊬ʰₚₗ" φ => ¬LHSConsequence Γ φ

lemma ex: T⊢ʰₚₗ φ


theorem h_prov_implies_self (φ : PL) : Γ ⊢ʰₚₗ φ →ₒ φ := by
  have ψ : PL := Inhabited.default
  have H1 : T⊢ʰₚₗ (φ →ₒ ((ψ →ₒ φ) →ₒ φ)) := LHSProof.ax1
  have H2 : T⊢ʰₚₗ (φ →ₒ ((ψ →ₒ φ) →ₒ φ)) →ₒ ((φ →ₒ (ψ →ₒ φ)) →ₒ (φ →ₒ φ)) :=
    LHSProof.ax2
  have H3 : T⊢ʰₚₗ ((φ →ₒ (ψ →ₒ φ)) →ₒ (φ →ₒ φ)) :=
    LHSProof.mp H1 H2
  have H4 : T⊢ʰₚₗ (φ →ₒ (ψ →ₒ φ)) := LHSProof.ax1
  have H5 : T⊢ʰₚₗ (φ →ₒ φ) := LHSProof.mp H4 H3
  exact ↑H5


lemma PL.h_if_intro: (Γ ⊢ʰₚₗ φ) -> (Γ ⊢ʰₚₗ ψ →ₒ φ) := by
  intro H
  have H1 : Γ T⊢ʰₚₗ φ := proof_of_prov H
  have H2 : Γ T⊢ʰₚₗ (φ →ₒ (ψ →ₒ φ)) := LHSProof.ax1
  have H3 : Γ T⊢ʰₚₗ (ψ →ₒ φ) := LHSProof.mp H1 H2
  exact ↑H3

/--
Version of `PL.h_if_intro` that takes a proof instead of provability.
-/
def PL.hp_if_intro: (Γ T⊢ʰₚₗ φ) -> (Γ ⊢ʰₚₗ ψ →ₒ φ) :=
  PL.h_if_intro ∘ prov_of_proof

/--
The Deduction Theorem for Hilbert style proof systems.
-/
theorem PL.deduction_theorem : ((φ ::ₘ Γ) ⊢ʰₚₗ ψ) → (Γ ⊢ʰₚₗ φ →ₒ ψ) := by
  intro H
  have H : (φ ::ₘ Γ) T⊢ʰₚₗ ψ := proof_of_prov H
  induction H
  . case assumption A H2 =>
    simp only [Multiset.mem_cons] at H2
    cases H2
    . case inl H3 =>
      rw [<-H3]
      exact h_prov_implies_self A
    . case inr H3 := PL.hp_if_intro (LHSProof.assumption H3)
  . case ax1 A B := PL.hp_if_intro LHSProof.ax1
  . case ax2 A B C := PL.hp_if_intro LHSProof.ax2
  . case ax3 A B := PL.hp_if_intro LHSProof.ax3
  . case mp A B C D IH1 IH2 =>
    have IH3 := ↑(IH1 (prov_of_proof C))
    have IH4 := ↑(IH2 (prov_of_proof D))
    apply prov_of_proof
    exact LHSProof.mp IH3 (LHSProof.mp IH4 (@LHSProof.ax2 Γ φ A B))

theorem PL.sound (φ : PL) : (⊢ʰₚₗ φ) → (⊨ₚₗ φ) := by
  intros H v
  have p := proof_of_prov H
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
