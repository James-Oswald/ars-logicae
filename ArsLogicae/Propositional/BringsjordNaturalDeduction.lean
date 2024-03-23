
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases

import ArsLogicae.Propositional.Language
import ArsLogicae.Propositional.Semantics

/-!
This file contains a natural deduction proof system for propositional logic.
The ND proof system is defined with Bringsjord's inference rules.
-/

/--
The type of natural deduction proofs for propositional logic.
-/
inductive NDProof : Multiset PL -> PL -> Type
| assumption {φ : PL} : NDProof {φ} φ
| intro_and {φ ψ : PL} : NDProof Γ φ -> NDProof Γ ψ -> NDProof Γ (φ ∧ₒ ψ)
| elim_and_left {φ ψ : PL} : NDProof Γ (φ ∧ₒ ψ) -> NDProof Γ φ
| elim_and_right {φ ψ : PL} : NDProof Γ (φ ∧ₒ ψ) -> NDProof Γ ψ
| intro_or_left {φ ψ : PL} : NDProof Γ φ -> NDProof Γ (φ ∨ₒ ψ)
| intro_or_right {φ ψ : PL} : NDProof Γ ψ -> NDProof Γ (φ ∨ₒ ψ)
| elim_or {φ ψ χ : PL} : NDProof Γ (φ ∨ₒ ψ) -> NDProof (φ ::ₘ Γ) χ -> NDProof (ψ ::ₘ Γ) χ -> NDProof Γ χ
| implies_intro {φ ψ : PL} : (NDProof (φ ::ₘ Γ) ψ) -> (NDProof Γ (φ →ₒ ψ))
| implies_elim {φ ψ : PL} : NDProof Γ φ -> NDProof Γ (φ →ₒ ψ) -> NDProof Γ ψ
| not_intro {φ ψ : PL} : NDProof (φ ::ₘ Γ) ψ -> (NDProof (φ ::ₘ Γ) (¬ₒψ)) -> NDProof Γ (¬ₒφ)
| not_elim {φ : PL} : NDProof (¬ₒφ ::ₘ Γ) ψ -> (NDProof (¬ₒφ ::ₘ Γ) (¬ₒψ)) -> NDProof Γ φ
| iff_intro {φ ψ : PL} : NDProof (φ ::ₘ Γ) ψ -> NDProof (ψ ::ₘ Γ) φ -> NDProof Γ (φ ↔ₒ ψ)
| iff_elim_left {φ ψ : PL} : NDProof Γ (φ ↔ₒ ψ) -> NDProof Γ φ -> NDProof Γ ψ
| iff_elim_right {φ ψ : PL} : NDProof Γ (φ ↔ₒ ψ) -> NDProof Γ ψ -> NDProof Γ φ

notation:43 Γ "T⊢ⁿₚₗ" φ => NDProof Γ φ
notation:43 "T⊢ⁿₚₗ" φ => NDProof ∅ φ

inductive PL.ndprov (Γ : Multiset PL) : PL -> Prop :=
| intro {φ : PL} : Nonempty (Γ T⊢ⁿₚₗ φ) -> PL.ndprov Γ φ
