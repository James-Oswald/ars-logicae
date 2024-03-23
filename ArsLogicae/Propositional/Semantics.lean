
import Mathlib.Tactic.Tauto

import ArsLogicae.Propositional.Language

/-!
The file contains definitions for the standard truth-functional
semantics for propositional logic.
-/

/--
A valuation is a function that maps each atom to a truth value.
-/
def Valuation : Type := Atom -> Prop

/--
A PL formula φ is satisfied by a valuation v, written `PL.sat v φ`
or `v ⊨ₚₗ φ` if the formula evaluates to true under the valuation.
-/
def PL.sat (v : Valuation) : PL-> Prop
| PL.atom a => v a
| PL.not φ => ¬PL.sat v φ
| PL.and φ ψ => PL.sat v φ ∧ PL.sat v ψ

notation:43 assignment "⊨ₚₗ" p => PL.sat assignment p
notation:43 assignment "⊭ₚₗ" p => ¬PL.sat assignment p

/-!
# Sat Constructed Connectives
The following theorems are how sat is defined for the other
connectives.
-/

theorem PL.sat_or : (v ⊨ₚₗ φ ∨ₒ ψ) ↔ (v ⊨ₚₗ φ) ∨ (v ⊨ₚₗ ψ) := by
  simp [PL.sat]
  tauto

theorem PL.sat_implies : (v ⊨ₚₗ φ →ₒ ψ) ↔ ((v ⊨ₚₗ φ) → (v ⊨ₚₗ ψ)) := by
  simp [PL.sat]

theorem PL.sat_iff : (v ⊨ₚₗ φ ↔ₒ ψ) ↔ ((v ⊨ₚₗ φ) ↔ (v ⊨ₚₗ ψ)) := by
  simp [PL.sat]
  tauto

theorem PL.sat_true : v ⊨ₚₗ ⊤ₒ := by
  simp [PL.true, PL.sat];

theorem PL.not_sat_false : v ⊭ₚₗ ⊥ₒ := by
  simp [PL.false, PL.sat];

/-! # Validity -/

/--
A PL formula is valid if it is satisfied by every assignment.
-/
def PL.valid (φ : PL) : Prop := ∀v, v ⊨ₚₗ φ
notation:40 "⊨ₚₗ" φ => PL.valid φ
