
import Mathlib.Tactic.Contrapose
import Mathlib.Data.Multiset.Basic

def Atom := String
deriving Repr, BEq, DecidableEq, Inhabited

inductive PL where
| atom (a : Atom): PL
| not (φ : PL) : PL
| and (φ ψ : PL): PL
deriving Repr, BEq, DecidableEq, Inhabited

prefix:70 "¬ₒ" => PL.not
infixr:65 "∧ₒ"  => PL.and

def PL.or (φ ψ : PL) : PL := ¬ₒ(¬ₒφ ∧ₒ ¬ₒψ)
infixr:60 "∨ₒ" => PL.or

def PL.implies (φ ψ : PL) : PL := ¬ₒφ ∨ₒ ψ
infixl:55 "⊃₀" => PL.implies
infixl:55 "→ₒ" => PL.implies

def PL.iff (φ ψ : PL) : PL := (φ →ₒ ψ) ∧ₒ (ψ →ₒ φ)
infix:50 "≡ₒ" => PL.iff
infix:50 "↔ₒ" => PL.iff

def PL.true : PL := PL.atom "A" →ₒ PL.atom "A"
notation "⊤ₒ" => PL.true

def PL.false : PL := ¬ₒ⊤ₒ
notation "⊥ₒ" => PL.false

def PL.sat (v : Atom -> Prop) : PL-> Prop
| PL.atom a => v a
| PL.not φ => ¬PL.sat v φ
| PL.and φ ψ => PL.sat v φ ∧ PL.sat v ψ

notation:43 assignment "⊨ₚₗ" p => PL.sat assignment p
notation:43 assignment "⊭ₚₗ" p => ¬PL.sat assignment p

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

def PL.valid (φ : PL) : Prop := ∀v, v ⊨ₚₗ φ
notation:40 "⊨ₚₗ" φ => PL.valid φ

/-
`PL.HLProof Γ φ` or `Γ T⊢ʰₚₗ φ` is the `Type` of proofs of φ from Γ in
a Łukasiewicz style Hilbert system.
-/
inductive PL.HProof (Γ : Multiset PL) : PL -> Type
| assumption {φ : PL} : φ ∈ Γ -> PL.HProof Γ φ
| ax1 {φ ψ : PL} : PL.HProof Γ (φ →ₒ (ψ →ₒ φ))
| ax2 {φ ψ χ : PL} : PL.HProof Γ ((φ →ₒ (ψ →ₒ χ)) →ₒ ((φ →ₒ ψ) →ₒ (φ →ₒ χ)))
| ax3 {φ ψ : PL} : PL.HProof Γ ((¬ₒφ →ₒ ¬ₒψ) →ₒ (ψ →ₒ φ))
| mp {φ ψ : PL} : PL.HProof Γ φ -> PL.HProof Γ (φ →ₒ ψ) -> PL.HProof Γ ψ

notation:43 Γ "T⊢ʰₚₗ" φ => PL.HProof Γ φ
notation:43 "T⊢ʰₚₗ" φ => PL.HProof ∅ φ

/-
The size of a proof is the number of leafs in the proof tree +
applications of the modus ponens rule.
-/
def PL.HLProof.size : (Γ T⊢ʰₚₗ φ) → ℕ
| PL.HProof.mp p1 p2 => 1 + PL.HLProof.size p1 + PL.HLProof.size p2
| _ => 1

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
| proof {φ : PL} : Nonempty (Γ T⊢ʰₚₗ φ) -> PL.hprov Γ φ

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
  apply PL.hprov.proof
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


theorem PL.neg_hprov (φ : PL) : (Γ ⊬ʰₚₗ φ) -> (Γ ⊢ʰₚₗ ¬ₒφ) := by
  intro H
  apply @PL.hprov.mp Γ φ
  sorry



/-
The Deduction Theorem for Hilbert style proof systems.
-/
theorem PL.deduction : ((φ ::ₘ Γ) ⊢ʰₚₗ ψ) ↔ (Γ ⊢ʰₚₗ φ →ₒ ψ) := by
  apply Iff.intro
  . case mp =>
    intro H
    apply PL.hprov.mp (Γ ⊢ʰₚₗ ψ)
    induction H
    . case assumption A H1 =>
      sorry
    . case ax1 =>
      sorry
    . case ax2 =>
      sorry
    . case ax3 =>
      sorry
    . case mp A B H1 H2 =>
      sorry
    --
    -- have H2 := PL.h_prov.assumption H1
  . case mpr =>
    intro H
    intro H
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
  contrapose
