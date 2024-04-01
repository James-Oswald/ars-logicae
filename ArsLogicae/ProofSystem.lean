
import Mathlib.Data.Multiset.Basic


inductive ProofSystem {L : Type} where
| HilbertStyle : (L -> Type) -> ProofSystem
| NaturalDeductionStyle : (Multiset L -> L -> Type) -> ProofSystem
| SequentStyle : (Multiset L -> Multiset L -> Type) -> ProofSystem

/--
Proof systems typically fall into one of a few catagories.
-/
class ProofClass (L : Type) (S : @ProofSystem L) : Type


def Provablity [inst : ProofClass L S] : Prop := by
  cases S



notation Γ "T⊢[" L "]" φ => Proof L Γ φ

/--
Provability is an inductively defined proposition
that takes a ProofSystem and reaturns a provability relation.
-/
inductive Prov (P : Proof L) : Multiset L -> L -> Prop :=
| intro {φ : L} {Γ : Multiset L} : Nonempty (P Γ φ) -> Prov P Γ φ

theorem prov_of_proof {P : Proof L} :
(P Γ φ) -> (Prov P Γ φ) := by
  intro H
  exact Prov.intro ⟨H⟩

/-
If we have that φ is provable from Γ in a system P, then the type of
proofs of φ from Γ is `Nonempty`. This allows us to
use the axiom of choice to extract an arbitrary proof of a
fact merely from us knowing that it is provable.
-/
theorem prov_imp_proof_nonempty : (Prov P Γ φ) -> Nonempty (P Γ φ) := by
  intro H1
  cases H1
  assumption

/-
Use classical.choice to create a proof from a proof of provability.
-/
noncomputable def proof_of_prov : (Prov P Γ φ) -> (P Γ φ) := by
  intro H
  exact Classical.choice (prov_imp_proof_nonempty H)


instance : Coe (P Γ φ) (Prov P Γ φ) := ⟨prov_of_proof⟩

noncomputable instance : Coe (Prov P Γ φ) (P Γ φ) := ⟨proof_of_prov⟩

theorem proof_exists {P : Proof L} :
(P Γ φ) → ∃(_ : P Γ φ), True := by
  intro h
  exact ⟨h, trivial⟩
