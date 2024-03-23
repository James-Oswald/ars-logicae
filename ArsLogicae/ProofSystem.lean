
import Mathlib.Data.Multiset.Basic

/--
A language has a proof system if provided with an inductive infrence rule
construction function.
-/
class ProofSystem (L : Type) where
  Proof : Multiset L -> L -> Type

/--
If L has a proof system in which we can construct proofs,
then we can define the notion of provability as the existence of a proof.
-/
inductive Prov [inst : ProofSystem L] : Multiset L -> L -> Prop where
| intro {φ : L} : Nonempty (inst.Proof Γ φ) -> Prov Γ φ

theorem proof_exists [inst : ProofSystem L] :
(inst.Proof Γ φ) → ∃(_ : inst.Proof Γ φ), True := by
  intro h
  exact ⟨h, trivial⟩

theorem prov_of_proof [inst : ProofSystem L] :
(inst.Proof Γ φ) -> (Prov Γ φ) := by
  intro H
  exact Prov.intro ⟨H⟩

/-
If we have that φ is provable from Γ, then the type of
proofs of φ from Γ is `Nonempty`. This allows us to
use the axiom of choice to extract an arbitrary proof of a
fact merely from us knowing that it is provable.
-/
theorem PL.HProof.nonempty [inst : ProofSystem L]: (Prov Γ φ) -> Nonempty (inst.Proof Γ φ) := by
  intro H1
  cases H1
  assumption

/-
Use classical.choice to create a proof from a proof of provability.
-/
noncomputable def proof_of_prov [inst : ProofSystem L]: (Prov Γ φ) -> (inst.Proof Γ φ) := by
  intro H
  exact Classical.choice (PL.HProof.nonempty H)

instance [inst : ProofSystem L] : Coe (inst.Proof Γ φ) (Prov Γ φ) := ⟨prov_of_proof⟩

noncomputable instance [inst : ProofSystem L] : Coe (Prov Γ φ) (inst.Proof Γ φ) := ⟨proof_of_prov⟩
