
import Mathlib.Data.Multiset.Basic

/-
The typeclasses of the three most common proof systems
-/
class HilbertProofSystem {L : Type} (S : L -> Type) : Prop
class NDProofSystem {L : Type} (S : Multiset L -> L -> Type) : Prop
class SequentProofSystem {L : Type} (S : Multiset L -> Multiset L -> Type) : Prop

/--
Something is provable if the type of proof trees for a formulae or sequent is nonempty.
-/
def HilbertProv [@HilbertProofSystem L S] (φ : L) : Prop :=
  Nonempty (S φ)
def NaturalDeductionProv [@NDProofSystem L S] (Γ : Multiset L) (φ : L) : Prop :=
  Nonempty (S Γ φ)
def SequentProv [@SequentProofSystem L S] (Γ1 Γ2 : Multiset L) : Prop :=
  Nonempty (S Γ1 Γ2)


theorem prov_of_Hproof [HilbertProofSystem S] :
(S φ) -> (HilbertProv φ) := by
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
