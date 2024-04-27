
import Mathlib.Data.Multiset.Basic

/-
The typeclasses of the three most common proof systems
-/
class HilbertProofSystem {L : Type} (S : L -> Type) : Prop
class NDProofSystem {L : Type} (S : Multiset L -> L -> Type) : Prop
class SequentProofSystem {L : Type} (S : Multiset L -> Multiset L -> Type) : Prop

--Proof System Casting
instance [NDProofSystem S] : HilbertProofSystem (S ∅) := ⟨⟩
instance [SequentProofSystem S]: NDProofSystem (λ H L => S H {L}) := ⟨⟩
instance [HilbertProofSystem (S ∅)]: NDProofSystem S := ⟨⟩
instance {S : Multiset L -> Multiset L -> Type} [NDProofSystem (λ H L => S H {L})] :
  SequentProofSystem S := ⟨⟩

theorem Hilbert_iff_ND : HilbertProofSystem (S ∅) ↔ NDProofSystem S :=
  Iff.intro (λ _ => NDProofSystem.mk) (λ _ => HilbertProofSystem.mk)

theorem Hilbert_iff_ND' : HilbertProofSystem S ↔ NDProofSystem (λ _ => S) :=
  Iff.intro (λ _ => NDProofSystem.mk) (λ _ => HilbertProofSystem.mk)

theorem ND_iff_Sequent {S : Multiset L -> Multiset L -> Type} :
NDProofSystem (λ H L => S H {L}) ↔ SequentProofSystem S :=
  Iff.intro (λ _ => SequentProofSystem.mk) (λ _ => NDProofSystem.mk)

def SequentProvablity [@SequentProofSystem L S] (Γ1 Γ2 : Multiset L) : Prop :=
  Nonempty (S Γ1 Γ2)
def NaturalDeductionProvablity [@NDProofSystem L S] (Γ : Multiset L) (φ : L) : Prop :=
  Nonempty (S Γ φ)
def HilbertProvablity [@HilbertProofSystem L S] (φ : L) : Prop :=
  Nonempty (S φ)

theorem HProv_iff_NDProv [HilbertProofSystem S]:
HilbertProvablity φ ↔ NaturalDeductionProvablity ∅ φ :=
  Iff.intro (λ h => ⟨h⟩) (λ h => ⟨h⟩)

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
