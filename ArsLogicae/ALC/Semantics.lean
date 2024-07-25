
import ArsLogicae.ALC.Language

import Mathlib.Data.Finset.Prod

--An interpretation is a
structure Interp where
  D : Finset String

  II : Indivdual -> String
  II_sub : ∀ (I : Indivdual), II I ∈ D

  IR : Role -> Finset (String × String)
  IR_sub : ∀ (R : Role), IR R ⊆ Finset.product D D

  IC : Concept -> Finset String
  IC_sub : ∀ (C : Concept), IC C ⊆ D
  --Properties of the concept interpretation function must satisfy
  IC_top : IC Concept.Top = D
  IC_bot : IC Concept.Bot = ∅
  IC_not : ∀ (C : Concept), IC (Concept.not C) = D \ IC C
  IC_inter : ∀ (A B : Concept), IC (Concept.inter A B) = IC A ∩ IC B
  IC_union : ∀ (A B : Concept), IC (Concept.union A B) = IC A ∪ IC B
  IC_all : ∀ (R : Role) (C : Concept),
    IC (Concept.all R C) = {x ∈ D | ∀ y, (x, y) ∈ IR R → y ∈ IC C}
  IC_some : ∀ (R : Role) (C : Concept),
    IC (Concept.some R C) = {x ∈ D | ∃ y, (x, y) ∈ IR R ∧ y ∈ IC C}

--Basic IC function we can use
def IC (D : Finset String) (ICB : String -> Finset String)
(IR : Role -> Finset (String × String)) : Concept -> Finset String
| Concept.atom s => ICB s
| Concept.Top => D
| Concept.Bot => ∅
| Concept.not A => D \ IC D ICB IR A
| Concept.inter A B => IC D ICB IR A ∩ IC D ICB IR B
| Concept.union A B => IC D ICB IR A ∪ IC D ICB IR B
| Concept.all R C => D.filter (λx => ∀ y ∈ D, (x, y) ∈ IR R → y ∈ IC D ICB IR C)
| Concept.some R C => D.filter (λx => ∃ y ∈ D, (x, y) ∈ IR R → y ∈ IC D ICB IR C)

def holds (I : Interp) : ALC -> Prop
| ALC.is i c => I.II i ∈ I.IC c
| ALC.role i j r => (I.II i, I.II j) ∈ I.IR r
| ALC.inc c d => I.IC c ⊆ I.IC d
| ALC.eq c d => I.IC c = I.IC d

def valid (I : Interp) (kb : Finset ALC) : Prop :=
  ∀ a ∈ kb, holds I a
