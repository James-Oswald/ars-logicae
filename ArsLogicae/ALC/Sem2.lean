
import ArsLogicae.ALC.Language

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod

structure Interp where
  D : Finset String
  II : String -> String
  II_sub : ∀ i, II i ∈ D
  IC : String -> Finset String
  IC_sub : ∀ c, IC c ⊆ D
  IR : String -> Finset (String × String)
  IR_sub : ∀ r, IR r ⊆ Finset.product D D

/- An ALC statement holds under some interpretation I
| Concept.all R C => D.filter (λx => ∀ y ∈ D, (x, y) ∈ IR R → y ∈ IC D ICB IR C)
| Concept.some R C => D.filter (λx => ∃ y ∈ D, (x, y) ∈ IR R → y ∈ IC D ICB IR C)

-/
--Termination hell, not playing this game
partial def holds (I : Interp) : ALC -> Prop
| ALC.role (Indivdual.atom a1) (Indivdual.atom a2) (Role.atom r) => (a1, a2) ∈ I.IR r
| ALC.is _ Concept.Top => True
| ALC.is _ Concept.Bot => False
| ALC.is (Indivdual.atom a) (Concept.atom s) => I.II a ∈ I.IC s
| ALC.is i (Concept.not c) => ¬(holds I (ALC.is i c))
| ALC.is i (Concept.inter c d) => holds I (ALC.is i c) ∧ holds I (ALC.is i d)
| ALC.is i (Concept.union c d) => holds I (ALC.is i c) ∨ holds I (ALC.is i d)
| ALC.is i (Concept.all r c) => ∀a ∈ I.D, holds I (ALC.role i (Indivdual.atom a) r) ->
                                holds I (ALC.is (Indivdual.atom a) c)
| ALC.is i (Concept.some r c) => ∃a ∈ I.D, holds I (ALC.role i (Indivdual.atom a) r) ->
                                holds I (ALC.is (Indivdual.atom a) c)
| ALC.inc c d => ∀a ∈ I.D, holds I (ALC.is (Indivdual.atom a) c) ->
                 holds I (ALC.is (Indivdual.atom a)  d)
| ALC.eq c d => ∀a ∈ I.D, holds I (ALC.is (Indivdual.atom a) c) ↔
                 holds I (ALC.is (Indivdual.atom a)  d)
