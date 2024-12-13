
import ArsLogicae.ALC.Language

import Mathlib.Data.Finset.Prod

import Std.Data.HashMap

structure Interp where
  D : Finset String
  II : String -> String
  II_sub : ∀ i, II i ∈ D
  IC : String -> Finset String
  IC_sub : ∀ c, IC c ⊆ D
  IR : String -> Finset (String × String)
  IR_sub : ∀ r, IR r ⊆ Finset.product D D

--Basic IC function we can use
def ICC (I : Interp) : Concept -> Finset String
| Concept.atom s => I.IC s
| Concept.Top => I.D
| Concept.Bot => ∅
| Concept.not A => I.D \ ICC I A
| Concept.inter A B => ICC I A ∩ ICC I B
| Concept.union A B => ICC I A ∪ ICC I B
| Concept.all (Role.atom R) C => I.D.filter (λx => ∀ y ∈ I.D, (x, y) ∈ I.IR R → y ∈ ICC I C)
| Concept.some (Role.atom R) C => I.D.filter (λx => ∃ y ∈ I.D, (x, y) ∈ I.IR R → y ∈ ICC I C)

def holds (I : Interp) : ALC -> Prop
| ALC.is (Indivdual.atom i) c => I.II i ∈ ICC I c
| ALC.role (Indivdual.atom i) (Indivdual.atom j) (Role.atom r) => (I.II i, I.II j) ∈ I.IR r
| ALC.inc c d => ICC I c ⊆ ICC I d
| ALC.eq c d => ICC I c = ICC I d

def holds_kb (I : Interp) (kb : Finset ALC) : Prop :=
  ∀ a ∈ kb, holds I a

def sampleDomain : Finset String := {"Albedo", "Ainz", "Nazarik", "E-Rantel", "Baruth", "Jirc", "Gazef", "Brain", "Climb"}

def samepleConcepts : Std.HashMap String (Finset String) :=
  Std.HashMap.ofList [
    ("character", {"Albedo", "Ainz", "Jirc", "Gazef", "Brain", "Climb"}),
    ("location", {"Nazarik", "E-Rantel", "Baruth"})
  ]

def sampleRoles : Std.HashMap String (Finset (String × String)) :=
  Std.HashMap.ofList [
    ("is_in", {("Albedo", "Nazarik"), ("Ainz", "Nazarik"), ("Nazarik", "Baruth"),
              ("Ainz", "E-Rantel"), ("Jirc", "Baruth"), ("Gazef", "E-Rantel"),
              ("Brain", "E-Rantel"), ("Climb", "E-Rantel")}),
    ("is_loyal_to", {("Gazef", "Brain"), ("Brain", "Climb"), ("Climb", "Gazef"),
                     ("Albedo", "Ainz")})
  ]

def sampleInterp : Interp := {
  D := sampleDomain ∪ {"Unknown"},
  II := λi => if i ∈ sampleDomain then i else "Unknown",
  II_sub := by
    intro i
    simp
    split
    all_goals simp [*]
  IC := λk => samepleConcepts.findD k ∅,
  IC_sub := by
    intro k
    simp [*]




}
