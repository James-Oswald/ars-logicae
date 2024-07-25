
inductive Indivdual where
| atom : String -> Indivdual

inductive Role where
| atom : String -> Role

inductive Concept where
| atom : String -> Concept
| Top : Concept
| Bot : Concept
| not : Concept -> Concept
| inter : Concept -> Concept -> Concept
| union : Concept -> Concept -> Concept
| some : Role -> Concept -> Concept
| all : Role -> Concept -> Concept

inductive ALC where
| is : Indivdual -> Concept -> ALC
| role : Indivdual -> Indivdual -> Role -> ALC
| inc : Concept -> Concept -> ALC
| eq : Concept -> Concept -> ALC
