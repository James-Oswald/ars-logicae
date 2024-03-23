

# Design Principals

* The inductive type representing the language of each logic will be kept reasonably minimal, all other operators will be defined in terms of the set of minimal operators. For example, the propositional logic inductive type will only include atoms + the  `not` and `and` operators. First order logic will only add `forall` ontop of this, basic modal logic will only add box. 
