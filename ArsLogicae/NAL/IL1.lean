
import Mathlib.Data.Finset.Basic

inductive IL1 where
| inher : String -> String -> IL1

infix:55 "→ₙ" => IL1.inher

-- /-O(n^2) algo for generating the transitive closure of a list of IL formulae-/
-- def transClose : List IL1 -> List IL1
-- | [] => []
-- | (t1 →ₙ t2)::t =>


inductive sat : List IL1 -> IL1 -> Prop
| rfl (t : String) : sat _ (t →ₙ t)
| trans (t1 t2 t3 : String) : sat _ (t1 →ₙ t2) -> sat _ (t2 →ₙ t3) -> sat _ (t1 →ₙ t3)
