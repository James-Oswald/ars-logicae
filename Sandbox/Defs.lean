
-- import Mathlib.Data.Finset.Basic

-- import ArsLogicae.ALC.Language

-- open ALC

-- def KB := Finset ALC

-- instance : Coe KB (Finset ALC) := ⟨id⟩
-- instance : Membership ALC KB := ⟨λx y => x ∈ (y : Finset ALC)⟩

-- def is_assetion : ALC -> Prop
-- | ALC.is _ _ => true
-- | ALC.role _ _ _ => true
-- | _ => false

-- instance : DecidablePred is_assetion := by
--   simp [DecidablePred]
--   intro a
--   cases a
--   repeat
--   . simp only [is_assetion]
--     exact decidableTrue
--   repeat
--   . simp only [is_assetion]
--     exact decidableFalse

-- --Returns the subkb of assertions
-- def Abox (kb : KB) : KB :=
--   kb.filter is_assetion

-- --Returns the subkb of teminological assertions
-- def Tbox (kb : KB) : KB :=
--   kb.filter (λx => ¬is_assetion x)
