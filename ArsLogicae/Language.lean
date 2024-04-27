

-- Lean 4

def curry (f: α × β -> γ) : α -> β -> γ :=
λ x y => f (x, y)

def add (ns : Nat × Nat) : Nat := ns.1 + ns.2

#check add            -- Nat × Nat -> Nat
#check curry add      -- Nat -> Nat -> Nat

#eval add (2, 2)      -- 4
#eval (curry add) 2 2 -- 4
