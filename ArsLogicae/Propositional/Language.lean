
/-!
This file contains a standard definition of the language of propositional
logic, as well as some basic notations.
-/

/--
An atom is some finite string of characters.
-/
def Atom := String
deriving Repr, BEq, DecidableEq, Inhabited

inductive PL where
| atom (a : Atom): PL
| not (φ : PL) : PL
| and (φ ψ : PL): PL
deriving Repr, BEq, DecidableEq, Inhabited

prefix:70 "¬ₒ" => PL.not
infixr:65 "∧ₒ"  => PL.and

def PL.or (φ ψ : PL) : PL := ¬ₒ(¬ₒφ ∧ₒ ¬ₒψ)
infixr:60 "∨ₒ" => PL.or

def PL.implies (φ ψ : PL) : PL := ¬ₒφ ∨ₒ ψ
infixl:55 "⊃₀" => PL.implies
infixl:55 "→ₒ" => PL.implies

def PL.iff (φ ψ : PL) : PL := (φ →ₒ ψ) ∧ₒ (ψ →ₒ φ)
infix:50 "≡ₒ" => PL.iff
infix:50 "↔ₒ" => PL.iff

def PL.true : PL := PL.atom "A" →ₒ PL.atom "A"
notation "⊤ₒ" => PL.true

def PL.false : PL := ¬ₒ⊤ₒ
notation "⊥ₒ" => PL.false
