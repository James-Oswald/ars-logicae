
import ArsLogicae.ALC.Semantics



def ExDomain : Finset String := {
  "Albedo", "Ainz", "Nazarik",
  "E-Rantel", "Baruth", "Jirc",
  "Gazef", "Brain", "Climb", "Unknown"
}

def ExConcepts : String -> Finset String
| "Human" => {"Gazef", "Brain", "Climb", "Jirc"}
| "Undead" => {"Albedo", "Ainz"}
| "Location" => {"Nazarik", "E-Rantel", "Baruth"}
| _ => ∅


def ExRoles (r : Role) : Finset (String × String) :=
  match r with
  | Role.atom s =>
    match s with
    | "is_in" => {
      ("Albedo", "Nazarik"), ("Ainz", "Nazarik"), ("Nazarik", "Baruth"),
      ("Ainz", "E-Rantel"), ("Jirc", "Baruth"), ("Gazef", "E-Rantel"),
      ("Brain", "E-Rantel"), ("Climb", "E-Rantel")}
    | "is_loyal_to" => {
      ("Gazef", "Brain"), ("Brain", "Climb"), ("Climb", "Gazef"),
      ("Albedo", "Ainz")}
    | _ => ∅

def ExIndivduals (i : Indivdual) : String :=
  match i with
  | Indivdual.atom s =>
    match s with
    | "Albedo" => "Albedo"
    | "Ainz" => "Ainz"
    | "Nazarik" => "Nazarik"
    | "E-Rantel" => "E-Rantel"
    | "Baruth" => "Baruth"
    | "Jirc" => "Jirc"
    | "Gazef" => "Gazef"
    | "Brain" => "Brain"
    | "Climb" => "Climb"
    | _ => "Unknown"

def ExInterp : Interp := {
  D := ExDomain,
  II := ExIndivduals,
  II_sub := by
    intros I
    cases I
    simp [ExIndivduals]
    split
    decide
    decide
    decide
    decide
    decide
    decide
    decide
    decide
    decide
    decide
  IR := ExRoles,
  IR_sub := by
    intros R
    cases R
    simp [ExRoles]
    split
    decide
    decide
    decide
  IC := IC ExDomain ExConcepts ExRoles,
  IC_sub := by
    intro c
    induction c
    . simp [IC, ExConcepts]
      split
      . decide
      . decide
      . decide
      . decide
    . decide
    . decide
    . simp [IC]
    . simp [IC]
      sorry
      --apply Finset.inter_subset
    . simp [IC]
      apply Finset.union_subset
      assumption
      assumption
    . simp [IC]
    . simp [IC]
  IC_top := by
    simp [IC]
  IC_bot := by
    simp [IC]
  IC_not := by
    simp [IC]
  IC_inter := by
    simp [IC]
  IC_union := by
    simp [IC]
  IC_all := by
    intros r c
    simp [IC]
    sorry
  IC_some := by
    sorry
}
