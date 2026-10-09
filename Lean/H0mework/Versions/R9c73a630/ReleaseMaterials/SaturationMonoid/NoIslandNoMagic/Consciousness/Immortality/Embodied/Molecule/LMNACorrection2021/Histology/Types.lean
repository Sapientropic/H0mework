import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Histology

/-- Split source ASCII tokens with ordinary structural recursion. -/
def split (separator : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    if c == separator then [] :: split separator rest
    else match split separator rest with
      | [] => [[c]]
      | word :: words => (c :: word) :: words

def digits? (word : List Char) : Option Nat :=
  if word.isEmpty then none else word.foldlM (fun value c =>
    if 48 ≤ c.toNat && c.toNat ≤ 57 then some (10 * value + (c.toNat - 48)) else none) 0

def mantissa? (text : List Char) : Option ℚ := do
  match split '.' text with
  | [whole] => pure (← digits? whole : ℚ)
  | [whole, fraction] =>
    let w ← digits? whole
    let f ← digits? fraction
    let scale := 10 ^ fraction.length
    pure (((w * scale + f : Nat) : ℚ) / (scale : ℚ))
  | _ => none

/-- Exact stored decimal, including the original E-2 notation. -/
def decimalChars? (text : List Char) : Option ℚ := do
  match split 'E' text with
  | [mantissa] => mantissa? mantissa
  | [mantissa, exponent] =>
    let q ← mantissa? mantissa
    match exponent with
    | '-' :: digits =>
      let power ← digits? digits
      pure (q / ((10 ^ power : Nat) : ℚ))
    | _ =>
      let power ← digits? exponent
      pure (q * ((10 ^ power : Nat) : ℚ))
  | _ => none

def decimal? (text : String) : Option ℚ := decimalChars? text.toList

structure Cell where
  row : Nat
  column : Nat
  address : String
  kind : String
  stored : List Char
  text : String
  value : Option ℚ
  deriving DecidableEq, Repr, Inhabited

structure Measurement where
  density : ℚ
  adventitia : ℚ
  deriving DecidableEq, Repr, Inhabited

structure Section where
  sample : Nat
  label : String
  densityAddress : String
  areaAddress : String
  measured : Measurement
  deriving DecidableEq, Repr, Inhabited

def Improves (before after : Measurement) : Prop :=
  before.density < after.density ∧ after.adventitia < before.adventitia
instance (before after : Measurement) : Decidable (Improves before after) :=
  inferInstanceAs (Decidable (_ ∧ _))

def calibrate (density area : ℚ → ℚ) (measurement : Measurement) : Measurement :=
  ⟨density measurement.density, area measurement.adventitia⟩

theorem improvement_preserved (density area : ℚ → ℚ)
    (hd : StrictMono density) (ha : StrictMono area) (before after : Measurement)
    (improvement : Improves before after) :
    Improves (calibrate density area before) (calibrate density area after) :=
  ⟨hd improvement.1, ha improvement.2⟩

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Histology
