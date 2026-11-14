import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Encoding.Syntax
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Dense

/-! The default source algorithm consumes the fixed original bit parser. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Encoding

/-- Generate and reduce the original source before the remaining component decisions. -/
def decideBits (bits : List Bool) : Bool :=
  match parse bits with
  | none => false
  | some input => Dense.decideFormula input.2

theorem decideBits_invalid (bits : List Bool) (invalid : parse bits = none) :
    decideBits bits = false := by simp [decideBits, invalid]

theorem decideBits_parsed (bits : List Bool) (input : Input)
    (parsed : parse bits = some input) :
    decideBits bits = true ↔ CNFSatisfiable input.2 := by
  simpa [decideBits, parsed] using Dense.decideFormula_correct input.2

theorem decideBits_encode (input : Input) :
    decideBits (encode input) = true ↔ CNFSatisfiable input.2 :=
  decideBits_parsed (encode input) input (parse_encode input)

theorem decideBits_correct (bits : List Bool) :
    decideBits bits = true ↔
      ∃ input : Input, parse bits = some input ∧ CNFSatisfiable input.2 := by
  cases parsed : parse bits with
  | none => simp [decideBits, parsed]
  | some input => simp [decideBits, parsed, Dense.decideFormula_correct]

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔
      ¬ ∃ input : Input, parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [Bool.eq_false_iff]
  exact not_congr (decideBits_correct bits)

end SaturationMonoid.ComplexityProjection.SATSource.Encoding
