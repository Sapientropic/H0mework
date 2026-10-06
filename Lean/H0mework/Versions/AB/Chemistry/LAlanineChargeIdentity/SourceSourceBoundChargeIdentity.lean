import H0mework.Versions.AB.Chemistry.LAlanineChargeIdentity.SourceParsing
import H0mework.Chemistry.LAlanineChargeIdentity.AlgebraMatrixScaling
import H0mework.Chemistry.LAlanineChargeIdentity.AlgebraRounding

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Source

open Lean Elab Term Command Inertia.SourceParsing LAlanine40K2025.Force.Interface SourceData

private def declareReadout (suffix : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

elab "generateChargeReadouts" : command => liftTermElabM do
  let packet ← SourceParsing.verifiedPacket
  let recovery ← field packet "recovery"
  let selection ← field recovery "selection"
  let protocol ← field packet "protocol"
  declareReadout `unitColumnBlocks (← SourceReification.fieldBlocks (← field packet "full_B_integer_blocks"))
  declareReadout `reportedResidualBlocks (← SourceReification.residualBlocks (← field recovery "full_field_residual_blocks"))
  declareReadout `selectedRows (← SourceReification.selected13 (← field selection "pivot_rows"))
  for (name, key) in [(`selectedBInteger, "selected_B_integer"), (`inverseNumerator, "left_inverse_numerators")] do
    declareReadout name (← SourceReification.matrix13 (← field selection key))
  for (name, key) in [(`reportedCharge, "decoded_Z"), (`reportedSelectedField, "selected_V_integer"),
      (`reportedSelectedResidual, "selected_residual_numerators")] do
    declareReadout name (← SourceReification.vector13 (← field recovery key))
  declareReadout `reportedRowAbsNumerator (← SourceReification.vector13 (← field selection "left_inverse_row_abs_numerators"))
  declareReadout `inverseDenominator (toExpr (← decode Nat (← field selection "left_inverse_denominator")))
  for (name, key) in [(`unitScale, "unit_column_scale"), (`fieldScale, "total_field_scale")] do
    declareReadout name (toExpr (← decode Nat (← field protocol key)))
  declareReadout `epsilon (← rationalExpr (← field protocol "absolute_channel_epsilon_hartree"))

set_option maxRecDepth 4096 in
generateChargeReadouts

noncomputable section
def fullBInteger : Matrix FieldRow Atom Int := fieldRead unitColumnBlocks
def reportedFullResidual : FieldRow → Int := residualRead reportedResidualBlocks
def selectedB : Matrix Atom Atom ℚ := Algebra.rationalMatrix selectedBInteger unitScale
def leftInverse : Matrix Atom Atom ℚ := Algebra.rationalMatrix inverseNumerator inverseDenominator
def fullB : Matrix FieldRow Atom ℚ := fun row atom => (fullBInteger row atom : ℚ) / unitScale
def fullField (row : FieldRow) : ℚ := (parentFieldInteger row : ℚ) / fieldScale
def selectedField (i : Atom) : ℚ := fullField (selectedRows i)
def decodedCharge (atom : Atom) : Int := round (Algebra.fieldCenter leftInverse selectedField atom)
def sourcePacketText : String := SourceParsing.sourceText

end
end LAlanine40K2025.ChargeIdentity.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
