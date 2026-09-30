import H0mework.Chemistry.LAlanineContinuousSource.SourceRectangle
import H0mework.Chemistry.LAlanineParametric.SeedDerivative

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceCellGeometry

open Lean Elab Term Command SourceGaussianModel SourceSignedEvaluator SourceRectangle
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

private def declare (suffix : Name) (value : Expr) : TermElabM Unit := do
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

private def rational (value : Json) : TermElabM (Int × Nat) := do
  let row ← decode (Array Json) value
  unless row.size == 2 do throwError "cell rational pair"
  let numerator ← decode Int row[0]!
  let denominator ← decode Nat row[1]!
  unless denominator > 0 do throwError "cell rational denominator"
  pure (numerator, denominator)

private def integerPair (value : Json) : TermElabM (Int × Int) := do
  let row ← decode (Array Int) value
  unless row.size == 2 && row[0]! ≤ row[1]! do throwError "cell ordered integer interval"
  pure (row[0]!, row[1]!)

elab "generateCellGeometryReadouts" : command => liftTermElabM do
  let packet ← parse SourceRectangle.fieldText
  let rectangle ← parse SourceRectangle.rectangleText
  let initial ← field packet "initial"
  let scope ← field packet "actual_scope"
  let incidence ← field rectangle "rectangle_incidence"
  let fields ← decode (Array Json) (← field packet "source_fields")
  unless (← field initial "coordinate_integer_box") == (← field fields[0]! "box_integer_intervals") &&
      (← field initial "coordinate_integer_box") == (← field incidence "source_coordinate_integer_box") do
    throwError "same first field and source initial position"
  let derivative ← decode (Array Json) (← field initial "parameter_derivative_integer_box")
  unless derivative.size == 3 do throwError "source initial derivative rows"
  let derivative ← derivative.mapM fun row => do
    let row ← decode (Array Json) row
    unless row.size == 3 do throwError "source initial derivative columns"
    row.mapM integerPair
  declare `rawInitialDerivative (toExpr derivative)
  let mut domain : Array (Array (Int × Nat)) := #[]
  for key in ["alpha", "v", "flow_parameter"] do
    let ends ← decode (Array Json) (← field scope key)
    unless ends.size == 2 do throwError "source parameter axis"
    domain := domain.push (← ends.mapM rational)
  declare `rawParameterDomain (toExpr domain)
  for (name, key) in [(`rawBandWidth, "band_width_integer_interval"), (`rawBandSlope, "band_slope_integer_interval")] do
    declare name (toExpr (← integerPair (← field initial key)))
  for (name, key) in [(`rawParameterU, "parameter_u_integer_interval"), (`rawParameterV, "parameter_v_integer_interval")] do
    declare name (toExpr (← integerPair (← field incidence key)))
  declare `rawReportedVolume (toExpr (← rational (← field (← field packet "target") "parameter_measure")))

generateCellGeometryReadouts

noncomputable section

def reportedInitialDerivative (axis direction : Fin 3) : Pair :=
  integerInterval ((rawInitialDerivative[axis.val]!)[direction.val]!)

def reportedParameter (axis : Fin 3) : Pair :=
  (SourceFiniteData.ratRead ((rawParameterDomain[axis.val]!)[0]!),
    SourceFiniteData.ratRead ((rawParameterDomain[axis.val]!)[1]!))

def reportedBandWidth : Pair := integerInterval rawBandWidth
def reportedBandSlope : Pair := integerInterval rawBandSlope
def reportedParameterU : Pair := integerInterval rawParameterU
def reportedParameterV : Pair := integerInterval rawParameterV
def reportedVolume : ℚ := SourceFiniteData.ratRead rawReportedVolume

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceCellGeometry
