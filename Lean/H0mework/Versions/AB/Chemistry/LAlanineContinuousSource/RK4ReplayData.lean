import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.CellGeometry
import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalFourStep
import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalIntegral

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRK4Replay

open Lean Elab Term Command SourceRectangle SourceSignedEvaluator SourceCellGeometry IntervalParameterMap
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

private def integerPair (value : Json) : TermElabM (Int × Int) := do
  let row ← decode (Array Int) value
  unless row.size == 2 && row[0]! ≤ row[1]! do throwError "RK4 interval target shape"
  pure (row[0]!, row[1]!)

private def declare (name : Name) (value : Expr) : TermElabM Unit := do
  let name := (← getCurrNamespace) ++ name
  let type ← Meta.inferType value
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

elab "generateRK4TargetReadouts" : command => liftTermElabM do
  let packet ← parse SourceRectangle.fieldText
  let target ← field packet "target"
  let point ← decode (Array Json) (← field target "coordinate_integer_box")
  unless point.size == 3 do throwError "RK4 target dimension"
  declare `rawTargetPosition (toExpr (← point.mapM integerPair))
  let jacobian ← decode (Array Json) (← field target "parameter_jacobian_integer_box")
  unless jacobian.size == 3 do throwError "RK4 Jacobian rows"
  let jacobian ← jacobian.mapM fun row => do
    let values ← decode (Array Json) row
    unless values.size == 3 do throwError "RK4 Jacobian columns"
    values.mapM integerPair
  declare `rawTargetJacobian (toExpr jacobian)
  for (name, key) in [(`rawTargetLaplacian, "laplacian_integer_interval"),
      (`rawTargetDeterminant, "det_jacobian_integer_interval"),
      (`rawTargetIntegrand, "signed_integrand_integer_interval"),
      (`rawTargetIntegral, "signed_integral_integer_interval")] do
    declare name (toExpr (← integerPair (← field target key)))

generateRK4TargetReadouts

noncomputable section

def gradientIndex (axis : Fin 3) : SourceRectangle.Jet := ⟨axis.val + 1, by omega⟩
def hessianIndex (axis direction : Fin 3) : SourceRectangle.Jet :=
  ![![4, 5, 6], ![5, 7, 8], ![6, 8, 9]] axis direction

def recordedField (index : SourceRectangle.Field) : FieldBox :=
  ⟨fun axis => reportedDensity index (gradientIndex axis),
    fun axis direction => reportedDensity index (hessianIndex axis direction)⟩

def sourceCall (step stage : Fin 4) : SourceRectangle.Field := ⟨4 * step.val + stage.val, by omega⟩
def recordedFields (step stage : Fin 4) : FieldBox := recordedField (sourceCall step stage)
def generatedStates : Fin 5 → JetBox :=
  fourStepState recordedFields initialJetBox stepSizeInterval stepDerivativeInterval

def generatedStageInput (step stage : Fin 4) : JetBox :=
  match stage.val with
  | 0 => generatedStates step.castSucc
  | 1 => intervalStage2 (recordedFields step) (generatedStates step.castSucc) stepSizeInterval stepDerivativeInterval
  | 2 => intervalStage3 (recordedFields step) (generatedStates step.castSucc) stepSizeInterval stepDerivativeInterval
  | _ => intervalStage4 (recordedFields step) (generatedStates step.castSucc) stepSizeInterval stepDerivativeInterval

def reportedTargetPosition : VectorPair := fun axis => integerInterval (rawTargetPosition[axis.val]!)
def reportedTargetJacobian : MatrixPair := fun axis direction => integerInterval ((rawTargetJacobian[axis.val]!)[direction.val]!)
def reportedTargetLaplacian : Pair := integerInterval rawTargetLaplacian
def reportedTargetDeterminant : Pair := integerInterval rawTargetDeterminant
def reportedTargetIntegrand : Pair := integerInterval rawTargetIntegrand
def reportedTargetIntegral : Pair := integerInterval rawTargetIntegral

def generatedTargetLaplacian : Pair :=
  add (add (add (point 0) (reportedDensity 16 4)) (reportedDensity 16 7)) (reportedDensity 16 9)
def generatedTargetDeterminant : Pair := determinantPair (generatedStates 4).derivative
def generatedTargetIntegrand : Pair := mul generatedTargetLaplacian generatedTargetDeterminant

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRK4Replay
