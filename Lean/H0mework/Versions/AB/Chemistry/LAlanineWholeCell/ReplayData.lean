import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.SourceData
import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.ReplayInitial
import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.ChartData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellReplay

open Lean Elab Term Command WholeCellSource SourceSignedEvaluator SourceRectangle
open WholeCellPartition IntervalParameterMap
open Inertia.SourceParsing

private def vector (value : Json) : TermElabM (Array (Int × Int)) := do
  (← sourceArray value 3).mapM sourceInterval
private def matrix (value : Json) : TermElabM (Array (Array (Int × Int))) := do
  (← sourceArray value 3).mapM vector
private def rationalVector (value : Json) : TermElabM (Array (Int × Nat)) := do
  (← sourceArray value 3).mapM sourceRational
private def rationalMatrix (value : Json) : TermElabM (Array (Array (Int × Nat))) := do
  (← sourceArray value 3).mapM rationalVector

elab "generateWholeCellReplayReceipts" : command => liftTermElabM do
  let packet ← verifiedPacket
  let leaves ← sourceArray (← field packet "leaves") 4
  let lower ← leaves.mapM fun leaf => do
    #["alpha", "v", "s"].mapM fun key => do
      let endpoints ← sourceArray (← field leaf key) 2
      sourceRational endpoints[0]!
  let upper ← leaves.mapM fun leaf => do
    #["alpha", "v", "s"].mapM fun key => do
      let endpoints ← sourceArray (← field leaf key) 2
      sourceRational endpoints[1]!
  declareSource `rawLower (toExpr lower)
  declareSource `rawUpper (toExpr upper)
  for (name, key) in [(`rawTargetPosition, "target_integer_box"),
      (`rawStepDerivative, "step_derivative_integer_vector")] do
    declareSource name (toExpr (← leaves.mapM fun leaf => do vector (← field leaf key)))
  declareSource `rawTargetJacobian
    (toExpr (← leaves.mapM fun leaf => do matrix (← field leaf "jacobian_integer_box")))
  for (name, key) in [(`rawTargetLaplacian, "laplacian_integer_interval"),
      (`rawTargetDeterminant, "determinant_integer_interval"),
      (`rawTargetIntegrand, "integrand_integer_interval"),
      (`rawTargetIntegral, "signed_integral_integer_interval"),
      (`rawStepSize, "step_size_integer_interval")] do
    declareSource name (toExpr (← leaves.mapM fun leaf => do sourceInterval (← field leaf key)))
  let initial ← field packet "initial"
  declareSource `rawInitialPosition (toExpr (← vector (← field initial "position")))
  declareSource `rawInitialDerivative (toExpr (← matrix (← field initial "parameter_jacobian")))
  declareSource `rawCommonJacobian (toExpr (← matrix (← field packet "whole_cell_jacobian_integer_box")))
  let condition ← field packet "whole_cell_condition"
  declareSource `rawWeights (toExpr (← rationalVector (← field condition "weights")))
  declareSource `rawPreconditioner (toExpr (← rationalMatrix (← field condition "preconditioner")))
  declareSource `rawError (toExpr (← matrix (← field condition "error_integer_box")))
  declareSource `rawNormBound (toExpr (← sourceRational (← field condition "norm_ceiling")))
  let balance ← field condition "balance_trace"
  declareSource `rawSlack (toExpr (← rationalVector (← field balance "slack_vector")))
  declareSource `rawInitialError
    (toExpr (← matrix (← field (← field balance "initial") "error_integer_box")))

generateWholeCellReplayReceipts

noncomputable section

def reportedLower (q : Quarter) (axis : Fin 3) : ℚ := rationalRead ((rawLower[q.val]!)[axis.val]!)
def reportedUpper (q : Quarter) (axis : Fin 3) : ℚ := rationalRead ((rawUpper[q.val]!)[axis.val]!)
def reportedTargetPosition (q : Quarter) : VectorPair := fun axis => integerInterval ((rawTargetPosition[q.val]!)[axis.val]!)
def reportedTargetJacobian (q : Quarter) : MatrixPair := fun axis direction =>
  integerInterval (((rawTargetJacobian[q.val]!)[axis.val]!)[direction.val]!)
def reportedTargetLaplacian (q : Quarter) : Pair := integerInterval (rawTargetLaplacian[q.val]!)
def reportedTargetDeterminant (q : Quarter) : Pair := integerInterval (rawTargetDeterminant[q.val]!)
def reportedTargetIntegrand (q : Quarter) : Pair := integerInterval (rawTargetIntegrand[q.val]!)
def reportedTargetIntegral (q : Quarter) : Pair := integerInterval (rawTargetIntegral[q.val]!)
def commonJacobian : MatrixPair := fun i j => integerInterval ((rawCommonJacobian[i.val]!)[j.val]!)
def weights (i : Fin 3) : ℚ := rationalRead (rawWeights[i.val]!)
def preconditioner (i j : Fin 3) : ℚ := rationalRead ((rawPreconditioner[i.val]!)[j.val]!)
def reportedError (i j : Fin 3) : Pair := integerInterval ((rawError[i.val]!)[j.val]!)
def normBound : ℚ := rationalRead rawNormBound
def reportedSlack (i : Fin 3) : ℚ := rationalRead (rawSlack[i.val]!)
def reportedInitialError (i j : Fin 3) : Pair := integerInterval ((rawInitialError[i.val]!)[j.val]!)

theorem quarter_source_bounds : ∀ q : Quarter, ∀ axis : Fin 3,
    reportedLower q axis = quarterLowerQ q axis ∧ reportedUpper q axis = quarterUpperQ q axis := by decide +kernel

theorem initial_position_reused : ∀ axis : Fin 3,
    integerInterval (rawInitialPosition[axis.val]!) = SourceCellGeometry.initialJetBox.position axis := by decide +kernel
theorem initial_derivative_reused : ∀ axis direction : Fin 3,
    integerInterval ((rawInitialDerivative[axis.val]!)[direction.val]!) =
      SourceCellGeometry.initialJetBox.derivative axis direction := by decide +kernel
theorem step_size_recomputed : ∀ q : Quarter, stepSizeInterval q = integerInterval (rawStepSize[q.val]!) := by decide +kernel
theorem step_derivative_reused : ∀ q : Quarter, ∀ direction : Fin 3,
    SourceCellGeometry.stepDerivativeInterval direction =
      integerInterval ((rawStepDerivative[q.val]!)[direction.val]!) := by decide +kernel

end
end LAlanine40K2025.BasinRefinement.WholeCellReplay
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
