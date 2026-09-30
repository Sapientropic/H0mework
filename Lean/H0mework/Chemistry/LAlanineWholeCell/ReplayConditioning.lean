import H0mework.Chemistry.LAlanineWholeCell.ReplayData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceSignedEvaluator SourceGaussianModel ContinuousChart IntervalParameterMap
open scoped BigOperators

noncomputable section

def midpointJacobian (i j : Fin 3) : ℚ := SourceChart.middle (commonJacobian i j)
def preconditionFor (w : Fin 3 → ℚ) (i j : Fin 3) : ℚ :=
  ((⌊(2 : ℚ)^20 * (SourceChart.adjugateThree midpointJacobian i j /
    SourceChart.signedDet midpointJacobian / w i)⌋ : ℤ) : ℚ) / (2 : ℚ)^20
def diagonalWeights (w : Fin 3 → ℚ) (i j : Fin 3) : ℚ := if i = j then w i else 0
def errorFor (w : Fin 3 → ℚ) (p : Fin 3 → Fin 3 → ℚ) (i j : Fin 3) : Pair :=
  sub (matrixMultiply (matrixMultiply (fun i j => point (p i j)) commonJacobian)
    (fun i j => point (diagonalWeights w i j)) i j) (point (if i = j then 1 else 0))

def initialError : MatrixPair := errorFor SourceChart.weights (preconditionFor SourceChart.weights)

/-- Literal intermediate normal forms are checked in source order in `ConditioningChecks`. -/
def slackSystem (i j : Fin 3) : ℚ := (if i = j then 1 else 0) - magnitude (reportedInitialError i j)
def calculatedSlack (i : Fin 3) : ℚ :=
  (∑ j : Fin 3, SourceChart.adjugateThree slackSystem i j) / SourceChart.signedDet slackSystem
def calculatedWeights (i : Fin 3) : ℚ :=
  ((⌈(2 : ℚ)^20 * SourceChart.weights i * reportedSlack i⌉ : ℤ) : ℚ) / (2 : ℚ)^20
def calculatedPreconditioner : Fin 3 → Fin 3 → ℚ := preconditionFor weights
def errorBox : MatrixPair := errorFor weights preconditioner
def reportedRowBound (i : Fin 3) : ℚ := ∑ j : Fin 3, magnitude (reportedError i j)
def calculatedNormBound : ℚ :=
  ((⌈(2 : ℚ)^20 * max (reportedRowBound 0) (max (reportedRowBound 1) (reportedRowBound 2))⌉ : ℤ) : ℚ) /
    (2 : ℚ)^20

def inputScale : Point →L[ℝ] Point := matrixLinear (diagonalWeights weights)
def outputScale : Point →L[ℝ] Point := matrixLinear preconditioner

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
