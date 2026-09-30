import H0mework.Chemistry.LAlanineContinuousSource.RK4ReplayChecks
import H0mework.Chemistry.LAlanineParametric.MatrixBounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceChart

open SourceRectangle SourceRK4Replay SourceSignedEvaluator ContinuousChart
open IntervalParameterMap
open scoped BigOperators

def weights : Fin 3 → ℚ := ![10, 1 / 400, 1 / 32]
def middle (a : Pair) : ℚ := (a.1 + a.2) / 2

def signedDet (a : Fin 3 → Fin 3 → ℚ) : ℚ :=
  a 0 0 * (a 1 1 * a 2 2 - a 1 2 * a 2 1) -
  a 0 1 * (a 1 0 * a 2 2 - a 1 2 * a 2 0) +
  a 0 2 * (a 1 0 * a 2 1 - a 1 1 * a 2 0)

def adjugateThree (a : Fin 3 → Fin 3 → ℚ) : Fin 3 → Fin 3 → ℚ :=
  ![![a 1 1 * a 2 2 - a 1 2 * a 2 1, a 0 2 * a 2 1 - a 0 1 * a 2 2,
      a 0 1 * a 1 2 - a 0 2 * a 1 1],
    ![a 1 2 * a 2 0 - a 1 0 * a 2 2, a 0 0 * a 2 2 - a 0 2 * a 2 0,
      a 0 2 * a 1 0 - a 0 0 * a 1 2],
    ![a 1 0 * a 2 1 - a 1 1 * a 2 0, a 0 1 * a 2 0 - a 0 0 * a 2 1,
      a 0 0 * a 1 1 - a 0 1 * a 1 0]]

def precondition (a : Fin 3 → Fin 3 → ℚ) (i j : Fin 3) : ℚ :=
  ((⌊(2 : ℚ)^20 * (adjugateThree a i j / signedDet a / weights i)⌋ : ℤ) : ℚ) / (2 : ℚ)^20

noncomputable section

/-- A small exact normal form; `preconditioner_generated` checks all nine source calculations. -/
def preconditioner (i j : Fin 3) : ℚ :=
  ((![![411896893, 143868237, 66759258], ![-184683460, 382118806, 309854970],
    ![34308374, -251617631, 331542577]] i j : ℤ) : ℚ) / (2 : ℚ)^20
def weightsMatrix (i j : Fin 3) : ℚ := if i = j then weights i else 0
def inputScale : SourceGaussianModel.Point →L[ℝ] SourceGaussianModel.Point := matrixLinear weightsMatrix
def outputScale : SourceGaussianModel.Point →L[ℝ] SourceGaussianModel.Point := matrixLinear preconditioner
def preconditionedDerivativeBox : MatrixPair :=
  matrixMultiply (matrixMultiply (fun i j => point (preconditioner i j)) reportedTargetJacobian)
    (fun i j => point (weightsMatrix i j))
def errorBox (i j : Fin 3) : Pair :=
  sub (preconditionedDerivativeBox i j) (point (if i = j then 1 else 0))

theorem preconditioner_generated (i j : Fin 3) :
    preconditioner i j = precondition (fun i j => middle (reportedTargetJacobian i j)) i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem preconditioner_of_actual_derivative (i j : Fin 3) :
    preconditioner i j = precondition (fun i j => middle ((generatedStates 4).derivative i j)) i j := by
  simp only [target_derivative_recomputed]
  exact preconditioner_generated i j

theorem error_rows_small : ∀ i : Fin 3, (∑ j : Fin 3, magnitude (errorBox i j)) ≤ (1 / 2 : ℚ) := by
  decide +kernel

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceChart
