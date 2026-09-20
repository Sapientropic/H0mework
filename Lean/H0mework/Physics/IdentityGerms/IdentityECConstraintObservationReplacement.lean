import H0mework.Physics.IdentityGerms.IdentityECTemporalEvolutionSection

/-!
# Identity-contact EC constraint-observation replacement

A Cauchy initial-data write must not solve the twelve evolution rows a second
time.  Given a current curvature observation and an independently generated
action curvature observation, this module keeps the current spatial-column
rows and takes only the temporal-column constraint rows from the action
curvature.

The mixed observation is then installed with the existing full EC normal
section.  Consequently the complete twenty-dimensional action-normal kernel
is transported unchanged.  No source, residual, target equation, branch,
constraint receipt, or stationarity certificate is accepted here; this is a
finite-dimensional transporter for an action curvature generated elsewhere.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECConstraintObservationReplacement

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineGlobalIntegratedAction
open StageNineLinearPlebanskiCoframeActionPrincipal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Column-faithful observation splice -/

/-- Linear coordinate form of the mixed observation.  Column zero is the
independent Cauchy-constraint sector; columns one through three are the
evolution sector. -/
def identityECConstraintReplacementObservationLinear
    (current action : LorentzianCoframe →L[ℝ] ℝ) :
    LorentzianCoframe →ₗ[ℝ] ℝ where
  toFun := fun variation =>
    ∑ row : Fin 4, ∑ column : Fin 4,
      (if column = 0 then
          action (coframeCoordinateDirection row column)
        else
          current (coframeCoordinateDirection row column)) *
        variation row column
  map_add' := by
    intro first second
    simp only [Matrix.add_apply]
    simp_rw [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar variation
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro column _
    ring

/-- Continuous mixed coframe covector used by the faithful curvature target. -/
def identityECConstraintReplacementObservation
    (current action : LorentzianCoframe →L[ℝ] ℝ) :
    LorentzianCoframe →L[ℝ] ℝ :=
  (identityECConstraintReplacementObservationLinear current action
    ).toContinuousLinearMap

theorem identityECConstraintReplacementObservation_coordinateDirection
    (current action : LorentzianCoframe →L[ℝ] ℝ)
    (row column : Fin 4) :
    identityECConstraintReplacementObservation current action
        (coframeCoordinateDirection row column) =
      if column = 0 then
        action (coframeCoordinateDirection row column)
      else
        current (coframeCoordinateDirection row column) := by
  fin_cases row <;> fin_cases column <;>
    simp [identityECConstraintReplacementObservation,
      identityECConstraintReplacementObservationLinear,
      coframeCoordinateDirection, Fin.sum_univ_four]

/-- All twelve evolution rows are inherited from the current curvature
observation. -/
theorem identityECSpatialCoframeCoordinates_constraintReplacement
    (current action : LorentzianCoframe →L[ℝ] ℝ) :
    identityECSpatialCoframeCoordinatesOfCovector
        (identityECConstraintReplacementObservation current action) =
      identityECSpatialCoframeCoordinatesOfCovector current := by
  funext row direction
  unfold identityECSpatialCoframeCoordinatesOfCovector
  rw [identityECConstraintReplacementObservation_coordinateDirection]
  simp

/-- All four independent constraint rows come from the action curvature
observation. -/
theorem identityECConstraintCoordinates_constraintReplacement
    (current action : LorentzianCoframe →L[ℝ] ℝ) :
    identityECConstraintCoordinatesOfCovector
        (identityECConstraintReplacementObservation current action) =
      identityECConstraintCoordinatesOfCovector action := by
  funext row
  unfold identityECConstraintCoordinatesOfCovector
  rw [identityECConstraintReplacementObservation_coordinateDirection]
  simp

/-! ## Complete-kernel-faithful curvature target -/

/-- Replace only the four observed constraint rows while retaining the
current twelve evolution rows and complete action-normal kernel. -/
def identityDiracDualECConstraintReplacementCurvatureTarget
    (current actionCurvature : PhysicalBivector) : PhysicalBivector :=
  identityDiracDualECCurvatureTarget current
    (identityECConstraintReplacementObservation
      (identityDiracDualECCurvatureObservation current)
      (identityDiracDualECCurvatureObservation actionCurvature))

theorem identityDiracDualECCurvatureObservation_constraintReplacementTarget
    (current actionCurvature : PhysicalBivector) :
    identityDiracDualECCurvatureObservation
        (identityDiracDualECConstraintReplacementCurvatureTarget
          current actionCurvature) =
      identityECConstraintReplacementObservation
        (identityDiracDualECCurvatureObservation current)
        (identityDiracDualECCurvatureObservation actionCurvature) := by
  unfold identityDiracDualECConstraintReplacementCurvatureTarget
  exact identityDiracDualECCurvatureObservation_target _ _

theorem
    identityDiracDualECTemporalEvolutionObservation_constraintReplacementTarget
    (current actionCurvature : PhysicalBivector) :
    identityDiracDualECTemporalEvolutionObservation
        (identityDiracDualECConstraintReplacementCurvatureTarget
          current actionCurvature) =
      identityDiracDualECTemporalEvolutionObservation current := by
  change
    identityECSpatialCoframeCoordinatesOfCovector
        (identityDiracDualECCurvatureObservation
          (identityDiracDualECConstraintReplacementCurvatureTarget
            current actionCurvature)) =
      identityECSpatialCoframeCoordinatesOfCovector
        (identityDiracDualECCurvatureObservation current)
  rw [identityDiracDualECCurvatureObservation_constraintReplacementTarget]
  exact identityECSpatialCoframeCoordinates_constraintReplacement _ _

theorem identityDiracDualECConstraintObservation_constraintReplacementTarget
    (current actionCurvature : PhysicalBivector) :
    identityDiracDualECConstraintObservation
        (identityDiracDualECConstraintReplacementCurvatureTarget
          current actionCurvature) =
      identityDiracDualECConstraintObservation actionCurvature := by
  change
    identityECConstraintCoordinatesOfCovector
        (identityDiracDualECCurvatureObservation
          (identityDiracDualECConstraintReplacementCurvatureTarget
            current actionCurvature)) =
      identityECConstraintCoordinatesOfCovector
        (identityDiracDualECCurvatureObservation actionCurvature)
  rw [identityDiracDualECCurvatureObservation_constraintReplacementTarget]
  exact identityECConstraintCoordinates_constraintReplacement _ _

/-- The splice cannot erase any component of the current curvature invisible
to the full sixteen-row EC observation. -/
theorem identityDiracDualECCurvatureKernelPart_constraintReplacementTarget
    (current actionCurvature : PhysicalBivector) :
    identityDiracDualECCurvatureKernelPart
        (identityDiracDualECConstraintReplacementCurvatureTarget
          current actionCurvature) =
      identityDiracDualECCurvatureKernelPart current := by
  unfold identityDiracDualECConstraintReplacementCurvatureTarget
  exact identityDiracDualECCurvatureKernelPart_target _ _

/-- Replacing the four constraint observations can change raw temporal
curvature coordinates, but it preserves the current six-dimensional
electric-kernel responsibility. -/
theorem
    identityDiracDualECTemporalEvolutionKernelPart_constraintReplacementTarget
    (current actionCurvature : PhysicalBivector) :
    identityDiracDualECTemporalEvolutionKernelPart
        (identityECTemporalCurvatureCoordinatesOf
          (identityDiracDualECConstraintReplacementCurvatureTarget
            current actionCurvature)) =
      identityDiracDualECTemporalEvolutionKernelPart
        (identityECTemporalCurvatureCoordinatesOf current) := by
  unfold identityDiracDualECConstraintReplacementCurvatureTarget
  exact identityDiracDualECTemporalEvolutionKernelPart_curvatureTarget _ _

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECConstraintObservationReplacement
