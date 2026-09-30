import H0mework.NavierStokes.NativeWorkWhole.RestartBlockKineticLedger
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinPositiveTimeSuffix

/-! The original whole receipt pays a terminal-to-mean mass rectangle.
Its arbitrary-time growth estimate consumes the same receipt's suffix and
the already proved whole nonlinear/viscous balance. -/

set_option autoImplicit false

open scoped ENNReal

namespace SaturationMonoid.NavierStokes.WholeWindowMass

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinPositiveTimeSuffix
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open GeneratedInfiniteWholeRestartEndpointMacroLineage
open FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance

noncomputable section

def growthCoefficient (nu : Viscosity) : Real :=
  (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))

theorem receipt_mass_growth_from_any_time
    {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration ceiling : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (massBound : ∀ᵐ time ∂(commonTimeMeasure duration),
      wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling)
    (start : Icc (0 : Real) duration) :
    nu.coeff * (wholeVorticityEuclideanMass
        (receipt.wholePath ⟨duration, receipt.requestedTimePos.le, le_rfl⟩) -
      wholeVorticityEuclideanMass (receipt.wholePath start)) ≤
      growthCoefficient nu * (ceiling ^ 3 * (duration - start.1)) := by
  rcases lt_or_eq_of_le start.2.2 with startLt | startEq
  · let suffix := positiveTimeSuffixWholeContinuousMildSerrinReceipt
      receipt start.1 start.2.1 startLt
    have bound : ∀ᵐ time ∂(commonTimeMeasure (duration - start.1)),
        wholeVorticityEuclideanMass (suffix.wholePath time) ≤ ceiling := by
      have restricted := ae_restrict_of_ae
        (s := Set.range (commonTimeShift start.2.1 startLt.le)) massBound
      have shifted := (commonTimeShift_measurePreserving start.2.1 startLt.le
        ).quasiMeasurePreserving.ae restricted
      exact shifted
    have signed := receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime suffix bound
    have tangentNonneg : 0 ≤ puncturedEuclideanSpaceTimeSquare suffix.wholeTangent := by
      unfold puncturedEuclideanSpaceTimeSquare
      positivity
    have viscousNonneg : 0 ≤ puncturedEuclideanSpaceTimeSquare
        (receiptViscousNegativeOneState suffix) := by
      unfold puncturedEuclideanSpaceTimeSquare
      positivity
    have terminalEq : suffix.wholePath
        ⟨duration - start.1, suffix.requestedTimePos.le, le_rfl⟩ =
        receipt.wholePath ⟨duration, receipt.requestedTimePos.le, le_rfl⟩ := by
      change receipt.wholePath
        (commonTimeShift start.2.1 startLt.le
          ⟨duration - start.1, suffix.requestedTimePos.le, le_rfl⟩) = _
      congr 1
      apply Subtype.ext
      change start.1 + (duration - start.1) = duration
      ring
    have initialEq : receipt.wholePath
        (wholeContinuousMildSerrinSuffixStartTime receipt start.1 start.2.1 startLt) =
        receipt.wholePath start := rfl
    have boundary := (le_add_of_nonneg_left
      (add_nonneg tangentNonneg
        (mul_nonneg (by norm_num : (0 : Real) ≤ 1 / 2) viscousNonneg))).trans signed
    simpa only [terminalEq, initialEq, growthCoefficient] using boundary
  · have pointEq : start = ⟨duration, receipt.requestedTimePos.le, le_rfl⟩ :=
      Subtype.ext startEq
    rw [pointEq]
    simp

private theorem commonTimeMeasure_real_univ (duration : Real) (durationPos : 0 < duration) :
    (commonTimeMeasure duration).real Set.univ = duration := by
  let terminal : Icc (0 : Real) duration := ⟨duration, durationPos.le, le_rfl⟩
  have generated :=
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation.commonTimeMeasure_Iic_real
      duration durationPos.le terminal
  have terminalIic : Iic terminal = Set.univ := by
    ext time
    simp only [mem_Iic, mem_univ, iff_true]
    exact time.2.2
  simpa only [terminalIic, Measure.restrict_univ] using generated

theorem receipt_terminal_mass_rectangle
    {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration ceiling : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (ceilingNonneg : 0 ≤ ceiling)
    (massBound : ∀ᵐ time ∂(commonTimeMeasure duration),
      wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    duration * (wholeVorticityEuclideanMass
        (receipt.wholePath ⟨duration, receipt.requestedTimePos.le, le_rfl⟩) -
      growthCoefficient nu * (ceiling ^ 3 * duration) / nu.coeff) ≤
      wholeSpaceTimeEuclideanMass duration receipt.stateLimit := by
  let mass := fun time => wholeVorticityEuclideanMass (receipt.wholePath time)
  let terminal : Icc (0 : Real) duration :=
    ⟨duration, receipt.requestedTimePos.le, le_rfl⟩
  have growthNonneg : 0 ≤ growthCoefficient nu := by
    unfold growthCoefficient
    positivity
  have pointwise : ∀ start : Icc (0 : Real) duration,
      mass terminal - growthCoefficient nu * (ceiling ^ 3 * duration) / nu.coeff ≤
        mass start := by
    intro start
    have generated := receipt_mass_growth_from_any_time receipt massBound start
    have growthLe : growthCoefficient nu * (ceiling ^ 3 * (duration - start.1)) ≤
        growthCoefficient nu * (ceiling ^ 3 * duration) := by
      gcongr
      exact sub_le_self _ start.2.1
    have difference : mass terminal - mass start ≤
        growthCoefficient nu * (ceiling ^ 3 * duration) / nu.coeff :=
      (le_div_iff₀ nu.coeff_pos).2 (by
        dsimp only [mass, terminal]
        nlinarith [generated.trans growthLe])
    dsimp only [mass, terminal]
    linarith
  have massIntegrable : Integrable mass (commonTimeMeasure duration) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (wholeReceiptVorticityMass_continuous receipt).continuousOn)
  have integrated := integral_mono_ae (integrable_const
      (mass terminal - growthCoefficient nu * (ceiling ^ 3 * duration) / nu.coeff))
    massIntegrable (Filter.Eventually.of_forall pointwise)
  rw [integral_const, commonTimeMeasure_real_univ duration receipt.requestedTimePos,
    smul_eq_mul] at integrated
  have pathAE := BoundedContinuousFunction.coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure duration) ℂ receipt.wholePath
  rw [receipt.wholePath_toLp_eq_stateLimit] at pathAE
  rw [wholeSpaceTimeEuclideanMass_eq_integral]
  refine integrated.trans_eq (integral_congr_ae ?_)
  filter_upwards [pathAE] with time same
  exact congrArg wholeVorticityEuclideanMass same.symm

end
end SaturationMonoid.NavierStokes.WholeWindowMass
