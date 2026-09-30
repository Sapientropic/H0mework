import H0mework.Versions.Y.Arithmetic.MellinProjection.Canonical
import H0mework.Versions.Y.Arithmetic.RieszCanonicalRaw.EvenProjectionCanonicalRaw

/-! The original mean-zero forcing and resolvent equation generate the canonical source traces. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
noncomputable section

def burnolRieszFourierForcingRaw
    (coordinate : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  burnolPositionMeanZeroRaw
    (fourierL2 (burnolAmbientCompletedMellinKernelFormula coordinate))
    (burnolGapTailFourierRaw (1 / 4 : ℝ) coordinate)

theorem burnolRieszFourierForcing_ae_raw
    (coordinate : BurnolCompletedMellinCoordinate) :
    ((burnolAmbientMeanZeroFourier
        (burnolAmbientCompletedMellinKernelFormula coordinate) :
          BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))]
        burnolRieszFourierForcingRaw coordinate := by
  have source := burnolPositionMeanZero_ae_raw
    (fourierL2 (burnolAmbientCompletedMellinKernelFormula coordinate))
    (burnolGapTailFourierRaw (1 / 4 : ℝ) coordinate)
    (burnolGapTailFourier_ae_canonical (1 / 4 : ℝ) (by norm_num) coordinate)
  change (burnolQuarterMeanZeroProjection
    (burnolQuarterRestriction (burnolAmbientEvenPart (fourierL2 _))) : ℝ → ℂ) =ᵐ[_] _ at source
  rw [← fourierL2_burnolAmbientEvenPart] at source
  exact source

theorem burnolRieszFourierForcingRaw_continuousAt
    (coordinate : BurnolCompletedMellinCoordinate) {frequency : ℝ}
    (nonzero : frequency ≠ 0) :
    ContinuousAt (burnolRieszFourierForcingRaw coordinate) frequency := by
  have direct := burnolGapTailFourierRaw_continuousAt (1 / 4 : ℝ)
    (by norm_num) coordinate nonzero
  have reflected := (burnolGapTailFourierRaw_continuousAt (1 / 4 : ℝ)
    (by norm_num) coordinate (neg_ne_zero.mpr nonzero)).comp
      continuous_neg.continuousAt
  exact (continuousAt_const.mul (direct.add reflected)).sub continuousAt_const

def burnolRieszSingleFourierSourceRaw
    (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) : ℂ :=
  burnolRieszFourierForcingRaw coordinate frequency +
    burnolMeanZeroFourierRaw
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) frequency

theorem burnolRieszSingleFourierSource_ae_raw
    (coordinate : BurnolCompletedMellinCoordinate) :
    ((burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
        ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))]
      burnolRieszSingleFourierSourceRaw coordinate := by
  have equation := burnolRieszSingleFourierSource_equation coordinate
  change burnolRieszSingleFourierSource coordinate -
    burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) = _ at equation
  have solved := congrArg
    (fun state : BurnolQuarterMeanZeroCarrier => (state : BurnolQuarterIntervalL2))
    (eq_add_of_sub_eq equation)
  change (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
    (burnolAmbientMeanZeroFourier
      (burnolAmbientCompletedMellinKernelFormula coordinate) : BurnolQuarterIntervalL2) +
    (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) :
        BurnolQuarterIntervalL2) at solved
  rw [solved]
  filter_upwards [Lp.coeFn_add
    (burnolAmbientMeanZeroFourier
      (burnolAmbientCompletedMellinKernelFormula coordinate) : BurnolQuarterIntervalL2)
    (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) :
        BurnolQuarterIntervalL2),
    burnolRieszFourierForcing_ae_raw coordinate,
    burnolMeanZeroFourier_ae_raw
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))]
      with x added forcing returned
  rw [added]
  change (burnolAmbientMeanZeroFourier
      (burnolAmbientCompletedMellinKernelFormula coordinate) : BurnolQuarterIntervalL2) x +
    (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) :
        BurnolQuarterIntervalL2) x = _
  rw [forcing, returned]
  rfl

theorem burnolRieszSingleFourierSourceRaw_continuousAt
    (coordinate : BurnolCompletedMellinCoordinate) {frequency : ℝ}
    (nonzero : frequency ≠ 0) :
    ContinuousAt (burnolRieszSingleFourierSourceRaw coordinate) frequency :=
  (burnolRieszFourierForcingRaw_continuousAt coordinate nonzero).add
    ((burnolRadiusTruncatedFourierRaw_continuous
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
        BurnolQuarterIntervalL2)).continuousAt.sub continuousAt_const)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
