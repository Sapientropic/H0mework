import H0mework.NavierStokes.WindowSchurMean.Forcing
import H0mework.NavierStokes.UnheatedWriterHalf.InverseQuarter
import H0mework.NavierStokes.WindowEnergyTraceCoupled.CoupledBound

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanForcingTest
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeResolventCompactness NativeWholeResolvent NativePhysicalPairing NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeEndpointVelocityCarrier
open NativeWindowHistoryMeanForcing (test)
noncomputable section
variable {nu : Viscosity}

private theorem decode_restore (data : State) (k : IntegerWavevector) (nonzero : k≠0) (i : Coordinate) :
    NativeUnheatedTriadRows.decode k i (NativeUnheatedInverseQuarter.inverseQuarter data)=
      NativeUnheatedHalfNonlinear.decode k i data := by
  rw [NativeUnheatedTriadRows.decode_apply,NativeUnheatedInverseQuarter.whole_row,Pi.smul_apply,smul_smul]
  have restored : NativeUnheatedPairNegativeKernel.root k*(NativeUnheatedHalfNonlinear.quarter k)⁻¹=
      NativeUnheatedHalfNonlinear.quarter k := by
    rw [← NativeUnheatedHalfNonlinear.quarter_sq,pow_two,mul_assoc,
      mul_inv_cancel₀ (NativeUnheatedInverseQuarter.quarter_positive k nonzero).ne',mul_one]
  rw [restored]
  rfl

theorem test_lift (M : ℕ) (v : physicalSpace (modes M)) (data : State) : test M v data=
    pairing (modes M) (NativeWindowStageNineSource.lift (modes M) (NativeUnheatedInverseQuarter.inverseQuarter data)) v := by
  rw [NativeWindowHistoryMeanForcing.test_apply,NativeWindowStageNineSource.lift_pairing]
  apply Finset.sum_congr rfl
  intro k member
  apply Finset.sum_congr rfl
  intro i _
  rw [decode_restore data k (fun zero => modes_zero M (zero ▸ member)) i]

theorem test_bound (M : ℕ) (v : physicalSpace (modes M)) :
    ‖test M v‖≤Real.sqrt (curlPair (modes M) v.1 v.1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro data
  rw [Real.norm_eq_abs,test_lift]
  exact (NativeWindowTraceCoupled.input_pairing_bound M (NativeUnheatedInverseQuarter.inverseQuarter data) v).trans
    ((mul_le_mul_of_nonneg_right (NativeUnheatedInverseQuarter.inverseQuarter_bound data) (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _))

theorem source_effect_small (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∀ M≥low,∀ time∈Icc 0 horizon,∀ v : physicalSpace (modes M),
      |inner ℝ (NativeWindowTraceWholeHistory.constant (includeCLM (modes M) (modes_closed M) v))
        (NativeWindowHistoryOseen.forcingHistory seed M time)|≤epsilon*Real.sqrt (curlPair (modes M) v.1 v.1) := by
  obtain ⟨low,paid⟩:=NativeWindowHistoryMeanForcing.source_effect_small seed horizon nonnegative epsilon positive
  exact ⟨low,fun M above time inside v => (paid M above time inside v).trans
    (mul_le_mul_of_nonneg_left (test_bound M v) positive.le)⟩

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanForcingTest
