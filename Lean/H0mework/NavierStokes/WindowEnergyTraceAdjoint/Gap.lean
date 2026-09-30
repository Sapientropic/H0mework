import H0mework.NavierStokes.WindowEnergyTraceAdjoint.Time
import H0mework.NavierStokes.WindowHistory.Current

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceAdjointGap
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceAdjoint (backward backward_terminal backward_energy_derivative backward_continuous)
noncomputable section
variable {nu : Viscosity}

def gap (nu : Viscosity) : ℝ := nu.coeff*(2*Real.pi)^2

theorem gap_positive (nu : Viscosity) : 0<gap nu := by unfold gap; positivity [nu.coeff_pos]

theorem spectral_gap (M : Finset IntegerWavevector) (zero : 0∉M) (v : physicalSpace M) :
    (2*Real.pi)^2*‖coefficients M v‖^2≤curlPair M v.1 v.1 := by
  have mass : ‖coefficients M v‖^2=pairing M v v := (real_inner_self_eq_norm_sq (coefficients M v)).symm
  rw [mass,pairing_eq,Finset.mul_sum,curlPair]
  apply Finset.sum_le_sum
  intro k inside
  have nonzero : k≠0 := fun same => zero (same ▸ inside)
  rw [← curl_pair_row k nonzero _ _ (physical_transverse v k inside) (physical_transverse v k inside)]
  have positive : 0≤complexCoordinateRealInner (v.1 k) (v.1 k) := by
    rw [complexCoordinateRealInner_self]
    exact complexCoordinateVectorNormSq_nonneg _
  apply mul_le_mul_of_nonneg_right _ positive
  have scale := mul_le_mul_of_nonneg_left (one_le_integerWaveNormSq k nonzero) (sq_nonneg (2*Real.pi))
  simpa only [integerWaveViscousMultiplier,mul_one] using scale

theorem weighted_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) (time : ℝ) (inside : time∈Icc start finish) :
    HasDerivWithinAt (fun t => Real.exp (2*gap nu*(finish-t))*‖coefficients (modes M) (backward seed M start finish ordered terminal t)‖^2)
      (Real.exp (2*gap nu*(finish-time))*(2*nu.coeff*curlPair (modes M)
        (backward seed M start finish ordered terminal time).1 (backward seed M start finish ordered terminal time).1-
          2*gap nu*‖coefficients (modes M) (backward seed M start finish ordered terminal time)‖^2)) (Icc start finish) time := by
  have linear : HasDerivAt (fun t : ℝ => 2*gap nu*(finish-t)) (-2*gap nu) time := by
    convert! (((hasDerivAt_const time finish).sub (hasDerivAt_id time)).const_mul (2*gap nu)) using 1
    ring
  have source := linear.exp.hasDerivWithinAt.mul (backward_energy_derivative seed M start finish ordered terminal time inside)
  convert! source using 1
  ring

theorem weighted_energy_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) (time : ℝ) (inside : time∈Icc start finish) :
    Real.exp (2*gap nu*(finish-time))*‖coefficients (modes M) (backward seed M start finish ordered terminal time)‖^2≤
      ‖coefficients (modes M) terminal‖^2 := by
  let curve:=backward seed M start finish ordered terminal
  let E:=fun t => Real.exp (2*gap nu*(finish-t))*‖coefficients (modes M) (curve t)‖^2
  have continuous : ContinuousOn E (Icc start finish) :=
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn).mul
      ((((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
        (backward_continuous seed M start finish ordered terminal)).norm.pow 2))
  have mono : MonotoneOn E (Icc start finish) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc start finish) continuous
    · intro t ht
      rw [interior_Icc] at ht
      exact ((weighted_derivative seed M start finish ordered terminal t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [((weighted_derivative seed M start finish ordered terminal t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).deriv]
      apply mul_nonneg (Real.exp_pos _).le
      have paid := mul_le_mul_of_nonneg_left (spectral_gap (modes M) (modes_zero M) (curve t))
        (show 0≤2*nu.coeff from by positivity [nu.coeff_pos])
      dsimp only [gap]
      nlinarith only [paid]
  have bound := mono inside (right_mem_Icc.mpr ordered) inside.2
  simpa only [E,curve,backward_terminal,sub_self,mul_zero,Real.exp_zero,one_mul] using bound

theorem backward_mass_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) (time : ℝ) (inside : time∈Icc start finish) :
    ‖coefficients (modes M) (backward seed M start finish ordered terminal time)‖≤
      Real.exp (-gap nu*(finish-time))*‖coefficients (modes M) terminal‖ := by
  have weighted := weighted_energy_bound seed M start finish ordered terminal time inside
  have cancel : Real.exp (2*gap nu*(finish-time))*Real.exp (-gap nu*(finish-time))^2=1 := by
    rw [pow_two,← mul_assoc,← Real.exp_add,← Real.exp_add]
    rw [show 2*gap nu*(finish-time)+(-gap nu*(finish-time))+(-gap nu*(finish-time))=0 by ring,Real.exp_zero]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (2*gap nu*(finish-time)))).mp
  rw [mul_pow]
  rw [← mul_assoc (Real.exp (2*gap nu*(finish-time))) (Real.exp (-gap nu*(finish-time))^2),cancel,one_mul]
  exact weighted

def factor (nu : Viscosity) : ℝ := Real.exp (-gap nu)

theorem factor_positive (nu : Viscosity) : 0<factor nu := Real.exp_pos _

theorem factor_lt_one (nu : Viscosity) : factor nu<1 := by
  rw [factor,← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (neg_neg_of_pos (gap_positive nu))

theorem sample_contraction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation sample : ℝ)
    (sampled : sample∈Icc (observation+1) (observation+2)) (terminal : physicalSpace (modes M)) :
    ‖coefficients (modes M) (backward seed M observation sample (by linarith [sampled.1]) terminal observation)‖≤
      factor nu*‖coefficients (modes M) terminal‖ := by
  have original := backward_mass_bound seed M observation sample (by linarith [sampled.1]) terminal observation
    (left_mem_Icc.mpr (by linarith [sampled.1]))
  apply original.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have paid := mul_le_mul_of_nonneg_left (show 1 ≤ sample-observation by linarith [sampled.1]) (gap_positive nu).le
  linarith only [paid]

theorem average_contraction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ) :
    ∀ᵐ shift : ℝ ∂NativeForwardWindowPairingReadout.averageMeasure,∃ ordered : observation≤observation-shift,
      ∀ terminal : physicalSpace (modes M),
        ‖coefficients (modes M) (backward seed M observation (observation-shift) ordered terminal observation)‖≤
          factor nu*‖coefficients (modes M) terminal‖ := by
  filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
  have ordered : observation≤observation-shift := by linarith
  refine ⟨ordered,fun terminal => ?_⟩
  have original := backward_mass_bound seed M observation (observation-shift) ordered terminal observation (left_mem_Icc.mpr ordered)
  apply original.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have paid := mul_le_mul_of_nonneg_left (show 1 ≤ observation-shift-observation by linarith) (gap_positive nu).le
  linarith only [paid]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceAdjointGap
