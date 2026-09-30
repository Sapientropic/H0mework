import H0mework.Versions.X.NavierStokes.WindowEnergyTraceInverse.Control
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineFullMatrixPotential

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeDistributedLyapunov
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeResolventAdjoint NativeCommonAdvectorAction NativeWholeH1Mixed
open NativeWindowOperatorGreen
open NativeWindowStressOseenTest (duality)
open NativeWindowTraceDualEvolution (mass lifted energy lyapunov)
noncomputable section
variable {nu : Viscosity}

def potential (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :=
  NativeWindowMetricGraphPotential.potential (modes M) F
    (NativeWindowTraceOperator.field seed time F radius)

theorem source_lifted_control (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∀ radius ≥ low, ∀ outerRadius M, ∀ time ∈ Icc 0 horizon,
      ∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := lifted seed M F radius time w
      ‖coefficients (modes M) z‖ ^ 2 ≤ energy seed M F radius time w := by
  obtain ⟨low,C,C0,source⟩ :=
    NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M time inside w => ?_⟩
  have paid := (source radius above outerRadius M time inside).2 w |>.2.1
  let z := lifted seed M (integerWaveFrequencyCube outerRadius) radius time w
  have curl0 : 0 ≤ curlPair (modes M) z.1 z.1 := by
    unfold curlPair
    simp only [complexCoordinateRealInner_self]
    exact Finset.sum_nonneg fun _ _ => complexCoordinateVectorNormSq_nonneg _
  have positive := nu.coeff_pos
  change ‖coefficients (modes M) z‖ ^ 2 ≤ _
  have normed : pairing (modes M) z z = ‖coefficients (modes M) z‖ ^ 2 := by
    change inner ℝ (coefficients (modes M) z) (coefficients (modes M) z) = _
    exact real_inner_self_eq_norm_sq _
  rw [normed] at paid
  nlinarith only [paid,curl0,positive]

theorem mass_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (z : physicalSpace (modes M)) :
    mass seed M F radius time z = z + nu.coeff •
      laplacian (modes M) (modes_zero M) (modes_closed M) nu z +
        potential seed M F radius time z := by
  apply (duality (modes M)).injective
  apply LinearMap.ext
  intro x
  change pairing (modes M) (mass seed M F radius time z) x =
    pairing (modes M) (z + nu.coeff •
      laplacian (modes M) (modes_zero M) (modes_closed M) nu z +
        potential seed M F radius time z) x
  rw [pairing_symmetric]
  change pairing (modes M) x
    (NativeWindowTraceOperator.test seed time (modes M) (modes M) F radius z) = _
  rw [NativeWindowTraceOperator.test_pairing,
    pairing_symmetric (modes M) (z + nu.coeff •
      laplacian (modes M) (modes_zero M) (modes_closed M) nu z +
        potential seed M F radius time z) x]
  simp only [NativeWindowTraceOperator.form, LinearMap.add_apply,
    NativeWindowTraceOperatorAction.spectral_laplacian _ (modes_zero M) (modes_closed M),
    map_add,map_smul,smul_eq_mul,potential,
    NativeWindowMetricGraphPotential.potential_pairing,
    NativeWindowTraceOperator.matrixForm,LinearMap.mk₂_apply,
    NativeWindowTraceOperator.read,ContinuousLinearMap.comp_apply,innerSL_apply_apply]

theorem source_potential_relative (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ∀ time ∈ Icc 0 horizon, ∀ z : physicalSpace (modes M),
      ‖coefficients (modes M)
        (potential seed M (integerWaveFrequencyCube outerRadius) radius time z)‖ ≤
      epsilon * ‖coefficients (modes M)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)‖ +
          C * ‖coefficients (modes M) z‖ := by
  obtain ⟨low,B,B0,source⟩ :=
    NativeStageNineFullMatrixPotential.source_field_bound seed horizon nonnegative
  obtain ⟨C,C0,paid⟩ :=
    NativeWindowMetricGraphPotential.exists_potential_bound nu (3*B) (by positivity)
      epsilon positive
  refine ⟨low,C,C0,fun radius above outerRadius M time inside z => ?_⟩
  apply paid (modes M) (integerWaveFrequencyCube outerRadius) (modes_zero M)
    (modes_closed M) (NativeWindowFiniteGramFourier.cube_closed outerRadius)
    (NativeWindowTraceOperator.field seed time (integerWaveFrequencyCube outerRadius) radius) _ z
  unfold NativeWindowTraceOperator.field
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ =>
    source radius above outerRadius time inside i i).trans_eq (by simp))

theorem source_heat_dissipation (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ∀ time ∈ Icc 0 horizon, ∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := lifted seed M F radius time w
      let L := laplacian (modes M) (modes_zero M) (modes_closed M) nu z;
      -2*nu.coeff*pairing (modes M) (mass seed M F radius time z) L ≤
        -nu.coeff^2*‖coefficients (modes M) L‖^2 + C*energy seed M F radius time w := by
  obtain ⟨first,C,C0,source⟩ := source_potential_relative seed horizon nonnegative
    (nu.coeff/4) (by positivity [nu.coeff_pos])
  obtain ⟨last,controlled⟩ := source_lifted_control seed horizon nonnegative
  refine ⟨max first last,2*C^2,by positivity,
    fun radius above outerRadius M time inside w => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let z := lifted seed M F radius time w
  let L := laplacian (modes M) (modes_zero M) (modes_closed M) nu z
  let P := potential seed M F radius time z
  let d := ‖coefficients (modes M) L‖
  let m := ‖coefficients (modes M) z‖
  have paid := source radius ((le_max_left first last).trans above)
    outerRadius M time inside z
  have pairBound : |pairing (modes M) P L| ≤ (nu.coeff/4*d+C*m)*d :=
    (abs_real_inner_le_norm (coefficients (modes M) P) (coefficients (modes M) L)).trans
      (mul_le_mul_of_nonneg_right paid (norm_nonneg _))
  have same : pairing (modes M) (mass seed M F radius time z) L =
      curlPair (modes M) z.1 z.1 + nu.coeff*d^2 + pairing (modes M) P L := by
    rw [mass_split]
    simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [laplacian_pairing]
    have normed : pairing (modes M) L L = d^2 := by
      change inner ℝ (coefficients (modes M) L) (coefficients (modes M) L) = _
      exact real_inner_self_eq_norm_sq _
    rw [normed]
  have curl0 : 0 ≤ curlPair (modes M) z.1 z.1 := by
    unfold curlPair
    simp only [complexCoordinateRealInner_self]
    exact Finset.sum_nonneg fun _ _ => complexCoordinateVectorNormSq_nonneg _
  have lower : nu.coeff*d^2-(nu.coeff/4*d+C*m)*d ≤
      pairing (modes M) (mass seed M F radius time z) L := by
    have signed := neg_abs_le (pairing (modes M) P L)
    linarith only [same,pairBound,signed,curl0]
  have scaled := mul_le_mul_of_nonneg_left lower nu.coeff_pos.le
  have heat : -2*nu.coeff*pairing (modes M) (mass seed M F radius time z) L ≤
      -nu.coeff^2*d^2+2*C^2*m^2 := by
    nlinarith only [scaled,sq_nonneg (nu.coeff*d-2*C*m)]
  have massPaid := mul_le_mul_of_nonneg_left
    (controlled radius ((le_max_right first last).trans above) outerRadius M time inside w)
    (show 0 ≤ 2*C^2 by positivity)
  dsimp only [F,z,L,d,m] at heat massPaid ⊢
  linarith only [heat,massPaid]

def convectionWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (z : physicalSpace (modes M)) : ℝ :=
  2*pairing (modes M) (mass seed M F radius time z)
    (convection (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time)
      (NativeWindowTraceAdjoint.advector_reality seed M time) z)

theorem forward_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (z : physicalSpace (modes M)) :
    NativeWindowTraceAdjoint.forward seed M time z =
      (-nu.coeff) • laplacian (modes M) (modes_zero M) (modes_closed M) nu z +
        convection (modes M) (modes_zero M) (modes_closed M) nu
          (NativeWindowTraceAdjoint.advector seed M time)
          (NativeWindowTraceAdjoint.advector_reality seed M time) z := by
  have original := congrArg (fun T : Module.End ℝ (physicalSpace (modes M)) => T z)
    (operator_split (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time)
      (NativeWindowTraceAdjoint.advector_reality seed M time))
  exact original

theorem lyapunov_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (z : physicalSpace (modes M)) :
    lyapunov seed M F radius time z =
      -2*nu.coeff*pairing (modes M) (mass seed M F radius time z)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu z) +
        convectionWork seed M F radius time z := by
  rw [NativeWindowTraceDualEvolution.lyapunov,
    NativeWindowTraceDualEvolution.mass_symmetric seed M F radius time z
      (NativeWindowTraceAdjoint.forward seed M time z)]
  rw [pairing_symmetric (modes M) (NativeWindowTraceAdjoint.forward seed M time z)]
  rw [forward_split]
  simp only [map_add,map_smul,smul_eq_mul,convectionWork]
  ring

theorem convectionWork_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (z : physicalSpace (modes M)) :
    let K := convection (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time)
      (NativeWindowTraceAdjoint.advector_reality seed M time)
    convectionWork seed M F radius time z =
      2*nu.coeff*pairing (modes M)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu z) (K z) +
        2*pairing (modes M) (potential seed M F radius time z) (K z) := by
  intro K
  have skew := convection_skew (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M time)
    (NativeWindowTraceAdjoint.advector_reality seed M time) z z
  rw [pairing_symmetric (modes M) (K z) z] at skew
  have zero : pairing (modes M) z (K z) = 0 := by linarith only [skew]
  unfold convectionWork
  rw [mass_split]
  simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
  change 2*(pairing (modes M) z (K z) +
    nu.coeff*pairing (modes M)
      (laplacian (modes M) (modes_zero M) (modes_closed M) nu z) (K z) +
    pairing (modes M) (potential seed M F radius time z) (K z)) = _
  rw [zero]
  ring

theorem source_lyapunov_gate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ∀ time ∈ Icc 0 horizon, ∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := lifted seed M F radius time w
      lyapunov seed M F radius time z ≤
        -nu.coeff^2*‖coefficients (modes M)
          (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)‖^2 +
        C*energy seed M F radius time w + convectionWork seed M F radius time z := by
  obtain ⟨low,C,C0,source⟩ := source_heat_dissipation seed horizon nonnegative
  refine ⟨low,C,C0,fun radius above outerRadius M time inside w => ?_⟩
  dsimp only
  rw [lyapunov_split]
  exact add_le_add_left (source radius above outerRadius M time inside w) _

end
end SaturationMonoid.NavierStokes.NativeDistributedLyapunov
