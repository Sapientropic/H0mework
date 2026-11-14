import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.PositiveTimeJointMoments
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers

set_option autoImplicit false

noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.ResolventTimeMoments

open Complex Filter MeasureTheory Set
open scoped Topology

open private monomial_decay_integrable from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.PositiveTimeJointMoments
open private observed_jet from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers

local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation
private abbrev time : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

variable (read : BurnolL2 →L[ℂ] ℂ) (source : BurnolL2)

def profile (coordinate : ℂ) (t : ℝ) : ℂ :=
  read (burnolDirectRightResolventIntegrand (coordinate/2) source t)

def decay (coordinate : ℂ) : ℝ := coordinate.re/2 - 1/4

theorem profile_continuous (coordinate : ℂ) : Continuous (profile read source coordinate) :=
  read.continuous.comp ((positiveMellinQuarterRightResolventWeight_continuous _).smul
    ((burnolMultiplicativeDilation_stronglyContinuous source).comp (by fun_prop)))

theorem profile_norm (coordinate : ℂ) (t : ℝ) :
    ‖profile read source coordinate t‖ ≤ (‖read‖ * ‖source‖) * Real.exp (-decay coordinate*t) := by
  have half_re : (coordinate / 2).re = coordinate.re / 2 := by
    rw [Complex.div_re]
    norm_num
    ring
  rw [profile, burnolDirectRightResolventIntegrand, map_smul, norm_smul,
    norm_positiveMellinQuarterRightResolventWeight, half_re]
  calc
    _ ≤ Real.exp (-decay coordinate*t) * (‖read‖ * ‖D (-t/2) source‖) :=
      mul_le_mul_of_nonneg_left (read.le_opNorm _) (Real.exp_pos _).le
    _ = _ := by rw [(D (-t/2)).norm_map]; ring

private def integrand (degree : ℕ) (coordinate : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ)^degree * profile read source coordinate t

private theorem integrand_cont (degree : ℕ) (coordinate : ℂ) :
    Continuous (integrand read source degree coordinate) := by
  unfold integrand
  exact (continuous_ofReal.pow degree).mul (profile_continuous read source coordinate)

private theorem integrand_norm (degree : ℕ) (coordinate : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖integrand read source degree coordinate t‖ ≤
      (‖read‖*‖source‖) * (t^degree * Real.exp (-decay coordinate*t)) := by
  rw [integrand, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  calc
    _ ≤ t^degree * ((‖read‖*‖source‖)*Real.exp (-decay coordinate*t)) :=
      mul_le_mul_of_nonneg_left (profile_norm read source coordinate t) (pow_nonneg ht degree)
    _ = _ := by ring

private theorem integrand_integrable (degree : ℕ) (coordinate : ℂ) (right : 1/2 < coordinate.re) :
    Integrable (integrand read source degree coordinate) time := by
  have positive : 0 < decay coordinate := by unfold decay; linarith
  refine ((monomial_decay_integrable degree (decay coordinate) positive).const_mul
    (‖read‖*‖source‖)).mono' (integrand_cont read source degree coordinate).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact integrand_norm read source degree coordinate (le_of_lt (show 0 < t from ht))

private theorem integrand_derivative (degree : ℕ) (coordinate : ℂ) (t : ℝ) :
    HasDerivAt (fun z => integrand read source degree z t)
      ((-1/2 : ℂ) * integrand read source (degree+1) coordinate t) coordinate := by
  have affine : HasDerivAt (fun z : ℂ => (1/4 : ℂ) - z/2) (-(1/2 : ℂ)) coordinate :=
    ((hasDerivAt_id' coordinate).div_const (2 : ℂ)).const_sub (1/4)
  have exponent := affine.mul_const (t : ℂ)
  have moved := (Complex.hasDerivAt_exp _).comp coordinate exponent
  have whole := (moved.const_mul ((t:ℂ)^degree)).mul_const (read (D (-t/2) source))
  have exactFunction :
      (fun z => integrand read source degree z t) =
      (fun z : ℂ => (t : ℂ)^degree * Complex.exp (((1/4 : ℂ)-z/2)*(t:ℂ)) *
        read (D (-t/2) source)) := by
    funext z
    simp only [integrand, profile, burnolDirectRightResolventIntegrand, positiveMellinQuarterRightResolventWeight, map_smul, smul_eq_mul, mul_assoc]
  have exactCoefficient :
      (-1/2 : ℂ) * integrand read source (degree+1) coordinate t =
        (t:ℂ)^degree * (Complex.exp (((1/4:ℂ)-coordinate/2)*(t:ℂ)) * (-(1/2:ℂ)*(t:ℂ))) *
          read (D (-t/2) source) := by
    simp only [integrand, profile, burnolDirectRightResolventIntegrand, positiveMellinQuarterRightResolventWeight, map_smul, smul_eq_mul, pow_succ]
    ring
  rw [exactFunction, exactCoefficient]
  exact whole

private def family (degree : ℕ) (coordinate : ℂ) : ℂ :=
  -(∫ t : ℝ, integrand read source degree coordinate t ∂time)

private theorem family_derivative (degree : ℕ) (coordinate : ℂ) (right : 1/2 < coordinate.re) :
    HasDerivAt (family read source degree) ((-1/2 : ℂ) * family read source (degree+1) coordinate) coordinate := by
  let ε := (coordinate.re-1/2)/2
  let C := ‖read‖*‖source‖
  let bound (t : ℝ) := (C/2) * (t^(degree+1)*Real.exp (-(ε/2)*t))
  have ep : 0 < ε := by unfold ε; linarith
  have boundInt : Integrable bound time :=
    (monomial_decay_integrable (degree+1) (ε/2) (half_pos ep)).const_mul _
  have dominated : ∀ᵐ t ∂time, ∀ z ∈ Metric.ball coordinate ε,
      ‖(-1/2 : ℂ) * integrand read source (degree+1) z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have pos : 0 < t := ht
    have closeNorm : ‖z-coordinate‖ < ε := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have close : |(z-coordinate).re| ≤ ε :=
      (Complex.abs_re_le_norm (z-coordinate)).trans closeNorm.le
    have rate : ε/2 ≤ decay z := by
      have lower := (abs_le.mp close).1
      rw [Complex.sub_re] at lower
      dsimp only [ε] at lower
      unfold ε decay
      linarith
    have moved : Real.exp (-decay z*t) ≤ Real.exp (-(ε/2)*t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg rate) pos.le)
    rw [norm_mul, show ‖(-1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num [norm_div]]
    calc
      _ ≤ (1/2 : ℝ) * (C * (t^(degree+1)*Real.exp (-decay z*t))) :=
        mul_le_mul_of_nonneg_left (integrand_norm read source (degree+1) z pos.le) (by norm_num)
      _ ≤ (1/2 : ℝ) * (C * (t^(degree+1)*Real.exp (-(ε/2)*t))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left moved (pow_nonneg pos.le _)) (by unfold C; positivity))
          (by norm_num)
      _ = bound t := by unfold bound; ring
  have performed := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds coordinate ep)
    (Eventually.of_forall fun z => (integrand_cont read source degree z).aestronglyMeasurable)
    (integrand_integrable read source degree coordinate right)
    ((integrand_cont read source (degree+1) coordinate).const_mul _).aestronglyMeasurable
    dominated boundInt
    (Eventually.of_forall fun t z _ => integrand_derivative read source degree z t)).2.neg
  rw [integral_const_mul] at performed
  have negIntegral : family read source degree =
      -(fun z : ℂ => ∫ t : ℝ, integrand read source degree z t ∂time) := rfl
  rw [negIntegral, family, mul_neg]
  exact performed

private theorem source_family (coordinate : ℂ) (right : 1/2 < coordinate.re) :
    read (burnolDirectRightResolvent (coordinate/2) source) = family read source 0 coordinate := by
  have quarter : (1/4 : ℝ) < (coordinate/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  rw [burnolDirectRightResolvent, map_neg, ← read.integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn _ quarter source)]
  simp only [family, integrand, pow_zero, one_mul, profile]

private theorem integral_jets (degree : ℕ) (coordinate : ℂ) (right : 1/2 < coordinate.re) :
    iteratedDeriv degree (fun z => read (burnolDirectRightResolvent (z/2) source)) coordinate =
      (-1/2 : ℂ)^degree * family read source degree coordinate := by
  induction degree generalizing coordinate with
  | zero => simpa only [iteratedDeriv_zero, id_eq, pow_zero, one_mul] using source_family read source coordinate right
  | succ degree ih =>
    rw [iteratedDeriv_succ]
    have openRight : IsOpen {z : ℂ | 1/2 < z.re} := isOpen_Ioi.preimage Complex.continuous_re
    have agree :
        iteratedDeriv degree (fun z => read (burnolDirectRightResolvent (z/2) source)) =ᶠ[𝓝 coordinate]
          fun z => (-1/2 : ℂ)^degree * family read source degree z :=
      (openRight.eventually_mem right).mono (fun z hz => ih z hz)
    rw [agree.deriv_eq]
    exact (((family_derivative read source degree coordinate right).const_mul ((-1/2 : ℂ)^degree)).deriv).trans
      (by rw [pow_succ]; ring)

/-- The moment is the coefficient of the actual source-integrated resolvent and its original power jet. -/
theorem moment_equation (c : BurnolCompletedMellinCoordinate) (degree : ℕ) :
    (-1/2 : ℂ)^degree * (-PositiveTimeJointMoments.moment (profile read source c.value) degree) =
      ((degree.factorial : ℂ)/(2:ℂ)^degree) * read ((R c^(degree+1)) source) :=
  (integral_jets read source degree c.value c.rightHalf).symm.trans
    (by simpa only [smul_eq_mul] using observed_jet read c source degree)

theorem moment_zero (c : BurnolCompletedMellinCoordinate) (degree : ℕ) :
    PositiveTimeJointMoments.moment (profile read source c.value) degree = 0 ↔
      read ((R c^(degree+1)) source) = 0 := by
  have coefficient : ((degree.factorial : ℂ)/(2:ℂ)^degree) ≠ 0 :=
    div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero degree) (pow_ne_zero _ (by norm_num))
  have leading : (-1/2 : ℂ)^degree ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · intro zero
    have actual := moment_equation read source c degree
    rw [zero, neg_zero, mul_zero] at actual
    exact (mul_eq_zero.mp actual.symm).resolve_left coefficient
  · intro zero
    have actual := moment_equation read source c degree
    rw [zero, mul_zero] at actual
    exact neg_eq_zero.mp ((mul_eq_zero.mp actual).resolve_left leading)

end OriginalRSourceJointContact.OutsideHistory.ResolventTimeMoments
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
