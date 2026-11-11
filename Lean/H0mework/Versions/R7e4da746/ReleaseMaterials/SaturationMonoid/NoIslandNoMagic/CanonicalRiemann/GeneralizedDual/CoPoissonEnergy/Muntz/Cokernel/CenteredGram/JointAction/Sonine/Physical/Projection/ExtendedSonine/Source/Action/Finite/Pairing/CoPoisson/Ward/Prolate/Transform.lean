import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prolate.Kernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prolate.Return
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ProlateTransform
open Complex Filter MeasureTheory Set ProlateKernel
open scoped ContDiff Topology
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

private theorem sine_norm (x y : ℝ) :
    ‖Complex.sin (frequency * (x : ℂ) * (y : ℂ))‖ ≤ 1 := by
  have realArgument : frequency * (x : ℂ) * (y : ℂ) = ((2 * Real.pi * x * y : ℝ) : ℂ) := by
    simp [frequency]
  rw [realArgument, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

private theorem cosine_norm (x y : ℝ) : ‖kernel x y‖ ≤ 1 := by
  have realArgument : frequency * (x : ℂ) * (y : ℂ) = ((2 * Real.pi * x * y : ℝ) : ℂ) := by
    simp [frequency]
  rw [kernel, realArgument, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

def transform (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y : ℝ, kernel x y * f y ∂μq

private theorem first_integral (f : ℝ → ℂ) (hf : Continuous f) (x : ℝ) :
    HasDerivAt (transform f) (∫ y : ℝ,
      (-frequency * (y : ℂ) * Complex.sin (frequency * (x : ℂ) * (y : ℂ))) * f y ∂μq) x := by
  let F := fun x y : ℝ => kernel x y * f y
  let D := fun x y : ℝ => (-frequency * (y : ℂ) * Complex.sin (frequency * (x : ℂ) * (y : ℂ))) * f y
  have raw (x : ℝ) : Continuous (F x) := by dsimp only [F, kernel]; fun_prop
  have derived (x : ℝ) : Continuous (D x) := by dsimp only [D]; fun_prop
  have majorant : Integrable (fun y : ℝ => (2 * Real.pi * q) * ‖f y‖) μq :=
    (hf.norm.integrableOn_Icc).const_mul _
  have source := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (s := Set.univ) (bound := fun y => (2 * Real.pi * q) * ‖f y‖)
    (Filter.univ_mem : (Set.univ : Set ℝ) ∈ 𝓝 x)
    (Eventually.of_forall fun t => (raw t).aestronglyMeasurable) (raw x).integrableOn_Icc
    (derived x).aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y hy
      intro t _
      have yq : |y| ≤ q := abs_le.mpr hy
      dsimp only [D]
      simp only [norm_mul, norm_neg, frequency, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      calc
        _ ≤ (2 * Real.pi * q * 1) * ‖f y‖ := by
          gcongr
          exact sine_norm t y
        _ = _ := by ring)
    majorant (by
      filter_upwards with y
      intro t _
      exact (kernel_hasDerivAt t y).mul_const (f y))
  exact source.2

private theorem second_integral (f : ℝ → ℂ) (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y : ℝ,
      (-frequency * (y : ℂ) * Complex.sin (frequency * (t : ℂ) * (y : ℂ))) * f y ∂μq)
      (∫ y : ℝ, (-(frequency ^ 2) * (y : ℂ) ^ 2 * kernel x y) * f y ∂μq) x := by
  let F := fun x y : ℝ => (-frequency * (y : ℂ) * Complex.sin (frequency * (x : ℂ) * (y : ℂ))) * f y
  let D := fun x y : ℝ => (-(frequency ^ 2) * (y : ℂ) ^ 2 * kernel x y) * f y
  have raw (x : ℝ) : Continuous (F x) := by dsimp only [F]; fun_prop
  have derived (x : ℝ) : Continuous (D x) := by dsimp only [D, kernel]; fun_prop
  have majorant : Integrable (fun y : ℝ => ((2 * Real.pi) ^ 2 * q ^ 2) * ‖f y‖) μq :=
    (hf.norm.integrableOn_Icc).const_mul _
  have source := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (s := Set.univ) (bound := fun y => ((2 * Real.pi) ^ 2 * q ^ 2) * ‖f y‖)
    (Filter.univ_mem : (Set.univ : Set ℝ) ∈ 𝓝 x)
    (Eventually.of_forall fun t => (raw t).aestronglyMeasurable) (raw x).integrableOn_Icc
    (derived x).aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y hy
      intro t _
      have yq : |y| ≤ q := abs_le.mpr hy
      dsimp only [D]
      simp only [norm_mul, norm_neg, norm_pow, frequency, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      calc
        _ ≤ ((2 * Real.pi) ^ 2 * q ^ 2 * 1) * ‖f y‖ := by
          gcongr
          exact cosine_norm t y
        _ = _ := by ring)
    majorant (by
      filter_upwards with y
      intro t _
      exact (kernel_second_hasDerivAt t y).mul_const (f y))
  exact source.2

theorem original_action_integral (f : ℝ → ℂ) (hf : Continuous f) (x : ℝ) :
    act (transform f) x = ∫ y : ℝ, act (fun t => kernel t y) x * f y ∂μq := by
  have first : deriv (transform f) = fun t : ℝ => ∫ y : ℝ,
      (-frequency * (y : ℂ) * Complex.sin (frequency * (t : ℂ) * (y : ℂ))) * f y ∂μq := by
    funext t
    exact (first_integral f hf t).deriv
  have second : deriv (deriv (transform f)) x =
      ∫ y : ℝ, (-(frequency ^ 2) * (y : ℂ) ^ 2 * kernel x y) * f y ∂μq := by
    rw [first]
    exact (second_integral f hf x).deriv
  unfold act
  rw [second, first]
  dsimp only
  simp_rw [kernel_second, kernel_deriv]
  have f0 : Integrable (fun y : ℝ => kernel x y * f y) μq :=
    (by unfold kernel; fun_prop : Continuous (fun y : ℝ => kernel x y * f y)).integrableOn_Icc
  have f1 : Integrable (fun y : ℝ => (-frequency * (y : ℂ) * Complex.sin (frequency * (x : ℂ) * (y : ℂ))) * f y) μq :=
    (by fun_prop : Continuous (fun y : ℝ => (-frequency * (y : ℂ) * Complex.sin (frequency * (x : ℂ) * (y : ℂ))) * f y)).integrableOn_Icc
  have f2 : Integrable (fun y : ℝ => (-(frequency ^ 2) * (y : ℂ) ^ 2 * kernel x y) * f y) μq :=
    (by unfold kernel; fun_prop : Continuous (fun y : ℝ => (-(frequency ^ 2) * (y : ℂ) ^ 2 * kernel x y) * f y)).integrableOn_Icc
  rw [transform, ← integral_const_mul, ← integral_const_mul, ← integral_add (f2.const_mul _) (f1.const_mul _),
    ← integral_const_mul]
  have combined := (f2.const_mul (-((q : ℂ) ^ 2 - (x : ℂ) ^ 2))).add (f1.const_mul (2 * (x : ℂ)))
  change Integrable (fun y : ℝ =>
    -((q : ℂ) ^ 2 - (x : ℂ) ^ 2) * ((-(frequency ^ 2) * (y : ℂ) ^ 2 * kernel x y) * f y) +
      2 * (x : ℂ) * ((-frequency * (y : ℂ) * Complex.sin (frequency * (x : ℂ) * (y : ℂ))) * f y)) μq at combined
  rw [← integral_add combined (f0.const_mul _)]
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem original_green {u v : ℝ → ℂ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    (∫ y : ℝ in (-q)..q, act u y * v y) = ∫ y : ℝ in (-q)..q, u y * act v y := by
  let W := fun y : ℝ => ((q : ℂ) ^ 2 - (y : ℂ) ^ 2) * (u y * deriv v y - deriv u y * v y)
  have derivative (y : ℝ) : HasDerivAt W (act u y * v y - u y * act v y) y := by
    have coefficient : HasDerivAt (fun y : ℝ => (q : ℂ) ^ 2 - (y : ℂ) ^ 2) (-2 * (y : ℂ)) y := by
      convert! (((hasDerivAt_id (y : ℂ)).pow 2).const_sub ((q : ℂ) ^ 2)).comp_ofReal using 1
      simp only [id_eq]
      ring
    have firstU := (hu.differentiable (by norm_num) y).hasDerivAt
    have firstV := (hv.differentiable (by norm_num) y).hasDerivAt
    have secondU := (hu.differentiable_deriv_two y).hasDerivAt
    have secondV := (hv.differentiable_deriv_two y).hasDerivAt
    convert! coefficient.mul ((firstU.mul secondV).sub (secondU.mul firstV)) using 1
    simp only [Pi.mul_apply, Pi.sub_apply]
    unfold act
    ring
  have left : Continuous (fun y => act u y * v y) := (act_continuous hu).mul hv.continuous
  have right : Continuous (fun y => u y * act v y) := hu.continuous.mul (act_continuous hv)
  have source := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => derivative y)
    ((left.sub right).intervalIntegrable (-q) q)
  have endpoints : W q - W (-q) = 0 := by dsimp only [W]; push_cast; ring
  rw [endpoints, intervalIntegral.integral_sub (left.intervalIntegrable (-q) q)
    (right.intervalIntegrable (-q) q)] at source
  exact sub_eq_zero.mp source

private theorem quarter_integral (f : ℝ → ℂ) :
    (∫ y : ℝ, f y ∂μq) = ∫ y : ℝ in (-q)..q, f y := by
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  rfl

/-- The original two-sided kernel identity is integrated with both degenerate-q boundary fluxes paid. -/
theorem original_commutation (f : ℝ → ℂ) (regular : ContDiff ℝ 2 f) (x : ℝ) :
    act (transform f) x = transform (act f) x := by
  rw [original_action_integral f regular.continuous x, transform]
  simp_rw [kernel_joint_action]
  rw [quarter_integral, quarter_integral]
  apply original_green _ regular
  unfold kernel
  exact (Complex.contDiff_cos.restrict_scalars ℝ).comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem original_return_action (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    act (InverseTail.smoothFourier coordinate) x = transform (act (burnolRieszReturnRaw coordinate)) x := by
  have source : InverseTail.smoothFourier coordinate = transform (burnolRieszReturnRaw coordinate) :=
    funext (original_return_kernel coordinate)
  rw [source]
  exact original_commutation _ ((ProlateReturn.original_return_contDiff coordinate).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) x

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ProlateTransform
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
