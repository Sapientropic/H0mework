import H0mework.Physics.LowEnergy.FullQuantum.FullSpace.Lift
import H0mework.Physics.LowEnergyMatterSpace.Continuity

/-! A uniform triangular bound lifts joint finite-fiber continuity to strong L² continuity. -/
set_option autoImplicit false
open Set MeasureTheory Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
open YangMills.FullPairing
noncomputable section
variable (matrices : ℝ → Position → FiberOperators)
    (continuousMatrices : Continuous (fun tx : ℝ × Position => matrices tx.1 tx.2))
    (rate : ℝ) (nonnegative : 0≤rate)
    (bounded : ∀ t x, ‖matrices t x‖≤1+|t| * rate)

include continuousMatrices in
theorem matrices_continuous (time : ℝ) : Continuous (matrices time) :=
  continuousMatrices.comp (continuous_const.prodMk continuous_id)

def liftedFamily (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  multiplier (matrices time) (matrices_continuous matrices continuousMatrices time)
    (1+|time| * rate) (bounded time) (by positivity)

theorem liftedFamily_ae (time : ℝ) (initial : FullMatterL2) :
    liftedFamily matrices continuousMatrices rate nonnegative bounded time initial=ᵐ[volume]
      fun x => matrices time x (initial x) :=
  multiplierValue_ae (matrices time) (matrices_continuous matrices continuousMatrices time)
    (1+|time| * rate) (bounded time) initial

theorem liftedFamily_norm (time : ℝ) :
    ‖liftedFamily matrices continuousMatrices rate nonnegative bounded time‖≤1+|time| * rate :=
  multiplier_norm _ _ _ _ (by positivity)

theorem liftedFamily_stronglyContinuous (initial : FullMatterL2) :
    Continuous (fun time => liftedFamily matrices continuousMatrices rate nonnegative bounded time initial) := by
  apply continuous_iff_continuousAt.mpr
  intro t0
  let difference := fun t x => matrices t x (initial x)-matrices t0 x (initial x)
  let limit := 2+(2 * |t0| + 1)*rate
  have measurable (t : ℝ) : AEStronglyMeasurable (fun x => ‖difference t x‖^2) volume :=
    ((multiplier_measurable (matrices t) (matrices_continuous matrices continuousMatrices t) initial).sub
      (multiplier_measurable (matrices t0) (matrices_continuous matrices continuousMatrices t0) initial)).norm.pow 2
  have localBound (t : ℝ) (near : |t| < |t0| + 1) (x : Position) :
      ‖‖difference t x‖^2‖≤limit^2*‖initial x‖^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have estimate : ‖difference t x‖≤limit*‖initial x‖ := by
      calc
        _ ≤ ‖matrices t x (initial x)‖+‖matrices t0 x (initial x)‖ := norm_sub_le _ _
        _ ≤ (1+|t| * rate)*‖initial x‖+(1+|t0| * rate)*‖initial x‖ :=
          add_le_add (((matrices t x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (bounded t x) (norm_nonneg _)))
            (((matrices t0 x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (bounded t0 x) (norm_nonneg _)))
        _ ≤ (1+(|t0|+1)*rate)*‖initial x‖+(1+|t0| * rate)*‖initial x‖ := by gcongr
        _ = _ := by dsimp [limit]; ring
    exact (pow_le_pow_left₀ (norm_nonneg _) estimate 2).trans_eq (by ring)
  have integrable : Integrable (fun x => limit^2*‖initial x‖^2) volume :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp initial).aestronglyMeasurable).mp
      (Lp.memLp initial)).const_mul (limit^2)
  have pointwise (x : Position) : Tendsto (fun t => ‖difference t x‖^2) (𝓝 t0) (𝓝 0) := by
    have continuous : Continuous (fun t => matrices t x (initial x)) :=
      (ContinuousLinearMap.apply ℂ Hilbert (initial x)).continuous.comp
        (continuousMatrices.comp (continuous_id.prodMk continuous_const))
    have limit := (continuous.tendsto t0).sub (tendsto_const_nhds (x := matrices t0 x (initial x)))
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using limit.norm.pow 2
  have near : ∀ᶠ t in 𝓝 t0, |t| < |t0| + 1 :=
    continuous_abs.continuousAt.tendsto.eventually (eventually_lt_nhds (by linarith : |t0| < |t0| + 1))
  have dominated : ∀ᶠ t in 𝓝 t0, ∀ᵐ x ∂volume, ‖‖difference t x‖^2‖≤limit^2*‖initial x‖^2 :=
    near.mono fun t bound => ae_of_all _ (localBound t bound)
  have integralLimit := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (F := fun t x => ‖difference t x‖^2) (f := fun _ => (0 : ℝ))
    (fun x => limit^2*‖initial x‖^2) (Eventually.of_forall measurable) dominated integrable (ae_of_all _ pointwise)
  have equality (t : ℝ) : (∫ x, ‖difference t x‖^2)=
      ‖liftedFamily matrices continuousMatrices rate nonnegative bounded t initial-
        liftedFamily matrices continuousMatrices rate nonnegative bounded t0 initial‖^2 := by
    rw [← MatterSpace.norm_square_integral volume]
    apply integral_congr_ae
    filter_upwards [liftedFamily_ae matrices continuousMatrices rate nonnegative bounded t initial,
      liftedFamily_ae matrices continuousMatrices rate nonnegative bounded t0 initial,
      Lp.coeFn_sub (liftedFamily matrices continuousMatrices rate nonnegative bounded t initial)
        (liftedFamily matrices continuousMatrices rate nonnegative bounded t0 initial)] with x ht h0 hsub
    rw [hsub]
    change ‖difference t x‖^2=‖liftedFamily matrices continuousMatrices rate nonnegative bounded t initial x-
      liftedFamily matrices continuousMatrices rate nonnegative bounded t0 initial x‖^2
    rw [ht,h0]
  simp only [equality,integral_zero] at integralLimit
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have root := Real.continuous_sqrt.continuousAt.tendsto.comp integralLimit
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero,dist_eq_norm] using root

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
