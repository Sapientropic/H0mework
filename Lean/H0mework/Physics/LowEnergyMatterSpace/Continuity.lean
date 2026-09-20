import H0mework.Physics.LowEnergyMatterSpace.Multiplier

/-! Domination by the original L² vector gives strong continuity without a bounded Hamiltonian. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open Fermion
noncomputable section
variable {ι X : Type*} [Fintype ι] [LinearOrder ι]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (H : X → Matrix ι ι ℂ)
  (continuousH : Continuous H) (hermitian : ∀ k, (H k).conjTranspose=H k)

omit [LinearOrder ι] [TopologicalSpace X] [BorelSpace X] in
theorem norm_square_integral (f : Space (ι := ι) μ) :
    (∫ k, ‖f k‖^2 ∂μ)=‖f‖^2 := by
  calc
    _ = ∫ k, (inner ℂ (f k) (f k)).re ∂μ :=
      integral_congr_ae (ae_of_all _ fun k => (inner_self_eq_norm_sq (𝕜 := ℂ) (f k)).symm)
    _ = (∫ k, inner ℂ (f k) (f k) ∂μ).re :=
      Complex.reCLM.integral_comp_comm (L2.integrable_inner f f)
    _ = ‖f‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) f

omit [MeasurableSpace X] [BorelSpace X] in
include continuousH in
theorem point_orbit_continuous (k : X) (v : Fiber (ι := ι)) :
    Continuous (fun t : ℝ => timeEvolution (H k) t v) := by
  exact (ContinuousLinearMap.apply ℂ (Fiber (ι := ι)) v).continuous.comp
    ((evolution_joint_continuous H continuousH).comp (continuous_id.prodMk continuous_const))

theorem flow_stronglyContinuous (f : Space (ι := ι) μ) :
    Continuous (fun t => flow μ H continuousH hermitian t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t0
  let difference := fun t k => timeEvolution (H k) t (f k)-timeEvolution (H k) t0 (f k)
  have measurable (t : ℝ) : AEStronglyMeasurable (fun k => ‖difference t k‖^2) μ :=
    ((orbit_measurable μ H continuousH t f).sub
      (orbit_measurable μ H continuousH t0 f)).norm.pow 2
  have bound (t : ℝ) (k : X) : ‖‖difference t k‖^2‖ ≤ 4*‖f k‖^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have estimate : ‖difference t k‖ ≤ 2*‖f k‖ := by
      dsimp only [difference]
      calc
        _ ≤ ‖timeEvolution (H k) t (f k)‖+‖timeEvolution (H k) t0 (f k)‖ := norm_sub_le _ _
        _ = _ := by rw [evolution_norm H hermitian,evolution_norm H hermitian]; ring
    nlinarith [norm_nonneg (difference t k),norm_nonneg (f k)]
  have integrable : Integrable (fun k => 4*‖f k‖^2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp
      (Lp.memLp f)).const_mul 4
  have pointwise (k : X) : Tendsto (fun t => ‖difference t k‖^2) (𝓝 t0) (𝓝 0) := by
    have actual := ((point_orbit_continuous H continuousH k (f k)).tendsto t0).sub
      (tendsto_const_nhds (x := timeEvolution (H k) t0 (f k)))
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using actual.norm.pow 2
  have integralLimit := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun t k => ‖difference t k‖^2) (f := fun _ => (0 : ℝ))
    (fun k => 4*‖f k‖^2) (Eventually.of_forall measurable)
    (Eventually.of_forall fun t => ae_of_all _ (bound t)) integrable
    (ae_of_all _ pointwise)
  have equality (t : ℝ) : (∫ k, ‖difference t k‖^2 ∂μ)=
      ‖flow μ H continuousH hermitian t f-flow μ H continuousH hermitian t0 f‖^2 := by
    rw [← norm_square_integral μ]
    apply integral_congr_ae
    filter_upwards [applyFlow_ae μ H continuousH hermitian t f,
      applyFlow_ae μ H continuousH hermitian t0 f,
      Lp.coeFn_sub (flow μ H continuousH hermitian t f)
        (flow μ H continuousH hermitian t0 f)] with k ht h0 hsub
    rw [hsub]
    change ‖difference t k‖^2=‖applyFlow μ H continuousH hermitian t f k-
      applyFlow μ H continuousH hermitian t0 f k‖^2
    rw [ht,h0]
  simp only [equality,integral_zero] at integralLimit
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have root := Real.continuous_sqrt.continuousAt.tendsto.comp integralLimit
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero,dist_eq_norm] using root

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
