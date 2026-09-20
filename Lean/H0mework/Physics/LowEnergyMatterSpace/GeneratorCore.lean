import H0mework.Physics.LowEnergyMatterSpace.Spatial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The actual multiplier energy generates the L² orbit derivative by domination. -/
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

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem fiber_orbit_derivative (k : X) (v : Fiber (ι := ι)) (t : ℝ) :
    HasDerivAt (fun s => timeEvolution (H k) s v)
      (timeEvolution (H k) t (timeGenerator (H k) v)) t := by
  have generated := ((ContinuousLinearMap.apply ℂ (Fiber (ι := ι)) v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    t (timeEvolution_derivative (H k) t)
  exact generated

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem fiber_generator_norm (k : X) (v : Fiber (ι := ι)) :
    ‖timeGenerator (H k) v‖=‖hamiltonianOperator (H k) v‖ := by
  change ‖(-Complex.I) • hamiltonianOperator (H k) v‖=_
  rw [norm_smul,norm_neg,Complex.norm_I,one_mul]

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] in
include hermitian in
theorem fiber_difference_bound (k : X) (v : Fiber (ι := ι)) (t : ℝ) :
    ‖timeEvolution (H k) t v-v‖≤‖hamiltonianOperator (H k) v‖*‖t‖ := by
  have generated := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (f := fun s => timeEvolution (H k) s v)
    (fun s _ => (fiber_orbit_derivative H k v s).differentiableAt)
    (fun s _ => by
      rw [(fiber_orbit_derivative H k v s).deriv,evolution_norm H hermitian,fiber_generator_norm])
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa only [timeEvolution_zero,sub_zero] using generated

def energyField (f : Space (ι := ι) μ) (k : X) : Fiber (ι := ι) :=
  hamiltonianOperator (H k) (f k)

def energyValue (f : Space (ι := ι) μ) (finiteEnergy : MemLp (energyField μ H f) 2 μ) : Space (ι := ι) μ :=
  finiteEnergy.toLp _

omit [TopologicalSpace X] [BorelSpace X] in
theorem energyValue_ae (f : Space (ι := ι) μ) (finiteEnergy : MemLp (energyField μ H f) 2 μ) :
    energyValue μ H f finiteEnergy=ᵐ[μ] energyField μ H f := finiteEnergy.coeFn_toLp

theorem finite_energy_orbit_derivative (f : Space (ι := ι) μ)
    (finiteEnergy : MemLp (energyField μ H f) 2 μ) :
    HasDerivAt (fun t => flow μ H continuousH hermitian t f)
      ((-Complex.I) • energyValue μ H f finiteEnergy) 0 := by
  let pointQuotient := fun t k => (t : ℝ)⁻¹ • (timeEvolution (H k) t (f k)-f k)
  let error := fun t k => pointQuotient t k-(-Complex.I) • energyField μ H f k
  have quotient_bound (t : ℝ) (k : X) : ‖pointQuotient t k‖≤‖energyField μ H f k‖ := by
    by_cases nonzero : t=0
    · simp [pointQuotient,nonzero]
    · dsimp only [pointQuotient,energyField]
      rw [norm_smul,norm_inv]
      calc
        _ ≤ ‖t‖⁻¹*(‖hamiltonianOperator (H k) (f k)‖*‖t‖) :=
          mul_le_mul_of_nonneg_left (fiber_difference_bound H hermitian k (f k) t)
            (inv_nonneg.mpr (norm_nonneg t))
        _ = ‖hamiltonianOperator (H k) (f k)‖ := by
          field_simp [norm_ne_zero_iff.mpr nonzero]
  have error_bound (t : ℝ) (k : X) : ‖‖error t k‖^2‖≤4*‖energyField μ H f k‖^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have estimate : ‖error t k‖≤2*‖energyField μ H f k‖ := by
      dsimp only [error]
      calc
        _ ≤ ‖pointQuotient t k‖+‖(-Complex.I) • energyField μ H f k‖ := norm_sub_le _ _
        _ ≤ ‖energyField μ H f k‖+‖(-Complex.I) • energyField μ H f k‖ := by
          linarith [quotient_bound t k]
        _ = _ := by rw [norm_smul,norm_neg,Complex.norm_I,one_mul]; ring
    nlinarith [norm_nonneg (error t k),norm_nonneg (energyField μ H f k)]
  have measurable (t : ℝ) : AEStronglyMeasurable (fun k => ‖error t k‖^2) μ := by
    have quotient := ((orbit_measurable μ H continuousH t f).sub
      (Lp.memLp f).aestronglyMeasurable).const_smul (t : ℝ)⁻¹
    exact (quotient.sub (finiteEnergy.aestronglyMeasurable.const_smul (-Complex.I))).norm.pow 2
  have integrable : Integrable (fun k => 4*‖energyField μ H f k‖^2) μ :=
    ((memLp_two_iff_integrable_sq_norm finiteEnergy.aestronglyMeasurable).mp finiteEnergy).const_mul 4
  have pointwise (k : X) : Tendsto (fun t => ‖error t k‖^2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have generated := (fiber_orbit_derivative H k (f k) 0).tendsto_slope_zero
    simp only [zero_add,timeEvolution_zero] at generated
    change Tendsto (fun t => pointQuotient t k) (𝓝[≠] 0)
      (𝓝 ((-Complex.I) • energyField μ H f k)) at generated
    have difference := generated.sub (tendsto_const_nhds (x := (-Complex.I) • energyField μ H f k))
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using difference.norm.pow 2
  have integralLimit := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun t k => ‖error t k‖^2) (f := fun _ => (0 : ℝ))
    (fun k => 4*‖energyField μ H f k‖^2) (Eventually.of_forall measurable)
    (Eventually.of_forall fun t => ae_of_all _ (error_bound t)) integrable (ae_of_all _ pointwise)
  have equality (t : ℝ) : (∫ k, ‖error t k‖^2 ∂μ)=
      ‖t⁻¹ • (flow μ H continuousH hermitian t f-f)-
        (-Complex.I) • energyValue μ H f finiteEnergy‖^2 := by
    rw [← norm_square_integral μ]
    apply integral_congr_ae
    filter_upwards [applyFlow_ae μ H continuousH hermitian t f,energyValue_ae μ H f finiteEnergy,
      Lp.coeFn_sub (flow μ H continuousH hermitian t f) f,
      Lp.coeFn_smul t⁻¹ (flow μ H continuousH hermitian t f-f),
      Lp.coeFn_smul (-Complex.I) (energyValue μ H f finiteEnergy),
      Lp.coeFn_sub (t⁻¹ • (flow μ H continuousH hermitian t f-f))
        ((-Complex.I) • energyValue μ H f finiteEnergy)] with k ht he hsub hscale henergy hdiff
    rw [hdiff]
    change ‖error t k‖^2=‖(t⁻¹ • (flow μ H continuousH hermitian t f-f)) k-
      ((-Complex.I) • energyValue μ H f finiteEnergy) k‖^2
    rw [hscale,henergy]
    change ‖error t k‖^2=‖t⁻¹ • ((flow μ H continuousH hermitian t f-f) k)-
      (-Complex.I) • energyValue μ H f finiteEnergy k‖^2
    rw [hsub]
    change ‖error t k‖^2=‖t⁻¹ • (applyFlow μ H continuousH hermitian t f k-f k)-
      (-Complex.I) • energyValue μ H f finiteEnergy k‖^2
    rw [ht,he]
  simp only [equality,integral_zero] at integralLimit
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simp only [zero_add,flow_zero]
  rw [tendsto_iff_dist_tendsto_zero]
  have root := Real.continuous_sqrt.continuousAt.tendsto.comp integralLimit
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero,dist_eq_norm] using root

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
