import H0mework.NavierStokes.WindowEnergyJoint.EnergyGate

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowTraceGradient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowStressHeatGram
noncomputable section

theorem cross_trace_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (value tangent : Coordinate → H) :
    (∑ output : Coordinate,∑ input : Coordinate,(cross value tangent output input)^2)≤
      4*Matrix.trace (gram value)*Matrix.trace (gram tangent) := by
  have inner_bound (x y : H) : (inner ℝ x y)^2≤‖x‖^2*‖y‖^2 := by
    have paid := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm x y) 2
    simpa only [sq_abs,mul_pow] using paid
  have row (output input : Coordinate) : (cross value tangent output input)^2≤
      2*(‖value output‖^2*‖tangent input‖^2)+2*(‖tangent output‖^2*‖value input‖^2) := by
    unfold cross
    nlinarith only [inner_bound (value output) (tangent input),inner_bound (tangent output) (value input),
      sq_nonneg (inner ℝ (value output) (tangent input)-inner ℝ (tangent output) (value input))]
  apply (Finset.sum_le_sum fun output _ => Finset.sum_le_sum fun input _ => row output input).trans_eq
  simp only [Matrix.trace,Matrix.diag_apply,gram,Matrix.gram_apply,real_inner_self_eq_norm_sq,
    Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem gradient_trace_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (value : Coordinate → H) (gradient : Coordinate → Coordinate → H) :
    (∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,(cross value (gradient j) output input)^2)≤
      4*Matrix.trace (gram value)*Matrix.trace (gradientGram gradient) := by
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ => cross_trace_bound value (gradient j)
  apply paid.trans_eq
  simp only [gradientGram,Matrix.trace,Matrix.diag_apply,Matrix.sum_apply,← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def traceStress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : C(Torus,ℝ) :=
  ∑ i : Coordinate,NativeWindowFiniteGramFourier.stress seed time F i i

def traceDiffusion (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : C(Torus,ℝ) :=
  ∑ i : Coordinate,NativeWindowStressHeatSource.diffusion seed time F i i

def traceInteraction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : C(Torus,ℝ) :=
  traceStress seed time F*traceDiffusion seed time F

theorem source_point_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (point : Torus) :
    (∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,
      ‖NativeWindowStressHeatSource.stressJet seed time F j 1 output input point‖^2)≤4*traceInteraction seed time F point := by
  obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  simp only [NativeWindowStressHeatSource.stressJet_first seed time F closed,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    traceInteraction,traceStress,traceDiffusion,ContinuousMap.mul_apply,ContinuousMap.sum_apply,
    NativeWindowFiniteGramFourier.stress_physical,NativeWindowStressHeatSource.diffusion_physical]
  simpa only [Matrix.trace,Matrix.diag_apply,NativeWindowFiniteGramSource.stress,NativeWindowFiniteGramSource.gradientStress,mul_assoc]
    using gradient_trace_bound (NativeWindowFiniteGramSource.value seed time F x) (NativeWindowFiniteGramSource.gradient seed time F x)

theorem traceInteraction_nonnegative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) : 0≤traceInteraction seed time F point := by
  obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  simp only [traceInteraction,traceStress,traceDiffusion,ContinuousMap.mul_apply,ContinuousMap.sum_apply,
    NativeWindowFiniteGramFourier.stress_physical,NativeWindowStressHeatSource.diffusion_physical]
  change 0≤(∑ i : Coordinate,inner ℝ (NativeWindowFiniteGramSource.value seed time F x i)
    (NativeWindowFiniteGramSource.value seed time F x i))*(∑ i : Coordinate,∑ j : Coordinate,
      inner ℝ (NativeWindowFiniteGramSource.gradient seed time F x j i) (NativeWindowFiniteGramSource.gradient seed time F x j i))
  exact mul_nonneg (Finset.sum_nonneg fun _ _ => real_inner_self_nonneg)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => real_inner_self_nonneg)

private theorem field_norm_square (f : C(Torus,ℂ)) : ‖f.toLp 2 volume ℂ‖^2=∫ point : Torus,‖f point‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f] with point actual
  rw [actual,real_inner_self_eq_norm_sq]

theorem source_gradient_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) :
    NativeWindowStressHeatSource.dirichlet seed time F≤4*(∫ point : Torus,traceInteraction seed time F point) := by
  have paid (j output input : Coordinate) : Integrable (fun point : Torus => ‖NativeWindowStressHeatSource.stressJet seed time F j 1 output input point‖^2) :=
    ((NativeWindowStressHeatSource.stressJet seed time F j 1 output input).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have read (j output input : Coordinate) :
      ‖NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteJet (F+F)
        (fun k => NativeWindowFiniteGramFourier.coefficients seed time F k output input) j 1)‖^2=
        ∫ point : Torus,‖NativeWindowStressHeatSource.stressJet seed time F j 1 output input point‖^2 := by
    rw [← NativeWindowStressHeatSource.polynomial_field]
    exact field_norm_square _
  rw [NativeWindowStressHeatSource.dirichlet]
  simp only [read]
  have original := integral_mono (integrable_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ
      (fun output _ => integrable_finsetSum Finset.univ (fun input _ => paid j output input))))
    (((traceInteraction seed time F).continuous.const_mul 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (source_point_bound seed time F closed)
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ
    (fun output _ => integrable_finsetSum Finset.univ (fun input _ => paid j output input)))] at original
  simp_rw [integral_finsetSum Finset.univ (fun output _ => integrable_finsetSum Finset.univ (fun input _ => paid _ output input)),
    integral_finsetSum Finset.univ (fun input _ => paid _ _ input)] at original
  exact original.trans_eq (integral_const_mul _ _)

end
end SaturationMonoid.NavierStokes.NativeWindowTraceGradient
