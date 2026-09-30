import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Cubic

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalMixedCubic
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeUnheatedSexticLatticePower
open NativeWindowStressHeatSource (physical)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeUnheatedTreeRieszPermutations (outputEquiv)
open NativeWindowTraceTerminalCubic (Z decode physical_fourier halfTrace halfTrace_read halfTrace_bound halfBudget budget)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def term (first last : Z) (index : IntegerWavevector × IntegerWavevector) : ℂ :=
  conj (decode last index.1)*(decode first index.2*decode first (index.1-index.2))

theorem term_norm (first last : Z) (index : IntegerWavevector × IntegerWavevector) :
    ‖term first last index‖=NativeUnheatedTreeRiesz.term (lp.toNorm first) (lp.toNorm first) (lp.toNorm last) (outputEquiv.symm index) := by
  simp only [term,decode,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg (density_positive _ _).le,
    NativeUnheatedTreeRiesz.term,outputEquiv,Equiv.coe_fn_symm_mk,add_sub_cancel,lp.toNorm,abs_of_nonneg (norm_nonneg _)]
  ring

theorem term_summable (first last : Z) : Summable (fun index => ‖term first last index‖) := by
  simp_rw [term_norm]
  exact outputEquiv.symm.summable_iff.mpr (NativeUnheatedTreeRiesz.summable (lp.toNorm first) (lp.toNorm first) (lp.toNorm last))

theorem term_bound (first last : Z) : (∑' index,‖term first last index‖)≤
    3*Real.sqrt NativeUnheatedRieszKernel.constant*‖first‖^2*‖last‖ := by
  simp_rw [term_norm]
  rw [outputEquiv.symm.tsum_eq]
  exact (NativeUnheatedTreeRiesz.bound (lp.toNorm first) (lp.toNorm first) (lp.toNorm last)).trans_eq
    (by rw [lp.norm_toNorm,lp.norm_toNorm]; ring)

theorem mixed_pairing (f g : C(Torus,ℝ)) (first last : Z)
    (firstRead : ∀ k,fourierRead k f=decode first k) (lastRead : ∀ k,fourierRead k g=decode last k) :
    inner ℂ (physical g) (physical (f*f))=∑' index,term first last index := by
  rw [← (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.inner_map_map,lp.inner_eq_tsum,
    (term_summable first last).of_norm.tsum_prod]
  apply tsum_congr
  intro k
  simp only [UnitAddTorus.mFourierBasis_repr,physical_fourier,NativeWindowHighTransportWork.fourier_product,
    firstRead,lastRead,RCLike.inner_apply,term,tsum_mul_left]
  ring

theorem mixed_bound (f g : C(Torus,ℝ)) (first last : Z)
    (firstRead : ∀ k,fourierRead k f=decode first k) (lastRead : ∀ k,fourierRead k g=decode last k) :
    |∫ point : Torus,(f point)^2*g point|≤3*Real.sqrt NativeUnheatedRieszKernel.constant*‖first‖^2*‖last‖ := by
  have same : (∫ point : Torus,(f point)^2*g point)=(inner ℂ (physical g) (physical (f*f))).re := by
    rw [← NativeWindowTraceTerminalCubic.real_pairing,NativeWindowStressHeatSource.physical_inner]
    apply integral_congr_ae
    filter_upwards with point
    simp only [ContinuousMap.mul_apply]
    ring
  rw [same,mixed_pairing f g first last firstRead lastRead]
  exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm (term_summable first last)).trans (term_bound first last))

variable {nu : Viscosity}

theorem source_mixed_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (frame sampling horizon : ℝ)
    (frameInside : frame∈Icc 0 horizon) (sampleInside : sampling∈Icc 0 horizon) :
    (∫ point : Torus,(NativeWindowTraceGradient.traceStress seed frame (integerWaveFrequencyCube radius) point)^2*
      NativeWindowTraceGradient.traceStress seed sampling (integerWaveFrequencyCube radius) point)≤budget seed horizon := by
  have native:=mixed_bound _ _ (halfTrace seed radius frame) (halfTrace seed radius sampling)
    (halfTrace_read seed radius frame frameInside.1) (halfTrace_read seed radius sampling sampleInside.1)
  have upper:=mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (halfTrace_bound seed radius frame horizon frameInside) 2)
    (halfTrace_bound seed radius sampling horizon sampleInside) (norm_nonneg _) (sq_nonneg _)
  have multiplied:=mul_le_mul_of_nonneg_left upper (by positivity : 0≤3*Real.sqrt NativeUnheatedRieszKernel.constant)
  have paid : 3*Real.sqrt NativeUnheatedRieszKernel.constant*‖halfTrace seed radius frame‖^2*
      ‖halfTrace seed radius sampling‖≤budget seed horizon := by
    unfold budget
    convert! multiplied using 1
    ring
  exact (le_abs_self _).trans (native.trans paid)

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalMixedCubic
