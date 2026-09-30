import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.RieszControl
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.FiniteDensityCoefficient
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Gradient
import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Work

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalCubic
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeUnheatedSexticLatticePower
open NativeWindowStressHeatSource (physical)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeUnheatedTreeRieszPermutations (outputEquiv)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev Z := NativeWindowHighTransportProduct.Z

def decode (value : Z) (k : IntegerWavevector) : ℂ := (density 1 k : ℂ)*value k

def term (value : Z) (index : IntegerWavevector × IntegerWavevector) : ℂ :=
  conj (decode value index.1)*(decode value index.2*decode value (index.1-index.2))

theorem term_norm (value : Z) (index : IntegerWavevector × IntegerWavevector) :
    ‖term value index‖=NativeUnheatedTreeRiesz.term (lp.toNorm value) (lp.toNorm value) (lp.toNorm value) (outputEquiv.symm index) := by
  simp only [term,decode,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg (density_positive _ _).le,
    NativeUnheatedTreeRiesz.term,outputEquiv,Equiv.coe_fn_symm_mk,add_sub_cancel,
    lp.toNorm,abs_of_nonneg (norm_nonneg _)]
  ring

theorem term_summable (value : Z) : Summable (fun index => ‖term value index‖) := by
  simp_rw [term_norm]
  exact outputEquiv.symm.summable_iff.mpr (NativeUnheatedTreeRiesz.summable (lp.toNorm value) (lp.toNorm value) (lp.toNorm value))

theorem term_bound (value : Z) : (∑' index,‖term value index‖)≤3*Real.sqrt NativeUnheatedRieszKernel.constant*‖value‖^3 := by
  simp_rw [term_norm]
  rw [outputEquiv.symm.tsum_eq]
  exact (NativeUnheatedTreeRiesz.bound (lp.toNorm value) (lp.toNorm value) (lp.toNorm value)).trans_eq (by rw [lp.norm_toNorm]; ring)

theorem physical_fourier (f : C(Torus,ℝ)) (k : IntegerWavevector) : UnitAddTorus.mFourierCoeff (physical f) k=fourierRead k f := by
  change UnitAddTorus.mFourierCoeff (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) f).toLp 2 volume ℂ) k=_
  rw [UnitAddTorus.mFourierCoeff_toLp,NativeWindowFiniteGramFourier.fourierRead_apply]
  rfl

theorem cubic_pairing (f : C(Torus,ℝ)) (value : Z) (original : ∀ k,fourierRead k f=decode value k) :
    inner ℂ (physical f) (physical (f*f))=∑' index,term value index := by
  rw [← (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.inner_map_map,lp.inner_eq_tsum,
    (term_summable value).of_norm.tsum_prod]
  apply tsum_congr
  intro k
  simp only [UnitAddTorus.mFourierBasis_repr,physical_fourier,NativeWindowHighTransportWork.fourier_product,original,RCLike.inner_apply]
  simp only [term,tsum_mul_left]
  ring

theorem real_pairing (first last : ScalarField) : inner ℝ first last=(inner ℂ first last).re := by
  rw [L2.inner_def,L2.inner_def]
  change (∫ point : Torus,RCLike.re (inner ℂ (first point) (last point)))=
    RCLike.re (∫ point : Torus,inner ℂ (first point) (last point))
  exact integral_re (L2.integrable_inner first last)

theorem cubic_bound (f : C(Torus,ℝ)) (value : Z) (original : ∀ k,fourierRead k f=decode value k) :
    |∫ point : Torus,(f point)^3|≤3*Real.sqrt NativeUnheatedRieszKernel.constant*‖value‖^3 := by
  have same : (∫ point : Torus,(f point)^3)=(inner ℂ (physical f) (physical (f*f))).re := by
    rw [← real_pairing,NativeWindowStressHeatSource.physical_inner]
    apply integral_congr_ae
    filter_upwards with point
    simp only [ContinuousMap.mul_apply]
    ring
  rw [same,cubic_pairing f value original]
  exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm (term_summable value)).trans (term_bound value))

variable {nu : Viscosity}

def halfTrace (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) : Z :=
  -∑ i : Coordinate,NativeWindowPressureLowSource.component (NativeWindowFiniteStressUniform.window seed radius 0 time) i i

theorem halfTrace_read (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0≤time) (k : IntegerWavevector) :
    fourierRead k (NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube radius))=decode (halfTrace seed radius time) k := by
  simp only [NativeWindowTraceGradient.traceStress,map_sum,decode,halfTrace,lp.coeFn_neg,lp.coeFn_sum,Pi.neg_apply,Finset.sum_apply]
  change (∑ i : Coordinate,fourierRead k (NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube radius) i i))=
    (density 1 k : ℂ)*(-(∑ i : Coordinate,NativeWindowFiniteStressUniform.window seed radius 0 time k (i,i)))
  simp only [NativeWindowFiniteDensityCoefficient.window_zero_row seed radius time nonnegative k,← Finset.mul_sum,
    ← NativeWindowFiniteGramFourier.fourierRead_apply]
  have restore : (density 1 k : ℂ)*(NativeWindowSobolevStress.quarter k : ℂ)=1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    change (radical k^1)⁻¹*radical k=1
    rw [pow_one,inv_mul_cancel₀ (radical_positive k).ne']
  rw [neg_mul,neg_neg,← mul_assoc,restore,one_mul]

def halfBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  3*(NativeWindowFiniteStressUniform.kernelBound 0*NativeWindowFiniteStressConvergence.cap*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2))

theorem halfTrace_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time horizon : ℝ) (inside : time∈Icc 0 horizon) :
    ‖halfTrace seed radius time‖≤halfBudget seed horizon := by
  rw [halfTrace,norm_neg]
  apply (norm_sum_le _ _).trans
  have row (i : Coordinate) := (NativeWindowPressureLowSource.component_bound (NativeWindowFiniteStressUniform.window seed radius 0 time) i i).trans
    (NativeWindowFiniteStressUniform.window_bound seed radius 0 time horizon inside)
  exact (Finset.sum_le_sum fun i _ => row i).trans_eq (by unfold halfBudget; simp)

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  3*Real.sqrt NativeUnheatedRieszKernel.constant*(halfBudget seed horizon)^3

theorem source_cubic_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time horizon : ℝ) (inside : time∈Icc 0 horizon) :
    (∫ point : Torus,(NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube radius) point)^3)≤budget seed horizon :=
  (le_abs_self _).trans ((cubic_bound _ (halfTrace seed radius time) (halfTrace_read seed radius time inside.1)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (halfTrace_bound seed radius time horizon inside) 3) (by positivity)))

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalCubic
