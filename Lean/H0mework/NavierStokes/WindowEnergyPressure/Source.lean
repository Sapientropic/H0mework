import H0mework.NavierStokes.WindowEnergyPressure.Kernel
import H0mework.NavierStokes.UnheatedWriterTree.RieszControl
import H0mework.NavierStokes.WindowStressHeat.OseenDiffusion
import H0mework.NavierStokes.WindowEnergyApproximation.Tail
import H0mework.NavierStokes.WindowSourceGreen.FiniteDensityCoefficient
import H0mework.NavierStokes.UnheatedWriterTail.Quadratic
import H0mework.NavierStokes.WindowStressHeat.OseenLow

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPressureLowSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing NativeEndpointVelocityCarrier
open NativeWindowPressureLowKernel NativeUnheatedSexticLatticePower NativeUnheatedTreeRiesz
open NativeStressCurlAlgebra
noncomputable section
abbrev Sequence := lp (fun _ : IntegerWavevector => ℂ) 2

def norms (value : Sequence) : Scalar := ⟨fun wave => ‖value wave‖,value.2.norm⟩

theorem norms_norm (value : Sequence) : ‖norms value‖ = ‖value‖ := by
  apply le_antisymm
  · exact lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) (fun wave => (Real.norm_of_nonneg (norm_nonneg (value wave))).le)
  · exact lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) (fun wave => (Real.norm_of_nonneg (norm_nonneg (value wave))).ge)

def integrand (value : wholePhysical) (L : Finset IntegerWavevector) (output input : Coordinate)
    (test : Sequence) (index : IntegerWavevector × IntegerWavevector) : ℂ :=
  star ((density 1 (index.1+index.2) : ℂ)*test (index.1+index.2))*
    rows value L output index.1*wholeVelocity value.1 index.2 input

theorem integrand_bound (value : wholePhysical) (regular : H1 value) (L : Finset IntegerWavevector)
    (output input : Coordinate) (test : Sequence) (index : IntegerWavevector × IntegerWavevector) :
    ‖integrand value L output input test index‖ ≤
      term (norms (space value regular L output))
        (NativeUnheatedTriadSum.rowNorms (wholeVelocity (gradientValue value regular))) (norms test) index := by
  have pressureRead : ‖rows value L output index.1‖ = density 1 index.1*norms (space value regular L output) index.1 := by
    change ‖rows value L output index.1‖ = density 1 index.1*‖(radical index.1:ℂ)*rows value L output index.1‖
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (radical_positive _).le]
    simp only [density,pow_one,← mul_assoc,inv_mul_cancel₀ (radical_positive _).ne',one_mul]
  have velocity : ‖wholeVelocity value.1 index.2 input‖ ≤ density 1 index.2*
      NativeUnheatedTriadSum.rowNorms (wholeVelocity (gradientValue value regular)) index.2 := by
    apply (norm_le_pi_norm _ input).trans
    change ‖wholeVelocity value.1 index.2‖ ≤ density 1 index.2*‖wholeVelocity (gradientValue value regular) index.2‖
    simp only [density,pow_one,inv_mul_eq_div]
    apply (le_div_iff₀ (radical_positive index.2)).mpr
    simpa only [mul_comm] using weighted_velocity value regular index.2
  rw [integrand,norm_mul,norm_mul,norm_star,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (density_positive 1 _).le,pressureRead]
  have paid := mul_le_mul_of_nonneg_left velocity (show 0 ≤
      density 1 (index.1+index.2)*‖test (index.1+index.2)‖*(density 1 index.1*norms (space value regular L output) index.1) by
    change 0 ≤ density 1 (index.1+index.2)*‖test (index.1+index.2)‖*(density 1 index.1*‖space value regular L output index.1‖)
    positivity [density_positive 1 index.1,density_positive 1 (index.1+index.2)])
  apply paid.trans_eq
  simp only [term,norms,NativeUnheatedTriadSum.rowNorms,abs_norm]
  ring

def form (value : wholePhysical) (L F : Finset IntegerWavevector) (output input : Coordinate) (test : Sequence) : ℂ :=
  ∑ p ∈ F, ∑ q ∈ F, integrand value L output input test (p,q)

theorem form_bound (value : wholePhysical) (regular : H1 value) (L F : Finset IntegerWavevector)
    (output input : Coordinate) (test : Sequence) :
    ‖form value L F output input test‖ ≤ (3*Real.sqrt NativeUnheatedRieszKernel.constant)*
      (∑ first ∈ L,cap first)*‖value.1‖*‖gradientValue value regular‖^2*‖test‖ := by
  let P := norms (space value regular L output)
  let U := NativeUnheatedTriadSum.rowNorms (wholeVelocity (gradientValue value regular))
  let S := norms test
  have finiteBudget : (∑ p ∈ F, ∑ q ∈ F, term P U S (p,q)) ≤ ∑' index, term P U S index := by
    rw [← Finset.sum_product]
    exact (summable P U S).sum_le_tsum _ (fun index _ => term_nonnegative P U S index)
  unfold form
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun q _ => integrand_bound value regular L output input test (p,q))).trans
  apply finiteBudget.trans
  apply (bound P U S).trans
  dsimp only [P,U,S]
  rw [norms_norm,norms_norm,NativeUnheatedTriadSum.rowNorms_norm]
  have pressure := space_norm value regular L output
  have velocity := wholeVelocity_norm_le (gradientValue value regular)
  have cap0 : 0 ≤ ∑ first ∈ L,cap first := Finset.sum_nonneg fun first _ => cap_nonnegative first
  calc
    _ ≤ (3*Real.sqrt NativeUnheatedRieszKernel.constant)*
        ((∑ first ∈ L,cap first)*‖value.1‖*‖gradientValue value regular‖)*‖gradientValue value regular‖*‖test‖ := by gcongr
    _ = _ := by ring

def component (test : NativeCompleteStressCarrier.Space) (output input : Coordinate) : Sequence :=
  ⟨fun wave => test wave (output,input),test.2.mono' (fun wave => PiLp.norm_apply_le (test wave) (output,input))⟩

theorem component_bound (test : NativeCompleteStressCarrier.Space) (output input : Coordinate) :
    ‖component test output input‖ ≤ ‖test‖ :=
  lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) (fun wave => PiLp.norm_apply_le (test wave) (output,input))

def work (value : wholePhysical) (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) : ℂ :=
  ∑ output : Coordinate, ∑ input : Coordinate,
    (form value L F output input (component test output input)+form value L F input output (component test output input))

theorem work_bound (value : wholePhysical) (regular : H1 value) (L F : Finset IntegerWavevector)
    (test : NativeCompleteStressCarrier.Space) :
    ‖work value L F test‖ ≤ (54*Real.sqrt NativeUnheatedRieszKernel.constant)*
      (∑ first ∈ L,cap first)*‖value.1‖*‖gradientValue value regular‖^2*‖test‖ := by
  have cap0 : 0 ≤ ∑ first ∈ L,cap first := Finset.sum_nonneg fun first _ => cap_nonnegative first
  have each (output input a b : Coordinate) : ‖form value L F a b (component test output input)‖ ≤
      (3*Real.sqrt NativeUnheatedRieszKernel.constant)*(∑ first ∈ L,cap first)*‖value.1‖*‖gradientValue value regular‖^2*‖test‖ :=
    (form_bound value regular L F a b _).trans (mul_le_mul_of_nonneg_left (component_bound test output input) (by positivity))
  unfold work
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun output _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun input _ => (norm_add_le _ _).trans
      (add_le_add (each output input output input) (each output input input output)))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  ring

theorem work_continuous (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    Continuous (fun value : wholePhysical => work value L F test) := by
  have observed (wave : IntegerWavevector) (coordinate : Coordinate) :
      Continuous (fun value : wholePhysical => wholeVelocity value.1 wave coordinate) :=
    (continuous_apply coordinate).comp ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp
      (wholeVelocityCLM.continuous.comp continuous_subtype_val))
  have pairC (p q : IntegerWavevector) (output : Coordinate) :
      Continuous (fun value : wholePhysical => pair p q (wholeVelocity value.1 p) (wholeVelocity value.1 q) output) := by
    have tensorC : Continuous (fun value : wholePhysical => tensor (wholeVelocity value.1 p) (wholeVelocity value.1 q)) :=
      continuous_pi fun output => continuous_pi fun input => (observed p input).neg.mul (observed q output)
    change Continuous (fun value : wholePhysical => -(Complex.I*(2*Real.pi:ℝ)*
      NativeCofinalStress.stressPressureCLM (p+q) (tensor (wholeVelocity value.1 p) (wholeVelocity value.1 q)))*complexWavevector (p+q) output)
    exact (((NativeCofinalStress.stressPressureCLM (p+q)).continuous.comp tensorC).const_mul _).neg.mul_const _
  have rowsC (wave : IntegerWavevector) (output : Coordinate) : Continuous (fun value : wholePhysical => rows value L output wave) :=
    continuous_finsetSum _ fun first _ => pairC first (wave-first) output
  have formC (output input : Coordinate) : Continuous (fun value : wholePhysical => form value L F output input (component test output input)) :=
    continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ =>
      ((rowsC p output).const_mul _).mul (observed q input)
  have reversed (output input : Coordinate) : Continuous (fun value : wholePhysical => form value L F input output (component test output input)) :=
    continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ =>
      ((rowsC p input).const_mul _).mul (observed q output)
  exact continuous_finsetSum _ fun output _ => continuous_finsetSum _ fun input _ => (formC output input).add (reversed output input)

variable {nu : Viscosity}
open NativeUnheatedSourceGradient NativeUnheatedSourceQuadraticApprox

def coefficient (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) : ℝ :=
  (54*Real.sqrt NativeUnheatedRieszKernel.constant)*(∑ first ∈ L,cap first)*
    NativeUnifiedCompleteSource.budget seed*(2*Real.pi)^2

theorem coefficient_nonnegative (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) :
    0 ≤ coefficient seed L := by
  have cap0 : 0 ≤ ∑ first ∈ L,cap first := Finset.sum_nonneg fun first _ => cap_nonnegative first
  have B0 := (norm_nonneg _).trans (NativeUnifiedCompleteSource.source_bound seed 0)
  unfold coefficient
  positivity

theorem source_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ L F (test : NativeCompleteStressCarrier.Space),
      ‖work (physicalSource seed time) (F∩L) F test‖ ≤ coefficient seed L*‖test‖*NativeUnheatedSourceGradient.mass seed time := by
  filter_upwards [physical_H1_ae seed] with time regular nonnegative L F test
  have paid := work_bound (physical seed time nonnegative) (regular nonnegative) (F∩L) F test
  rw [gradientValue_norm_sq,physical_mass] at paid
  have amplitude := NativeUnheatedSourceWeightedTail.velocity_bound seed time
  have caps : (∑ first ∈ F∩L,cap first) ≤ ∑ first ∈ L,cap first :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun first _ _ => cap_nonnegative first)
  have cap0 : 0 ≤ ∑ first ∈ L,cap first := Finset.sum_nonneg fun first _ => cap_nonnegative first
  rw [physicalSource,dif_pos nonnegative]
  apply paid.trans
  calc
    _ ≤ (54*Real.sqrt NativeUnheatedRieszKernel.constant)*(∑ first ∈ L,cap first)*NativeUnifiedCompleteSource.budget seed*
        ((2*Real.pi)^2*NativeUnheatedSourceGradient.mass seed time)*‖test‖ := by
      change ‖(NativeUnifiedCompleteSource.source seed time).fst‖ ≤ NativeUnifiedCompleteSource.budget seed at amplitude
      gcongr
      · exact mul_nonneg (sq_nonneg _) (mass_nonnegative seed time)
      · simpa only [physical,NativeUnifiedCompleteSource.velocity_read] using amplitude
    _ = _ := by unfold coefficient; ring

def window (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (L F : Finset IntegerWavevector)
    (test : NativeCompleteStressCarrier.Space) : ℂ :=
  ∫ shift, work (physicalSource seed (time-shift)) (F∩L) F test ∂NativeForwardWindowPairingReadout.averageMeasure

theorem window_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    Integrable (fun shift => work (physicalSource seed (time-shift)) (F∩L) F test) NativeForwardWindowPairingReadout.averageMeasure := by
  have moved := (physicalSource_measurable seed).comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) time)
  have source := (work_continuous (F∩L) F test).comp_aestronglyMeasurable moved
  have measured := source.mono_ac (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞)))
  have bound := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae (source_bound_ae seed)
  have actual := (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞))).ae_le bound
  apply ((NativeWindowHistoryGradient.weighted_mass_integrable seed time (by linarith)).const_mul (coefficient seed L*‖test‖)).mono' measured
  filter_upwards [actual,NativeWindowHistoryGNS.average_support] with shift paid support
  exact paid (by linarith) L F test

theorem window_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (inside : time ∈ Icc 0 horizon)
    (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    ‖window seed time L F test‖ ≤ coefficient seed L*‖test‖*(NativeWindowFiniteStressUniform.kernelBound 0*
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)) := by
  have bound := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae (source_bound_ae seed)
  have actual := (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞))).ae_le bound
  unfold window
  apply (norm_integral_le_integral_norm _).trans
  have paid := integral_mono_ae (window_integrable seed time inside.1 L F test).norm
    ((NativeWindowHistoryGradient.weighted_mass_integrable seed time (by linarith [inside.1])).const_mul (coefficient seed L*‖test‖)) (by
      filter_upwards [actual,NativeWindowHistoryGNS.average_support] with shift paid support
      exact paid (by linarith [inside.1]) L F test)
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (NativeWindowStressOseenDiffusion.weighted_mass_horizon seed time horizon inside)
    (mul_nonneg (coefficient_nonnegative seed L) (norm_nonneg _)))

open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

def sourceTest (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (high : Finset IntegerWavevector) :
    NativeCompleteStressCarrier.Space :=
  NativeWindowSobolevUniformTail.high high (NativeWindowFiniteStressUniform.window seed radius 0 time)

theorem sourceTest_read (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (high : Finset IntegerWavevector) (wave : IntegerWavevector) (output input : Coordinate) :
    (density 1 wave : ℂ)*component (sourceTest seed radius time high) output input wave =
      if wave ∈ high then 0 else -NativeWindowFiniteGramFourier.fourierRead wave
        (NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube radius) output input) := by
  change (density 1 wave:ℂ)*(if wave ∈ high then (0 : NativeCompleteStressCarrier.Tensor)
    else NativeWindowFiniteStressUniform.window seed radius 0 time wave) (output,input) = _
  split_ifs with inside
  · change (density 1 wave:ℂ)*0=0
    exact mul_zero _
  · rw [NativeWindowFiniteDensityCoefficient.window_zero_row seed radius time nonnegative wave output input]
    rw [NativeWindowFiniteGramFourier.fourierRead_apply]
    have same : (NativeWindowSobolevStress.quarter wave : ℂ) = (radical wave : ℂ) := rfl
    rw [same]
    simp only [density,pow_one,Complex.ofReal_inv]
    field_simp [(Complex.ofReal_ne_zero.mpr (radical_positive wave).ne')]

def sourceWindow (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ)
    (L high : Finset IntegerWavevector) : ℂ :=
  window seed time L (integerWaveFrequencyCube radius) (sourceTest seed radius time high)

theorem exists_uniform_small (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (L : Finset IntegerWavevector) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ high : Finset IntegerWavevector, ∀ radius : ℕ, ∀ time : Icc (0:ℝ) horizon,
      ‖sourceWindow seed radius time L high‖ ≤ epsilon := by
  let G := NativeWindowFiniteStressUniform.kernelBound 0*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)
  have G0 : 0 ≤ G := (integral_nonneg (fun shift => mass_nonnegative seed (0-shift))).trans
    (NativeWindowStressOseenDiffusion.weighted_mass_horizon seed 0 horizon ⟨le_rfl,nonnegative⟩)
  let A := coefficient seed L*G
  have A0 : 0 ≤ A := mul_nonneg (coefficient_nonnegative seed L) G0
  let delta := epsilon/(A+1)
  have delta0 : 0 < delta := div_pos positive (by linarith)
  obtain ⟨high,tail⟩ := NativeWindowFiniteStressTail.exists_uniform_high seed 0 horizon delta nonnegative delta0
  refine ⟨high,fun radius time => ?_⟩
  have paid := window_bound seed time horizon time.property L (integerWaveFrequencyCube radius) (sourceTest seed radius time high)
  have small : ‖sourceTest seed radius time high‖ ≤ delta := (tail radius time).le
  have controlled : ‖sourceWindow seed radius time L high‖ ≤ A*delta := by
    apply paid.trans
    have bound := mul_le_mul_of_nonneg_left small A0
    simpa only [A,G,mul_assoc,mul_left_comm,mul_comm] using bound
  apply controlled.trans
  have equal : (A+1)*delta = epsilon := mul_div_cancel₀ _ (by linarith : A+1 ≠ 0)
  nlinarith only [equal,delta0]

open NativePhysicalFourier NativeWindowStressHeatSource
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem polynomial_product (F : Finset IntegerWavevector) (a b : IntegerWavevector → ℂ) :
    polynomial F a 0 0*polynomial F b 0 0 =
      ∑ p ∈ F, ∑ q ∈ F, (a p*b q) • UnitAddTorus.mFourier (p+q) := by
  ext point
  simp only [polynomial,pow_zero,one_mul,ContinuousMap.sum_apply,ContinuousMap.mul_apply,
    ContinuousMap.smul_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum,UnitAddTorus.mFourier_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem form_physical (value : wholePhysical) (L F : Finset IntegerWavevector) (output input : Coordinate)
    (test : Sequence) (field : ScalarField)
    (read : ∀ wave, (UnitAddTorus.mFourierBasis (d := Coordinate)).repr field wave = (density 1 wave:ℂ)*test wave) :
    form value L F output input test = inner ℂ field
      ((polynomial F (rows value L output) 0 0*polynomial F (fun wave => wholeVelocity value.1 wave input) 0 0).toLp 2 volume ℂ) := by
  rw [polynomial_product]
  simp only [map_sum,map_smul,inner_sum,inner_smul_right,form]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  have basis : (UnitAddTorus.mFourier (p+q)).toLp 2 volume ℂ = UnitAddTorus.mFourierBasis (p+q) := by
    rw [show UnitAddTorus.mFourierBasis (p+q) = UnitAddTorus.mFourierLp 2 (p+q) from congrFun UnitAddTorus.coe_mFourierBasis (p+q)]
  rw [basis,← inner_conj_symm,← HilbertBasis.repr_apply_apply,read]
  simp only [integrand,starRingEnd_apply]
  ring

theorem source_form_physical (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (high : Finset IntegerWavevector) (value : wholePhysical) (L : Finset IntegerWavevector) (output input : Coordinate) :
    form value L (integerWaveFrequencyCube radius) output input (component (sourceTest seed radius time high) output input) =
      inner ℂ (NativeWindowStressHeatBalance.sigma seed (integerWaveFrequencyCube radius) output input time+
        NativeWindowStressOseenLow.lowField high (NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube radius) output input))
      ((polynomial (integerWaveFrequencyCube radius) (rows value L output) 0 0*
        polynomial (integerWaveFrequencyCube radius) (fun wave => wholeVelocity value.1 wave input) 0 0).toLp 2 volume ℂ) := by
  apply form_physical
  intro wave
  rw [sourceTest_read seed radius time nonnegative high wave output input]
  simp only [NativeWindowStressHeatBalance.sigma,map_add,map_neg,NativeWindowStressOseenLow.lowField,
    NativeWindowStressHeatEnergy.field,LinearIsometryEquiv.apply_symm_apply,lp.coeFn_add,lp.coeFn_neg,
    Pi.add_apply,Pi.neg_apply,NativeWindowStressHeatEnergy.finiteSequence_apply]
  change -NativeWindowFiniteGramFourier.fourierRead wave _+
    (if wave ∈ high then NativeWindowFiniteGramFourier.fourierRead wave _ else 0) = _
  split_ifs <;> ring

open SourceGeneratedNativeResponseDisposition
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem sourceWindow_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (radius : ℕ) (L high : Finset IntegerWavevector) :
    sourceWindow seed radius (step.2.clockAdvance+time) L high = sourceWindow step.1 radius time L high := by
  have test : sourceTest seed radius (step.2.clockAdvance+time) high = sourceTest step.1 radius time high := by
    rw [sourceTest,sourceTest,NativeWindowFiniteStressUniform.window_next seed radius 0 step generated time nonnegative]
  unfold sourceWindow window
  rw [test]
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
  have base : 0 ≤ time-shift := by linarith
  have later : 0 ≤ step.2.clockAdvance+(time-shift) := add_nonneg step.2.clockAdvance_pos.le base
  have same : physicalSource seed (step.2.clockAdvance+time-shift) = physicalSource step.1 (time-shift) := by
    rw [show step.2.clockAdvance+time-shift=step.2.clockAdvance+(time-shift) by ring]
    simp only [physicalSource,dif_pos later,dif_pos base]
    apply Subtype.ext
    change (NativeUnifiedCompleteSource.source seed (step.2.clockAdvance+(time-shift))).fst =
      (NativeUnifiedCompleteSource.source step.1 (time-shift)).fst
    rw [NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) base]
  rw [same]

end
end SaturationMonoid.NavierStokes.NativeWindowPressureLowSource
