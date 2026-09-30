import H0mework.NavierStokes.WindowEnergyPressureSectors.Kernel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowPressureLowInputs
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing NativeEndpointVelocityCarrier
open NativeWindowPressureSectors NativeWindowPressureLowSource NativeUnheatedSourceGradient NativeUnheatedSourceQuadraticApprox
noncomputable section

def high (value : ComplexVorticityHilbertState) (L : Finset IntegerWavevector) : ComplexVorticityHilbertState :=
  value-complexSharpSupportProjection L value

theorem high_row (value : ComplexVorticityHilbertState) (L : Finset IntegerWavevector) (wave : IntegerWavevector) :
    high value L wave = if wave ∈ L then 0 else value wave := by
  simp only [high,lp.coeFn_sub,Pi.sub_apply,complexSharpSupportProjection_apply]
  split_ifs <;> simp

theorem high_density (value : ComplexVorticityHilbertState) (L : Finset IntegerWavevector) (wave : IntegerWavevector) :
    NativeUnheatedStressProduct.density (high value L) wave =
      if wave ∈ L then 0 else NativeUnheatedStressProduct.density value wave := by
  simp only [NativeUnheatedStressProduct.density,NativeUnheatedStressProduct.amplitude,high_row]
  split_ifs <;> simp [euclideanCoordinateRow]

theorem high_H1 (value : ComplexVorticityHilbertState) (regular : NativeUnheatedStressProduct.H1 value)
    (L : Finset IntegerWavevector) : NativeUnheatedStressProduct.H1 (high value L) := by
  apply regular.of_nonneg_of_le (NativeUnheatedStressProduct.density_nonnegative _)
  intro wave
  rw [high_density]
  split_ifs
  · exact NativeUnheatedStressProduct.density_nonnegative value wave
  · rfl

theorem high_mass (value : ComplexVorticityHilbertState) (regular : NativeUnheatedStressProduct.H1 value)
    (L : Finset IntegerWavevector) : NativeUnheatedStressProduct.gradientMass (high value L) ≤ NativeUnheatedStressProduct.gradientMass value := by
  apply (high_H1 value regular L).tsum_le_tsum _ regular
  intro wave
  rw [high_density]
  split_ifs
  · exact NativeUnheatedStressProduct.density_nonnegative value wave
  · rfl

theorem high_zero (value : ComplexVorticityHilbertState) (zero : value 0=0) (L : Finset IntegerWavevector) : high value L 0=0 := by
  simp only [high_row,zero,ite_self]

def tensorWork (left right last : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) : ℂ :=
  ∑ output : Coordinate, ∑ input : Coordinate,
    (trilinear left right last F output input (component test output input)+
      trilinear left right last F input output (component test output input))

def remainder (value : wholePhysical) (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) : ℂ :=
  tensorWork (wholeVelocity value.1) (wholeVelocity value.1) (wholeVelocity value.1) F test-
    tensorWork (high (wholeVelocity value.1) L) (high (wholeVelocity value.1) L) (high (wholeVelocity value.1) L) F test

theorem remainder_sectors (value : wholePhysical) (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    remainder value L F test = 2*work value L F test-
      tensorWork (complexSharpSupportProjection L (wholeVelocity value.1)) (complexSharpSupportProjection L (wholeVelocity value.1))
        (wholeVelocity value.1) F test+
      tensorWork (high (wholeVelocity value.1) L) (high (wholeVelocity value.1) L)
        (complexSharpSupportProjection L (wholeVelocity value.1)) F test := by
  simp only [remainder,tensorWork,trilinear_sectors (wholeVelocity value.1) (complexSharpSupportProjection L (wholeVelocity value.1)),
    ← trilinear_low,work,high,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  ring

private theorem tensorWork_bound (left right last : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (test : NativeCompleteStressCarrier.Space) (cap : ℝ) (nonnegative : 0 ≤ cap)
    (paid : ∀ output input (scalar : Sequence), ‖trilinear left right last F output input scalar‖ ≤ cap*‖scalar‖) :
    ‖tensorWork left right last F test‖ ≤ 18*cap*‖test‖ := by
  have each (a b output input : Coordinate) : ‖trilinear left right last F a b (component test output input)‖ ≤ cap*‖test‖ :=
    (paid a b _).trans (mul_le_mul_of_nonneg_left (component_bound test output input) nonnegative)
  unfold tensorWork
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun output _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun input _ => (norm_add_le _ _).trans
      (add_le_add (each output input output input) (each input output output input)))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  ring

theorem remainder_bound (value : wholePhysical) (regular : H1 value) (L F : Finset IntegerWavevector)
    (test : NativeCompleteStressCarrier.Space) :
    ‖remainder value L F test‖ ≤
      (108*Real.sqrt NativeUnheatedRieszKernel.constant*(∑ p ∈ L, NativeWindowPressureLowKernel.cap p)*‖value.1‖*
        ‖gradientValue value regular‖^2+18*lowLowCap L*‖value.1‖^3+
        216*thirdCap L*Real.sqrt NativeUnheatedRieszKernel.constant*‖value.1‖*gradientMass value)*‖test‖ := by
  let u := wholeVelocity value.1
  let h := high u L
  have same : NativeUnheatedStressProduct.H1 u := regular
  have zero : h 0=0 := high_zero u (wholeVelocity_zero value.1) L
  have hh : NativeUnheatedStressProduct.H1 h := high_H1 u same L
  have g : NativeUnheatedStressProduct.gradientMass h ≤ gradientMass value := high_mass u same L
  have uBound : ‖u‖ ≤ ‖value.1‖ := wholeVelocity_norm_le value.1
  have low := tensorWork_bound (complexSharpSupportProjection L u) (complexSharpSupportProjection L u) u F test
    (lowLowCap L*‖u‖^3) (by positivity [lowLowCap_nonnegative L]) (fun i j s => low_low_bound u L F i j s)
  have last := tensorWork_bound h h (complexSharpSupportProjection L u) F test
    (thirdCap L*‖u‖*‖NativeWindowSobolevProduct.state h h zero zero hh hh‖)
    (by positivity [thirdCap_nonnegative L]) (fun i j s => third_low_bound h h u zero zero hh hh L F i j s)
  have state : ‖NativeWindowSobolevProduct.state h h zero zero hh hh‖ ≤
      12*Real.sqrt NativeUnheatedRieszKernel.constant*gradientMass value :=
    (NativeWindowSobolevProduct.state_bound h h zero zero hh hh).trans (by
      have paid := mul_le_mul_of_nonneg_left g (Real.sqrt_nonneg NativeUnheatedRieszKernel.constant)
      nlinarith only [paid])
  have third : ‖tensorWork h h (complexSharpSupportProjection L u) F test‖ ≤
      (216*thirdCap L*Real.sqrt NativeUnheatedRieszKernel.constant*‖value.1‖*gradientMass value)*‖test‖ := by
    apply last.trans
    have mass0 : 0 ≤ gradientMass value := tsum_nonneg (gradient_nonnegative value)
    calc
      _ ≤ 18*(thirdCap L*‖value.1‖*(12*Real.sqrt NativeUnheatedRieszKernel.constant*gradientMass value))*‖test‖ := by gcongr <;> positivity [thirdCap_nonnegative L]
      _ = _ := by ring
  have low' : ‖tensorWork (complexSharpSupportProjection L u) (complexSharpSupportProjection L u) u F test‖ ≤
      (18*lowLowCap L*‖value.1‖^3)*‖test‖ := by
    apply low.trans
    have positive := lowLowCap_nonnegative L
    rw [← mul_assoc]
    gcongr
  rw [remainder_sectors]
  apply (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) (le_rfl : ‖tensorWork h h (complexSharpSupportProjection L u) F test‖ ≤ _)).trans ?_)
  rw [norm_mul,show ‖(2:ℂ)‖=2 by norm_num]
  have first := work_bound value regular L F test
  have total := add_le_add (add_le_add (mul_le_mul_of_nonneg_left first (by norm_num : (0:ℝ) ≤ 2)) low') third
  exact total.trans_eq (by ring)

private theorem tensorWork_continuous (first second third : wholePhysical → ComplexVorticityHilbertState)
    (firstC : Continuous first) (secondC : Continuous second) (thirdC : Continuous third)
    (F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    Continuous (fun value => tensorWork (first value) (second value) (third value) F test) := by
  have forceC (wave : IntegerWavevector) (output : Coordinate) :
      Continuous (fun value => force (first value) (second value) wave output) := by
    have flux : Continuous (fun value => NativeHigherTimeJets.mixedFlux (first value) (second value) wave) :=
      continuous_pi fun i => continuous_pi fun j =>
        ((NativeHigherTimeJets.mixedFluxCLM wave i j).continuous.comp firstC).clm_apply secondC
    exact (((NativeCofinalStress.stressPressureCLM wave).continuous.comp flux).const_mul _).neg.mul_const _
  have thirdRow (wave : IntegerWavevector) (input : Coordinate) : Continuous (fun value => third value wave input) :=
    (continuous_apply input).comp ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp thirdC)
  have formC (output input : Coordinate) (scalar : Sequence) :
      Continuous (fun value => trilinear (first value) (second value) (third value) F output input scalar) :=
    continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ((forceC p output).const_mul _).mul (thirdRow q input)
  exact continuous_finsetSum _ fun output _ => continuous_finsetSum _ fun input _ =>
    (formC output input _).add (formC input output _)

theorem remainder_continuous (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    Continuous (fun value : wholePhysical => remainder value L F test) := by
  have mean : Continuous (fun value : wholePhysical => wholeVelocity value.1) := wholeVelocityCLM.continuous.comp continuous_subtype_val
  have projection : Continuous (complexSharpSupportProjection L) := by
    have lip : LipschitzWith 1 (complexSharpSupportProjection L) := LipschitzWith.of_dist_le_mul fun first last => by
      simpa only [NNReal.coe_one,one_mul] using complexSharpSupportProjection_dist_le L first last
    exact lip.continuous
  have highC : Continuous (fun value : wholePhysical => high (wholeVelocity value.1) L) := mean.sub (projection.comp mean)
  exact (tensorWork_continuous _ _ _ mean mean mean F test).sub (tensorWork_continuous _ _ _ highC highC highC F test)

variable {nu : Viscosity}

def sectorBudget (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) : ℝ :=
  2*NativeWindowPressureLowSource.coefficient seed L+
    18*lowLowCap L*(NativeUnifiedCompleteSource.budget seed)^3+
    216*thirdCap L*Real.sqrt NativeUnheatedRieszKernel.constant*NativeUnifiedCompleteSource.budget seed

theorem sectorBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) :
    0 ≤ sectorBudget seed L := by
  have B0 := (norm_nonneg _).trans (NativeUnifiedCompleteSource.source_bound seed 0)
  unfold sectorBudget
  positivity [NativeWindowPressureLowSource.coefficient_nonnegative seed L,lowLowCap_nonnegative L,thirdCap_nonnegative L]

theorem source_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ L F (test : NativeCompleteStressCarrier.Space),
      ‖remainder (physicalSource seed time) L F test‖ ≤ sectorBudget seed L*‖test‖*(1+mass seed time) := by
  filter_upwards [physical_H1_ae seed] with time regular nonnegative L F test
  have paid := remainder_bound (physical seed time nonnegative) (regular nonnegative) L F test
  rw [gradientValue_norm_sq,physical_mass] at paid
  have B := NativeUnheatedSourceWeightedTail.velocity_bound seed time
  have B0 := (norm_nonneg _).trans B
  have G0 := mass_nonnegative seed time
  have cap0 : 0 ≤ ∑ p ∈ L,NativeWindowPressureLowKernel.cap p := Finset.sum_nonneg fun p _ => NativeWindowPressureLowKernel.cap_nonnegative p
  have first0 := NativeWindowPressureLowSource.coefficient_nonnegative seed L
  have low0 := lowLowCap_nonnegative L
  have third0 := thirdCap_nonnegative L
  rw [physicalSource,dif_pos nonnegative]
  apply paid.trans
  have normB : ‖(physical seed time nonnegative).1‖ ≤ NativeUnifiedCompleteSource.budget seed := B
  calc
    _ ≤ (108*Real.sqrt NativeUnheatedRieszKernel.constant*(∑ p ∈ L,NativeWindowPressureLowKernel.cap p)*
          NativeUnifiedCompleteSource.budget seed*((2*Real.pi)^2*mass seed time)+
        18*lowLowCap L*(NativeUnifiedCompleteSource.budget seed)^3+
        216*thirdCap L*Real.sqrt NativeUnheatedRieszKernel.constant*NativeUnifiedCompleteSource.budget seed*mass seed time)*‖test‖ := by
      gcongr
    _ = (2*NativeWindowPressureLowSource.coefficient seed L*mass seed time+
        18*lowLowCap L*(NativeUnifiedCompleteSource.budget seed)^3+
        216*thirdCap L*Real.sqrt NativeUnheatedRieszKernel.constant*NativeUnifiedCompleteSource.budget seed*mass seed time)*‖test‖ := by
      unfold NativeWindowPressureLowSource.coefficient
      ring
    _ ≤ _ := by
      unfold sectorBudget
      have extra : 0 ≤ 2*NativeWindowPressureLowSource.coefficient seed L+
          216*thirdCap L*Real.sqrt NativeUnheatedRieszKernel.constant*NativeUnifiedCompleteSource.budget seed+
          (18*lowLowCap L*(NativeUnifiedCompleteSource.budget seed)^3)*mass seed time := by positivity
      nlinarith only [mul_nonneg extra (norm_nonneg test)]

def window (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (L F : Finset IntegerWavevector)
    (test : NativeCompleteStressCarrier.Space) : ℂ :=
  ∫ shift, remainder (physicalSource seed (time-shift)) L F test ∂NativeForwardWindowPairingReadout.averageMeasure

theorem window_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    Integrable (fun shift => remainder (physicalSource seed (time-shift)) L F test) NativeForwardWindowPairingReadout.averageMeasure := by
  have moved := (physicalSource_measurable seed).comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) time)
  have source := (remainder_continuous L F test).comp_aestronglyMeasurable moved
  have measured := source.mono_ac (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞)))
  have bound := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae (source_bound_ae seed)
  have actual := (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞))).ae_le bound
  have paid := ((integrable_const 1).add (NativeWindowHistoryGradient.weighted_mass_integrable seed time (by linarith))).const_mul (sectorBudget seed L*‖test‖)
  apply paid.mono' measured
  filter_upwards [actual,NativeWindowHistoryGNS.average_support] with shift bounded support
  exact bounded (by linarith) L F test

theorem window_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (inside : time ∈ Icc 0 horizon)
    (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    ‖window seed time L F test‖ ≤ sectorBudget seed L*‖test‖*(1+NativeWindowFiniteStressUniform.kernelBound 0*
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)) := by
  have bound := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae (source_bound_ae seed)
  have actual := (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞))).ae_le bound
  have G := NativeWindowHistoryGradient.weighted_mass_integrable seed time (by linarith [inside.1])
  unfold window
  apply (norm_integral_le_integral_norm _).trans
  have paid := integral_mono_ae (window_integrable seed time inside.1 L F test).norm
    (((integrable_const 1).add G).const_mul (sectorBudget seed L*‖test‖)) (by
      filter_upwards [actual,NativeWindowHistoryGNS.average_support] with shift bounded support
      exact bounded (by linarith [inside.1]) L F test)
  rw [integral_const_mul] at paid
  simp only [Pi.add_apply] at paid
  rw [integral_add (integrable_const 1) G] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (add_le_add (by simp : (∫ _shift : ℝ, (1:ℝ) ∂NativeForwardWindowPairingReadout.averageMeasure) ≤ 1)
    (NativeWindowStressOseenDiffusion.weighted_mass_horizon seed time horizon inside))
    (mul_nonneg (sectorBudget_nonnegative seed L) (norm_nonneg _)))

def sourceWindow (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (L high : Finset IntegerWavevector) : ℂ :=
  window seed time L (integerWaveFrequencyCube radius) (sourceTest seed radius time high)

theorem exists_uniform_small (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (L : Finset IntegerWavevector) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ high : Finset IntegerWavevector, ∀ radius : ℕ, ∀ time : Icc (0:ℝ) horizon,
      ‖sourceWindow seed radius time L high‖ ≤ epsilon := by
  let G := NativeWindowFiniteStressUniform.kernelBound 0*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)
  have G0 : 0 ≤ G := (integral_nonneg (fun shift => mass_nonnegative seed (0-shift))).trans
    (NativeWindowStressOseenDiffusion.weighted_mass_horizon seed 0 horizon ⟨le_rfl,nonnegative⟩)
  let A := sectorBudget seed L*(1+G)
  have A0 : 0 ≤ A := mul_nonneg (sectorBudget_nonnegative seed L) (by positivity)
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

theorem source_trilinear_physical (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (high : Finset IntegerWavevector) (left right last : ComplexVorticityHilbertState) (output input : Coordinate) :
    trilinear left right last (integerWaveFrequencyCube radius) output input (component (sourceTest seed radius time high) output input) =
      inner ℂ (NativeWindowStressHeatBalance.sigma seed (integerWaveFrequencyCube radius) output input time+
        NativeWindowStressOseenLow.lowField high (NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube radius) output input))
      ((polynomial (integerWaveFrequencyCube radius) (fun wave => force left right wave output) 0 0*
        polynomial (integerWaveFrequencyCube radius) (fun wave => last wave input) 0 0).toLp 2 volume ℂ) := by
  apply trilinear_physical
  intro wave
  rw [sourceTest_read seed radius time nonnegative high wave output input]
  simp only [NativeWindowStressHeatBalance.sigma,map_add,map_neg,NativeWindowStressOseenLow.lowField,
    NativeWindowStressHeatEnergy.field,LinearIsometryEquiv.apply_symm_apply,lp.coeFn_add,lp.coeFn_neg,
    Pi.add_apply,Pi.neg_apply,NativeWindowStressHeatEnergy.finiteSequence_apply]
  change -NativeWindowFiniteGramFourier.fourierRead wave _+
    (if wave ∈ high then NativeWindowFiniteGramFourier.fourierRead wave _ else 0) = _
  split_ifs <;> ring

def gradientTail (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (time : ℝ) : ℝ :=
  ∑' wave : NonzeroIntegerWavevector, if wave.1 ∈ L then 0 else NativeUnheatedSourceGradient.row seed wave time

theorem gradientTail_nonnegative (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (time : ℝ) :
    0 ≤ gradientTail seed L time := tsum_nonneg fun wave => by
  split_ifs
  · rfl
  · exact row_nonnegative seed wave time

theorem gradientTail_original (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    gradientTail seed L time = NativeUnheatedStressProduct.gradientMass (high (wholeVelocity (physicalSource seed time).1) L) := by
  rw [physicalSource,dif_pos nonnegative]
  let value := high (wholeVelocity (physical seed time nonnegative).1) L
  have support : Function.support (NativeUnheatedStressProduct.density value) ⊆ {wave | wave ≠ 0} := by
    intro wave member
    by_contra equal
    have zero : wave=0 := not_ne_iff.mp equal
    subst wave
    simp [NativeUnheatedStressProduct.density,integerWaveNormSq] at member
  rw [NativeUnheatedStressProduct.gradientMass,← tsum_subtype_eq_of_support_subset support]
  apply tsum_congr
  intro wave
  rw [high_density]
  split_ifs
  · rfl
  · exact (physical_row seed time nonnegative wave).symm

theorem gradientTail_le (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (time : ℝ)
    (summable : Summable (fun wave => row seed wave time)) : gradientTail seed L time ≤ mass seed time := by
  have bounded (wave : NonzeroIntegerWavevector) : (if wave.1 ∈ L then 0 else row seed wave time) ≤ row seed wave time := by
    split_ifs
    · exact row_nonnegative seed wave time
    · rfl
  have positive (wave : NonzeroIntegerWavevector) : 0 ≤ (if wave.1 ∈ L then 0 else row seed wave time) := by
    split_ifs <;> positivity [row_nonnegative seed wave time]
  exact (summable.of_nonneg_of_le positive bounded).tsum_le_tsum bounded summable

theorem gradientTail_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (L : Finset IntegerWavevector) : Integrable (gradientTail seed L) (volume.restrict (Icc 0 horizon)) := by
  have measurable : AEStronglyMeasurable (gradientTail seed L) (volume.restrict (Icc 0 horizon)) :=
    (AEMeasurable.tsum fun wave => by
      by_cases member : wave.1 ∈ L
      · simp only [if_pos member]
        exact aemeasurable_const
      · simp only [if_neg member]
        exact (row_integrable seed wave horizon).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  apply (mass_integrable seed horizon nonnegative).mono' measurable
  filter_upwards [row_summable_ae_on seed horizon nonnegative] with time summable
  rw [Real.norm_of_nonneg (gradientTail_nonnegative seed L time)]
  exact gradientTail_le seed L time summable

theorem gradientTail_integral_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon, gradientTail seed (integerWaveFrequencyCube radius) time) atTop (𝓝 0) := by
  have point : ∀ᵐ time ∂volume.restrict (Icc 0 horizon),
      Tendsto (fun radius => gradientTail seed (integerWaveFrequencyCube radius) time) atTop (𝓝 0) := by
    filter_upwards [row_summable_ae_on seed horizon nonnegative] with time summable
    have entries (wave : NonzeroIntegerWavevector) :
        Tendsto (fun radius => if wave.1 ∈ integerWaveFrequencyCube radius then (0:ℝ) else row seed wave time) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [integerWave_eventually_mem_frequencyCube wave.1] with radius member
      exact (if_pos member).symm
    have bounded : ∀ᶠ radius in atTop, ∀ wave : NonzeroIntegerWavevector,
        ‖if wave.1 ∈ integerWaveFrequencyCube radius then (0:ℝ) else row seed wave time‖ ≤ row seed wave time :=
      Eventually.of_forall fun radius wave => by
        split_ifs
        · simpa only [norm_zero] using row_nonnegative seed wave time
        · exact (Real.norm_of_nonneg (row_nonnegative seed wave time)).le
    simpa only [gradientTail,tsum_zero] using tendsto_tsum_of_dominated_convergence summable entries bounded
  have limit := tendsto_integral_of_dominated_convergence (mass seed)
    (fun radius => (gradientTail_integrable seed horizon nonnegative (integerWaveFrequencyCube radius)).aestronglyMeasurable)
    (mass_integrable seed horizon nonnegative) (fun radius => by
      filter_upwards [row_summable_ae_on seed horizon nonnegative] with time summable
      rw [Real.norm_of_nonneg (gradientTail_nonnegative seed _ time)]
      exact gradientTail_le seed _ time summable) point
  simpa only [integral_zero] using limit

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
end SaturationMonoid.NavierStokes.NativeWindowPressureLowInputs
