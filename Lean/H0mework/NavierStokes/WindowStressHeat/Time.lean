import H0mework.NavierStokes.WindowStressHeat.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowStressHeatTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeCompleteStressAction NativeResolventCompactness
open NativeUnheatedGlobalNegativeOne NativeUnheatedIntegralBilinear NativeUnheatedPairGlobalEvolution
open NativeForwardWindowJets NativeForwardWindowSource NativeForwardWindowPairingReadout
noncomputable section
variable {nu : Viscosity}

def read (F : Finset IntegerWavevector) (coordinate : Coordinate) : State →L[ℝ] C(Torus,ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ Torus).comp
    (∑ wave ∈ F, ((ContinuousLinearMap.toSpanSingleton ℂ (UnitAddTorus.mFourier wave)).restrictScalars ℝ).comp
      (NativeUnheatedTriadRows.decode wave coordinate))

def field (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (coordinate : Coordinate)
    (time : ℝ) : C(Torus,ℝ) := read F coordinate (state seed time)

def fieldRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (coordinate : Coordinate)
    (time : ℝ) : C(Torus,ℝ) := read F coordinate (rate seed time)

def fieldAction (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (coordinate : Coordinate)
    (time : ℝ) : C(Torus,ℝ) := read F coordinate (NativeUnheatedSourceWeightedTail.nonlinear seed time)

theorem field_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (time : ℝ) : field seed F coordinate time =
      NativeWindowFiniteGramFourier.read F coordinate (NativeUnifiedCompleteSource.source seed time) := by
  unfold field read NativeWindowFiniteGramFourier.read NativeWindowFiniteGramFourier.complexRead
  simp only [ContinuousLinearMap.comp_apply,sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro wave _
  rw [show NativeUnheatedTriadRows.decode wave coordinate (state seed time) =
      velocityRead wave coordinate (NativeUnifiedCompleteSource.source seed time) from
    NativeUnheatedTriadRows.velocity_original seed time wave coordinate]

theorem field_ac (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    AbsolutelyContinuousOnInterval (field seed F coordinate) a b := by
  apply dominated (state_ac seed a b a0 b0) ‖read F coordinate‖
  intro x _ y _
  rw [dist_eq_norm,dist_eq_norm]
  simpa only [field,← map_sub] using (read F coordinate).le_opNorm (state seed x-state seed y)

theorem field_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) : ∀ᵐ time : ℝ, 0 < time →
    HasDerivAt (field seed F coordinate) (fieldRate seed F coordinate time) time := by
  filter_upwards [source_hasDerivAt_ae seed] with time actual positive
  exact (read F coordinate).hasFDerivAt.comp_hasDerivAt time (actual positive)

theorem fieldRate_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    IntervalIntegrable (fieldRate seed F coordinate) volume a b :=
  ⟨(read F coordinate).integrable_comp (rate_intervalIntegrable seed a b a0 b0).1,
    (read F coordinate).integrable_comp (rate_intervalIntegrable seed a b a0 b0).2⟩

def product (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) := field seed F output time*field seed F input time

def productRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  fieldRate seed F output time*field seed F input time+field seed F output time*fieldRate seed F input time

def nonlinearPair (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  fieldAction seed F output time*field seed F input time+field seed F output time*fieldAction seed F input time

theorem product_ac (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    AbsolutelyContinuousOnInterval (product seed F output input) a b :=
  diagonal_ac ((ContinuousLinearMap.mul ℝ C(Torus,ℝ)).bilinearComp (read F output) (read F input))
    (state_ac seed a b a0 b0)

theorem product_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) : ∀ᵐ time : ℝ, 0 < time →
      HasDerivAt (product seed F output input) (productRate seed F output input time) time := by
  filter_upwards [field_hasDerivAt_ae seed F output,field_hasDerivAt_ae seed F input] with time left right positive
  exact (left positive).mul (right positive)

theorem productRate_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    IntervalIntegrable (productRate seed F output input) volume a b :=
  ((fieldRate_integrable seed F output a b a0 b0).mul_continuousOn (field_ac seed F input a b a0 b0).continuousOn).add
    ((fieldRate_integrable seed F input a b a0 b0).continuousOn_mul (field_ac seed F output a b a0 b0).continuousOn)

theorem product_locallyIntegrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) : LocallyIntegrable (product seed F output input) := by
  have left := (NativeWindowFiniteGramFourier.read F output).continuous.comp_aestronglyMeasurable
    (NativeUnifiedCompleteSource.source_measurable seed)
  have right := (NativeWindowFiniteGramFourier.read F input).continuous.comp_aestronglyMeasurable
    (NativeUnifiedCompleteSource.source_measurable seed)
  have bounded : MemLp (product seed F output input) ∞ (volume : Measure ℝ) := by
    apply memLp_top_of_bound (by
      unfold product
      simp only [field_original]
      exact left.mul right)
      (‖NativeWindowFiniteGramFourier.read F output‖*‖NativeWindowFiniteGramFourier.read F input‖*NativeUnifiedCompleteSource.budget seed^2)
    filter_upwards with time
    have bound (coordinate : Coordinate) : ‖field seed F coordinate time‖ ≤
        ‖NativeWindowFiniteGramFourier.read F coordinate‖*NativeUnifiedCompleteSource.budget seed := by
      rw [field_original]
      exact ((NativeWindowFiniteGramFourier.read F coordinate).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (NativeUnifiedCompleteSource.source_bound seed time) (norm_nonneg _))
    exact (norm_mul_le _ _).trans ((mul_le_mul (bound output) (bound input) (norm_nonneg _)
      ((norm_nonneg _).trans (bound output))).trans_eq (by ring))
  exact bounded.locallyIntegrable le_top

def jet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (output input : Coordinate)
    (order : ℕ) : ℝ → C(Torus,ℝ) :=
  kernelJet order ⋆[ContinuousLinearMap.lsmul ℝ ℝ] product seed F output input

theorem jet_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : jet seed F output input 0 time =
      NativeWindowFiniteGramFourier.stress seed time F output input := by
  rw [NativeWindowFiniteGramFourier.stress,density_integral]
  change (∫ shift, kernelJet 0 shift • product seed F output input (time-shift)) = _
  simp only [kernelJet,iteratedDeriv_zero,product,field_original,NativeWindowFiniteGramFourier.pairRead]

theorem jet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (order : ℕ) (time : ℝ) :
    HasDerivAt (jet seed F output input order) (jet seed F output input (order+1) time) time := by
  have generated := (kernelJet_compact order).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth order).of_le (by simp)) (product_locallyIntegrable seed F output input) time
  simpa only [jet,kernelJet,iteratedDeriv_succ] using generated

open NativeUnheatedStressPairEvolution NativeUnheatedPairGlobalWindow

theorem kernel_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (order : ℕ) (time : ℝ) :
    (∫ shift : ℝ, kernelJet order shift • f (time-shift)) =
      ∫ actual in time+1..time+2, kernelWeight order time 0 actual • f actual := by
  have support : (∫ shift : ℝ, kernelJet order shift • f (time-shift)) =
      ∫ shift in Icc (-2 : ℝ) (-1), kernelJet order shift • f (time-shift) := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with shift
    by_cases inside : shift ∈ Icc (-2 : ℝ) (-1)
    · rw [indicator_of_mem inside]
    · rw [indicator_of_notMem inside]
      have zero : kernelJet order shift = 0 := by
        by_contra nonzero
        exact inside (NativeUnheatedWindowJensen.kernel_support order shift nonzero)
      rw [zero,zero_smul]
  rw [support,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ -1)]
  simpa only [kernelWeight,zero_add,sub_sub_cancel,sub_neg_eq_add] using!
    (intervalIntegral.integral_comp_sub_left
      (f := fun actual => kernelWeight order time 0 actual • f actual) (a := -2) (b := -1) time)

theorem jet_rate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) (nonnegative : 0 ≤ time) :
    jet seed F output input 1 time =
      ∫ actual in time+1..time+2, kernelWeight 0 time 0 actual • productRate seed F output input actual := by
  have a0 : 0 ≤ time+1 := by linarith
  have b0 : 0 ≤ time+2 := by linarith
  have base := (product_ac seed F output input (time+1) (time+2) a0 b0).continuousOn.intervalIntegrable (μ := volume)
  have p (n : ℕ) := base.continuousOn_smul (kernelWeight_continuous n time 0).continuousOn
  have q := (productRate_integrable seed F output input (time+1) (time+2) a0 b0).continuousOn_smul
    (kernelWeight_continuous 0 time 0).continuousOn
  have written : kernelWeight 0 time 0 (time+2) • product seed F output input (time+2)-
      kernelWeight 0 time 0 (time+1) • product seed F output input (time+1) =
      ∫ actual in time+1..time+2, kernelWeight 0 time 0 actual • productRate seed F output input actual-
        kernelWeight 1 time 0 actual • product seed F output input actual := by
    apply integral_of_ac_derivative (E := C(Torus,ℝ))
      (fun actual => kernelWeight 0 time 0 actual • product seed F output input actual)
      (fun actual => kernelWeight 0 time 0 actual • productRate seed F output input actual-
        kernelWeight 1 time 0 actual • product seed F output input actual)
    · simpa only [Pi.smul_apply] using!
        (kernel_ac 0 time 0 (time+1) (time+2)).smul (product_ac seed F output input (time+1) (time+2) a0 b0)
    · exact q.sub (p 1)
    ·
      filter_upwards [product_hasDerivAt_ae seed F output input] with actual generated inside
      have positive : 0 < actual := by
        rw [uIcc_of_le (by linarith : time+1 ≤ time+2)] at inside
        linarith [inside.1]
      convert! (kernelWeight_hasDerivAt 0 time 0 actual).smul (generated positive) using 1
      simp only [neg_smul]
      abel
  have left : kernelWeight 0 time 0 (time+1) = 0 := by
    simp only [kernelWeight,zero_add,show time-(time+1) = -1 by ring,kernelJet_right_zero]
  have right : kernelWeight 0 time 0 (time+2) = 0 := by
    simp only [kernelWeight,zero_add,show time-(time+2) = -2 by ring,kernelJet_left_zero]
  simp only [left,right,zero_smul,sub_self] at written
  rw [intervalIntegral.integral_sub q (p 1)] at written
  change (∫ shift : ℝ, kernelJet 1 shift • product seed F output input (time-shift)) = _
  rw [kernel_integral]
  exact (sub_eq_zero.mp written.symm).symm

open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem jet_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (output input : Coordinate) (order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    jet seed F output input order (step.2.clockAdvance+time) = jet step.1 F output input order time := by
  change (∫ shift : ℝ, kernelJet order shift • product seed F output input (step.2.clockAdvance+time-shift)) =
    ∫ shift : ℝ, kernelJet order shift • product step.1 F output input (time-shift)
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernelJet order shift = 0
  · simp only [zero,zero_smul]
  · simp only [product,field_original,add_sub_assoc,NativeUnifiedCompleteSource.source_generated_next seed step generated
      (time-shift) (by linarith [kernelJet_nonpositive order shift zero])]

end
end SaturationMonoid.NavierStokes.NativeWindowStressHeatTime
