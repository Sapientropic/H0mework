import H0mework.NavierStokes.WindowEnergyPreparation.Field

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowStressPreparationWrite
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeCompleteStressAction
open NativeWindowStressHeatTime (field product jet)
open NativeWindowStressPreparationField (rate fullRate)
open NativeForwardWindowJets NativeUnheatedIntegralBilinear NativeUnheatedPairGlobalEvolution
open NativeUnheatedStressPairEvolution NativeUnheatedPairGlobalWindow
noncomputable section
variable {nu : Viscosity}

def pairRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  rate seed F output time*field seed F input time+field seed F output time*rate seed F input time

def fullPairRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  fullRate seed F output time*field seed F input time+field seed F output time*fullRate seed F input time

theorem pair_correction (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : pairRate seed F output input time = fullPairRate seed F output input time-
      NativeWindowPreparationWrite.inactive time • fullPairRate seed F output input 0 := by
  unfold pairRate
  simp only [NativeWindowStressPreparationField.rate_correction]
  by_cases before : time ≤ 0
  · simp [NativeWindowPreparationWrite.inactive,before,fullPairRate,
      NativeWindowStressPreparationField.field_nonpositive seed F input time before,
      NativeWindowStressPreparationField.field_nonpositive seed F output time before,
      NativeWindowStressPreparationField.fullRate_nonpositive seed F input time before,
      NativeWindowStressPreparationField.fullRate_nonpositive seed F output time before]
  · simp [NativeWindowPreparationWrite.inactive,before,fullPairRate]

theorem product_ac (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (a b : ℝ) : AbsolutelyContinuousOnInterval (product seed F output input) a b := by
  have actual := diagonal_ac ((ContinuousLinearMap.mul ℝ C(Torus,ℝ)).bilinearComp
    (NativeWindowStressPreparationField.read F output) (NativeWindowStressPreparationField.read F input))
    (NativeWindowPreparationAction.state_lipschitz seed).lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  simpa only [product,ContinuousLinearMap.bilinearComp_apply,
    ← NativeWindowStressPreparationField.field_read] using! actual

theorem product_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) : ∀ᵐ time : ℝ,
      HasDerivAt (product seed F output input) (pairRate seed F output input time) time := by
  filter_upwards [NativeWindowStressPreparationField.field_derivative seed F output,
    NativeWindowStressPreparationField.field_derivative seed F input] with time first last
  exact first.mul last

theorem pairRate_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (a b : ℝ) : IntervalIntegrable (pairRate seed F output input) volume a b :=
  ((NativeWindowStressPreparationField.rate_integrable seed F output a b).mul_continuousOn
    (NativeWindowStressPreparationField.field_lipschitz seed F input).continuous.continuousOn).add
    ((NativeWindowStressPreparationField.rate_integrable seed F input a b).continuousOn_mul
      (NativeWindowStressPreparationField.field_lipschitz seed F output).continuous.continuousOn)

theorem fullPairRate_original_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) : ∀ᵐ time : ℝ, 0 < time →
      fullPairRate seed F output input time = NativeWindowStressHeatTime.productRate seed F output input time := by
  filter_upwards [NativeWindowStressPreparationField.fullRate_original_ae seed F output,
    NativeWindowStressPreparationField.fullRate_original_ae seed F input] with time first last positive
  simp only [fullPairRate,NativeWindowStressHeatTime.productRate,first positive,last positive]

theorem jet_clipped_rate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : jet seed F output input 1 time =
      ∫ actual in time+1..time+2, kernelWeight 0 time 0 actual • pairRate seed F output input actual := by
  have base := (product_ac seed F output input (time+1) (time+2)).continuousOn.intervalIntegrable (μ := volume)
  have p (n : ℕ) := base.continuousOn_smul (kernelWeight_continuous n time 0).continuousOn
  have q := (pairRate_integrable seed F output input (time+1) (time+2)).continuousOn_smul
    (kernelWeight_continuous 0 time 0).continuousOn
  have written : kernelWeight 0 time 0 (time+2) • product seed F output input (time+2)-
      kernelWeight 0 time 0 (time+1) • product seed F output input (time+1) =
      ∫ actual in time+1..time+2, kernelWeight 0 time 0 actual • pairRate seed F output input actual-
        kernelWeight 1 time 0 actual • product seed F output input actual := by
    apply integral_of_ac_derivative (E := C(Torus,ℝ))
      (fun actual => kernelWeight 0 time 0 actual • product seed F output input actual)
      (fun actual => kernelWeight 0 time 0 actual • pairRate seed F output input actual-
        kernelWeight 1 time 0 actual • product seed F output input actual)
    · simpa only [Pi.smul_apply] using!
        (kernel_ac 0 time 0 (time+1) (time+2)).smul (product_ac seed F output input (time+1) (time+2))
    · exact q.sub (p 1)
    · filter_upwards [product_derivative seed F output input] with actual generated _
      convert! (kernelWeight_hasDerivAt 0 time 0 actual).smul generated using 1
      simp only [neg_smul]
      abel
  have left : kernelWeight 0 time 0 (time+1) = 0 := by
    simp only [kernelWeight,zero_add,show time-(time+1) = -1 by ring,kernelJet_right_zero]
  have right : kernelWeight 0 time 0 (time+2) = 0 := by
    simp only [kernelWeight,zero_add,show time-(time+2) = -2 by ring,kernelJet_left_zero]
  simp only [left,right,zero_smul,sub_self] at written
  rw [intervalIntegral.integral_sub q (p 1)] at written
  change (∫ shift : ℝ, kernelJet 1 shift • product seed F output input (time-shift)) = _
  rw [NativeWindowStressHeatTime.kernel_integral]
  exact (sub_eq_zero.mp written.symm).symm

theorem pairRate_locallyIntegrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) : LocallyIntegrable (pairRate seed F output input) (volume : Measure ℝ) := by
  intro time
  refine ⟨Icc (time-1) (time+1),Icc_mem_nhds (by linarith) (by linarith),?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : time-1 ≤ time+1)).mp
    (pairRate_integrable seed F output input (time-1) (time+1))

theorem jet_writer (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : jet seed F output input 1 time =
      (∫ shift : ℝ, NativeForwardWindowSource.kernel shift • fullPairRate seed F output input (time-shift))-
        NativeWindowPreparationWrite.fraction time • fullPairRate seed F output input 0 := by
  have clipped : Integrable (fun shift : ℝ => NativeForwardWindowSource.kernel shift •
      pairRate seed F output input (time-shift)) :=
    NativeForwardWindowSource.kernel_compact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      NativeForwardWindowSource.kernel_smooth.continuous (pairRate_locallyIntegrable seed F output input) time
  have correction := (NativeWindowPreparationWrite.fraction_integrable time).smul_const
    (fullPairRate seed F output input 0)
  have pointwise (shift : ℝ) : NativeForwardWindowSource.kernel shift • fullPairRate seed F output input (time-shift) =
      NativeForwardWindowSource.kernel shift • pairRate seed F output input (time-shift)+
        (NativeForwardWindowSource.kernel shift*NativeWindowPreparationWrite.inactive (time-shift)) •
          fullPairRate seed F output input 0 := by
    rw [pair_correction,smul_sub,smul_smul,sub_add_cancel]
  have actual : (∫ shift : ℝ, NativeForwardWindowSource.kernel shift • fullPairRate seed F output input (time-shift)) =
      jet seed F output input 1 time+NativeWindowPreparationWrite.fraction time • fullPairRate seed F output input 0 := by
    simp_rw [pointwise]
    rw [integral_add clipped correction,integral_smul_const]
    have same : (∫ shift : ℝ, NativeForwardWindowSource.kernel shift • pairRate seed F output input (time-shift)) =
        jet seed F output input 1 time := by
      rw [jet_clipped_rate]
      simpa only [kernelJet,iteratedDeriv_zero] using
        NativeWindowStressHeatTime.kernel_integral (pairRate seed F output input) 0 time
    rw [same]
    rfl
  rw [actual]
  abel

theorem stress_generator (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) :
    HasDerivAt (fun actual => NativeWindowFiniteGramFourier.stress seed actual F output input)
      ((∫ shift : ℝ, NativeForwardWindowSource.kernel shift • fullPairRate seed F output input (time-shift))-
        NativeWindowPreparationWrite.fraction time • fullPairRate seed F output input 0) time := by
  have generated := NativeWindowStressHeatTime.jet_hasDerivAt seed F output input 0 time
  have same : jet seed F output input 0 = fun actual => NativeWindowFiniteGramFourier.stress seed actual F output input := by
    funext actual
    exact NativeWindowStressHeatTime.jet_zero seed F output input actual
  rw [same] at generated
  simpa only [zero_add,jet_writer] using generated

theorem writer_after_preparation (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) (after : -1 ≤ time) : jet seed F output input 1 time =
      ∫ shift : ℝ, NativeForwardWindowSource.kernel shift • fullPairRate seed F output input (time-shift) := by
  rw [jet_writer,NativeWindowPreparationWrite.fraction_after time after,zero_smul,sub_zero]

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem writer_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    ((∫ shift : ℝ, NativeForwardWindowSource.kernel shift • fullPairRate seed F output input
      (response.2.clockAdvance+time-shift))-
        NativeWindowPreparationWrite.fraction (response.2.clockAdvance+time) • fullPairRate seed F output input 0) =
      ((∫ shift : ℝ, NativeForwardWindowSource.kernel shift • fullPairRate response.1 F output input (time-shift))-
        NativeWindowPreparationWrite.fraction time • fullPairRate response.1 F output input 0) := by
  rw [← jet_writer,← jet_writer]
  exact NativeWindowStressHeatTime.jet_next seed F output input 1 response generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeWindowStressPreparationWrite
