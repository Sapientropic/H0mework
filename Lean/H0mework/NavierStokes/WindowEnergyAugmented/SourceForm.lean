import H0mework.NavierStokes.WindowEnergyAugmented.Green
import H0mework.NavierStokes.WindowEnergyJoint.NormalForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedSourceForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativePhysicalFourier NativeCompleteStressAction NativeResolventCompactness
open NativeUnheatedGlobalNegativeOne NativeUnheatedIntegralBilinear NativeUnheatedPairGlobalEvolution
open NativeWindowAugmentedGreen NativeUnheatedStressPairEvolution NativeUnheatedPairGlobalWindow
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {nu : Viscosity}

def spectralForm (nu : Viscosity) (L : Finset IntegerWavevector) : State →L[ℝ] State →L[ℝ] ℝ :=
  ∑ wave ∈ L,∑ coordinate : Coordinate,(1+nu.coeff*integerWaveViscousMultiplier wave) •
    (innerSL ℝ).bilinearComp (NativeUnheatedTriadRows.decode wave coordinate) (NativeUnheatedTriadRows.decode wave coordinate)

def matrixField (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (radius : ℕ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed observation F output input)+
    NativeWindowPressureStrainHistory.correction seed F radius observation output input

theorem matrixField_relative (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (radius : ℕ) (output input : Coordinate) : matrixField seed observation F radius output input=
      -NativeWindowPressureStrainHistory.relative seed F radius observation output input := by
  unfold matrixField NativeWindowPressureStrainHistory.relative NativeWindowStressHeatBalance.sigma
  abel

def matrixRead (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (radius : ℕ) (output input : Coordinate) : C(Torus,ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (matrixField seed observation F radius output input)).comp NativeWindowStressHeatSource.physical

def matrixForm (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (radius : ℕ) : State →L[ℝ] State →L[ℝ] ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,
    ((ContinuousLinearMap.compL ℝ State C(Torus,ℝ) ℝ) (matrixRead seed observation F radius output input)).comp
      ((ContinuousLinearMap.mul ℝ C(Torus,ℝ)).bilinearComp
        (NativeWindowStressHeatTime.read F output) (NativeWindowStressHeatTime.read F input))

def form (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius : ℕ) : State →L[ℝ] State →L[ℝ] ℝ := spectralForm nu L+matrixForm seed observation F radius

def diagonal (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : ℝ := form seed observation L F radius (state seed sample) (state seed sample)

def actualRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : ℝ :=
  form seed observation L F radius (rate seed sample) (state seed sample)+
    form seed observation L F radius (state seed sample) (rate seed sample)

theorem diagonal_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : diagonal seed observation L F radius sample=
      (∑ wave ∈ L,∑ coordinate : Coordinate,(1+nu.coeff*integerWaveViscousMultiplier wave)*
        ‖NativeUnheatedTriadRows.velocity seed sample wave coordinate‖^2)+
      ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (matrixField seed observation F radius output input)
        (NativeWindowStressHeatSource.physical (NativeWindowStressHeatTime.product seed F output input sample)) := by
  simp only [diagonal,form,spectralForm,matrixForm,add_apply,sum_apply,smul_apply,
    ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    smul_eq_mul,NativeWindowStressHeatTime.product,NativeWindowStressHeatTime.field]
  congr 1
  apply Finset.sum_congr rfl
  intro wave _
  apply Finset.sum_congr rfl
  intro coordinate _
  change (1+nu.coeff*integerWaveViscousMultiplier wave)*inner ℝ
    (NativeUnheatedTriadRows.decode wave coordinate (state seed sample))
    (NativeUnheatedTriadRows.decode wave coordinate (state seed sample))=
      (1+nu.coeff*integerWaveViscousMultiplier wave)*‖NativeUnheatedTriadRows.velocity seed sample wave coordinate‖^2
  rw [real_inner_self_eq_norm_sq]
  rfl

theorem diagonal_ac (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    AbsolutelyContinuousOnInterval (diagonal seed observation L F radius) a b :=
  NativeUnheatedIntegralBilinear.diagonal_ac (form seed observation L F radius) (state_ac seed a b a0 b0)

theorem diagonal_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius : ℕ) : ∀ᵐ sample : ℝ,0<sample →
      HasDerivAt (diagonal seed observation L F radius) (actualRate seed observation L F radius sample) sample := by
  filter_upwards [source_hasDerivAt_ae seed] with sample generated positive
  have actual := ((form seed observation L F radius).hasFDerivAt.comp_hasDerivAt sample
    (generated positive)).clm_apply (generated positive)
  simpa only [diagonal,actualRate,Function.comp_def] using! actual

theorem actualRate_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius : ℕ) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    IntervalIntegrable (actualRate seed observation L F radius) volume a b := by
  have source := (state_ac seed a b a0 b0).continuousOn
  obtain ⟨bound,bounded⟩ := (state_ac seed a b a0 b0).exists_bound
  let B:=form seed observation L F radius
  have normed : ∀ sample∈uIcc a b,‖actualRate seed observation L F radius sample‖ ≤
      (2*‖B‖*bound)*‖rate seed sample‖ := by
    intro sample inside
    apply (norm_add_le _ _).trans
    have first := (B.le_opNorm₂ (rate seed sample) (state seed sample)).trans
      (mul_le_mul_of_nonneg_left (bounded sample inside) (mul_nonneg (norm_nonneg B) (norm_nonneg _)))
    have last := (B.le_opNorm₂ (state seed sample) (rate seed sample)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bounded sample inside) (norm_nonneg B)) (norm_nonneg _))
    exact (add_le_add first last).trans_eq (by ring)
  have measured : AEStronglyMeasurable (actualRate seed observation L F radius) (volume.restrict (uIoc a b)) :=
    (B.aestronglyMeasurable_comp₂ (rate_intervalIntegrable seed a b a0 b0).def'.aestronglyMeasurable
      ((source.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)).add
        (B.aestronglyMeasurable_comp₂ ((source.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
          (rate_intervalIntegrable seed a b a0 b0).def'.aestronglyMeasurable)
  apply intervalIntegrable_iff.mpr
  exact (((rate_intervalIntegrable seed a b a0 b0).def'.norm.const_mul (2*‖B‖*bound)).mono' measured
    (by filter_upwards [ae_restrict_mem measurableSet_uIoc] with sample inside; exact normed sample (uIoc_subset_uIcc inside)))

theorem actual_write (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius : ℕ) (a b : ℝ) (a0 : 0<a) (b0 : 0<b) :
    diagonal seed observation L F radius b-diagonal seed observation L F radius a=
      ∫ sample in a..b,actualRate seed observation L F radius sample := by
  apply integral_of_ac_derivative _ _ (diagonal_ac seed observation L F radius a b a0.le b0.le)
    (actualRate_integrable seed observation L F radius a b a0.le b0.le)
  filter_upwards [diagonal_hasDerivAt_ae seed observation L F radius] with sample generated inside
  exact generated ((lt_min a0 b0).trans_le inside.1)

def nonlinearRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : ℝ :=
  form seed observation L F radius (NativeUnheatedSourceWeightedTail.nonlinear seed sample) (state seed sample)+
    form seed observation L F radius (state seed sample) (NativeUnheatedSourceWeightedTail.nonlinear seed sample)

def viscousRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : ℝ :=
  form seed observation L F radius (NativeWindowHistoryGradient.gradientState seed sample) (state seed sample)+
    form seed observation L F radius (state seed sample) (NativeWindowHistoryGradient.gradientState seed sample)

theorem actualRate_split (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) :
    actualRate seed observation L F radius sample=nonlinearRate seed observation L F radius sample-
      nu.coeff*viscousRate seed observation L F radius sample := by
  simp only [actualRate,nonlinearRate,viscousRate,NativeWindowHistoryGradient.gradientState,map_smul,map_sub,
    smul_apply,sub_apply,smul_eq_mul]
  field_simp [nu.coeff_pos.ne']
  ring


theorem viscous_source_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius : ℕ) : ∀ᵐ sample : ℝ,∀ nonnegative : 0 ≤ sample,
      ∃ regular : NativeWholeH1Mixed.H1 (NativeUnheatedSourceGradient.physical seed sample nonnegative),
        viscousRate seed observation L F radius sample=
          form seed observation L F radius (NativeWholeH1Pairing.gradientValue
            (NativeUnheatedSourceGradient.physical seed sample nonnegative) regular) (state seed sample)+
          form seed observation L F radius (state seed sample) (NativeWholeH1Pairing.gradientValue
            (NativeUnheatedSourceGradient.physical seed sample nonnegative) regular) := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with sample generated nonnegative
  refine ⟨generated nonnegative,?_⟩
  simp only [viscousRate,NativeWindowHistoryGradient.gradientState_original seed sample nonnegative (generated nonnegative)]

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (L F : Finset IntegerWavevector) (radius order : ℕ) :
    (∫ sample in observation+1..observation+2,kernelWeight order observation 0 sample • actualRate seed observation L F radius sample)=
      ∫ sample in observation+1..observation+2,kernelWeight (order+1) observation 0 sample • diagonal seed observation L F radius sample := by
  have left0 : 0<observation+1 := by linarith
  have right0 : 0<observation+2 := by linarith
  have base := (diagonal_ac seed observation L F radius (observation+1) (observation+2) left0.le right0.le).continuousOn.intervalIntegrable (μ := volume)
  have p (n : ℕ) := base.continuousOn_smul (kernelWeight_continuous n observation 0).continuousOn
  have q := (actualRate_integrable seed observation L F radius (observation+1) (observation+2) left0.le right0.le).continuousOn_smul
    (kernelWeight_continuous order observation 0).continuousOn
  have written : kernelWeight order observation 0 (observation+2) • diagonal seed observation L F radius (observation+2)-
      kernelWeight order observation 0 (observation+1) • diagonal seed observation L F radius (observation+1)=
      ∫ sample in observation+1..observation+2,kernelWeight order observation 0 sample • actualRate seed observation L F radius sample-
        kernelWeight (order+1) observation 0 sample • diagonal seed observation L F radius sample := by
    apply integral_of_ac_derivative
      (fun sample => kernelWeight order observation 0 sample • diagonal seed observation L F radius sample)
      (fun sample => kernelWeight order observation 0 sample • actualRate seed observation L F radius sample-
        kernelWeight (order+1) observation 0 sample • diagonal seed observation L F radius sample)
      ((kernel_ac order observation 0 (observation+1) (observation+2)).smul
        (diagonal_ac seed observation L F radius (observation+1) (observation+2) left0.le right0.le)) (q.sub (p (order+1)))
    filter_upwards [diagonal_hasDerivAt_ae seed observation L F radius] with sample generated inside
    have sample0 : 0<sample := by
      rw [uIcc_of_le (by linarith : observation+1 ≤ observation+2)] at inside
      linarith [inside.1]
    convert! (kernelWeight_hasDerivAt order observation 0 sample).smul (generated sample0) using 1
    simp only [neg_smul]
    abel
  have left : kernelWeight order observation 0 (observation+1)=0 := by
    simp only [kernelWeight,zero_add,show observation-(observation+1)=(-1:ℝ) by ring,NativeUnheatedPairGlobalWindow.kernelJet_right_zero]
  have right : kernelWeight order observation 0 (observation+2)=0 := by
    simp only [kernelWeight,zero_add,show observation-(observation+2)=(-2:ℝ) by ring,NativeUnheatedPairGlobalWindow.kernelJet_left_zero]
  simp only [left,right,zero_smul,sub_self] at written
  rw [intervalIntegral.integral_sub q (p (order+1))] at written
  exact sub_eq_zero.mp written.symm


open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem form_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (L F : Finset IntegerWavevector) (radius : ℕ) :
    form seed (step.2.clockAdvance+observation) L F radius=form step.1 observation L F radius := by
  simp only [form,matrixForm,matrixRead,matrixField,
    NativeWindowFiniteGramFourier.stress_next seed step generated observation nonnegative F,
    NativeWindowPressureStrainHistory.correction_next seed step generated radius observation nonnegative F]

theorem diagonal_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (observation sample : ℝ)
    (observation0 : 0 ≤ observation) (sample0 : 0 ≤ sample) (L F : Finset IntegerWavevector) (radius : ℕ) :
    diagonal seed (step.2.clockAdvance+observation) L F radius (step.2.clockAdvance+sample)=
      diagonal step.1 observation L F radius sample := by
  rw [diagonal,diagonal,form_next seed step generated observation observation0 L F radius,
    state_next seed step generated sample sample0]

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedSourceForm
