import H0mework.NavierStokes.WindowStressHeat.OseenDiffusion

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowStressOseenLow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativePhysicalGradient NativeEndpointVelocityCarrier
open NativeWindowFiniteGramFourier NativeWindowStressHeatSource NativeWindowStressHeatTime
open NativeUnheatedStressPairEvolution
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def pairBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ := 3*NativeUnifiedCompleteSource.budget seed^2

theorem pair_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) (wave : IntegerWavevector) :
    ‖fourierRead wave (product seed F output input time)‖ ≤ pairBudget seed := by
  simp only [product,field_original]
  change ‖fourierRead wave (pairRead F output input (NativeUnifiedCompleteSource.source seed time))‖ ≤ _
  rw [pair_fourier F _ (complexSharpSupportProjection_reality _ _ closed
    (wholeVelocity_reality _ (NativeCompletePairedAction.source seed time).reality)),norm_neg,NativeCompleteStressBilinear.mixed_read]
  apply (NativeHigherTimeJets.mixedFlux_norm_le _ _ wave output input).trans
  have source := ((NativeWindowStressOseenDiffusion.projection_bound F _).trans (wholeVelocity_norm_le _)).trans
    ((WithLp.norm_fst_le _ (NativeUnifiedCompleteSource.source seed time)).trans (NativeUnifiedCompleteSource.source_bound seed time))
  have sq := pow_le_pow_left₀ (norm_nonneg _) source 2
  unfold pairBudget
  nlinarith only [sq]

def jetBudget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) : ℝ :=
  NativeWindowFiniteStressUniform.kernelBound order*pairBudget seed

theorem jet_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F)
    (output input : Coordinate) (order : ℕ) (wave : IntegerWavevector) :
    ‖fourierRead wave (jet seed F output input order time)‖ ≤ jetBudget seed order := by
  have paid := ((product_ac seed F output input (time+1) (time+2) (by linarith) (by linarith)).continuousOn.intervalIntegrable
    (μ := volume)).continuousOn_smul (kernelWeight_continuous order time 0).continuousOn
  change ‖fourierRead wave (∫ shift, NativeForwardWindowJets.kernelJet order shift • product seed F output input (time-shift))‖ ≤ _
  rw [kernel_integral,← (fourierRead wave).intervalIntegral_comp_comm paid]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (by
    intro sample _
    rw [map_smul,norm_smul]
    have kernel : ‖kernelWeight order time 0 sample‖ ≤ NativeWindowFiniteStressUniform.kernelBound order := by
      simpa only [kernelWeight,zero_add] using NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)
    exact mul_le_mul kernel (pair_bound seed sample F closed output input wave) (norm_nonneg _)
      (NativeWindowFiniteStressUniform.kernelBound_positive order).le)).trans_eq ?_
  simp only [jetBudget,show time+2-(time+1)=(1:ℝ) by ring,abs_one,mul_one]

def complexCoefficient (wave : IntegerWavevector) : C(Torus,ℂ) →L[ℂ] ℂ :=
  ((lp.evalCLM ℂ (fun _ : IntegerWavevector => ℂ) 2 wave).comp
    (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ)

theorem polynomial_coefficient (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ)
    (direction : Coordinate) (order : ℕ) (wave : IntegerWavevector) :
    complexCoefficient wave (polynomial F a direction order) =
      if wave ∈ F then multiplier wave direction^order*a wave else 0 := by
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr ((polynomial F a direction order).toLp 2 volume ℂ) wave = _
  rw [polynomial_field,NativeWindowStressHeatEnergy.field,LinearIsometryEquiv.apply_symm_apply]
  simp only [NativeWindowStressHeatEnergy.finiteJet,NativeWindowStressHeatEnergy.finiteSequence,lp.coeFn_sum,Finset.sum_apply,
    lp.coeFn_single,Finset.sum_pi_single]

theorem stressJet_coefficient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (direction output input : Coordinate) (wave : IntegerWavevector) :
    fourierRead wave ((Complex.reCLM.compLeftContinuous ℝ Torus) (stressJet seed time F direction 2 output input)) =
      multiplier wave direction^2*fourierRead wave (stress seed time F output input) := by
  have real : (Complex.ofRealCLM.compLeftContinuous ℝ Torus)
      ((Complex.reCLM.compLeftContinuous ℝ Torus) (stressJet seed time F direction 2 output input)) =
      stressJet seed time F direction 2 output input := by
    ext point
    obtain ⟨x,rfl⟩ := circle_surjective point
    change (((stressJet seed time F direction 2 output input (NativeFullOrderSynthesis.circlePoint x)).re : ℝ) : ℂ) = _
    rw [stressJet_second seed time F closed direction output input x,Complex.ofReal_re]
  change complexCoefficient wave ((Complex.ofRealCLM.compLeftContinuous ℝ Torus)
    ((Complex.reCLM.compLeftContinuous ℝ Torus) (stressJet seed time F direction 2 output input))) = _
  rw [real,stressJet,polynomial_coefficient]
  split_ifs with inside
  · rfl
  · rw [← NativeWindowFiniteGramFourier.coefficients,coefficients_supported seed time F closed wave inside output input,mul_zero]

theorem laplacian_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F)
    (output input : Coordinate) (wave : IntegerWavevector) :
    ‖fourierRead wave (laplacian seed time F output input)‖ ≤
      (2*Real.pi)^2*integerWaveNormSq wave*jetBudget seed 0 := by
  simp only [laplacian,map_sum,stressJet_coefficient seed time F closed]
  apply (norm_sum_le _ _).trans
  have bound : ‖fourierRead wave (stress seed time F output input)‖ ≤ jetBudget seed 0 := by
    rw [← jet_zero]
    exact jet_bound seed time nonnegative F closed output input 0 wave
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun direction _ => mul_le_mul_of_nonneg_left bound (sq_nonneg ‖multiplier wave direction‖))
  simp only [← Finset.sum_mul,multiplier_sum_norm_sq] at paid
  simpa only [norm_mul,norm_pow,← Finset.sum_mul,multiplier_sum_norm_sq] using paid

def rowBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (wave : IntegerWavevector) : ℝ :=
  jetBudget seed 1+nu.coeff*((2*Real.pi)^2*integerWaveNormSq wave*jetBudget seed 0)+
    (2*nu.coeff)*NativeWindowStressOseenDiffusion.budget seed horizon

theorem nonlinear_coefficient_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (inside : time ∈ Icc 0 horizon) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) (wave : IntegerWavevector) :
    ‖fourierRead wave (NativeWindowStressHeatBalance.nonlinearWindow seed time F output input)‖ ≤ rowBudget seed horizon wave := by
  have actual := congrArg (fourierRead wave) (NativeWindowStressHeatBalance.jet_generator seed time inside.1 F closed output input)
  simp only [map_neg,map_add,heat,map_smul] at actual
  have solved : fourierRead wave (NativeWindowStressHeatBalance.nonlinearWindow seed time F output input) =
      -fourierRead wave (jet seed F output input 1 time)+nu.coeff • fourierRead wave (laplacian seed time F output input)-
        (2*nu.coeff) • fourierRead wave (diffusion seed time F output input) := by
    rw [neg_smul] at actual
    linear_combination -actual
  rw [solved]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  rw [norm_neg,norm_smul,norm_smul,Real.norm_of_nonneg nu.coeff_pos.le,
    Real.norm_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) nu.coeff_pos.le)]
  exact add_le_add (add_le_add (jet_bound seed time inside.1 F closed output input 1 wave)
    (mul_le_mul_of_nonneg_left (laplacian_bound seed time inside.1 F closed output input wave) nu.coeff_pos.le))
    (mul_le_mul_of_nonneg_left (NativeWindowStressOseenDiffusion.diffusion_bound seed time horizon inside F closed output input wave)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) nu.coeff_pos.le))

def lowField (L : Finset IntegerWavevector) (field : C(Torus,ℝ)) : ScalarField :=
  NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteSequence L (fun wave => fourierRead wave field))

theorem lowField_pairing (L : Finset IntegerWavevector) (first last : C(Torus,ℝ)) :
    inner ℝ (lowField L first) (physical last) =
      (∑ wave ∈ L, star (fourierRead wave first)*fourierRead wave last).re := by
  have real : inner ℝ (lowField L first) (physical last) = (inner ℂ (lowField L first) (physical last)).re := by
    rw [L2.inner_def,L2.inner_def]
    exact integral_re (L2.integrable_inner _ _)
  rw [real]
  congr 1
  have moved := (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.inner_map_map (lowField L first) (physical last)
  rw [← moved,lowField,NativeWindowStressHeatEnergy.field,LinearIsometryEquiv.apply_symm_apply,
    NativeWindowStressHeatEnergy.finiteSequence,sum_inner]
  apply Finset.sum_congr rfl
  intro wave _
  rw [lp.inner_single_left,RCLike.inner_apply]
  change fourierRead wave last*star (fourierRead wave first) = _
  exact mul_comm _ _

def lowWork (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F L : Finset IntegerWavevector) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate, inner ℝ (-lowField L (stress seed time F output input))
    (physical (NativeWindowStressHeatBalance.nonlinearWindow seed time F output input))

def workBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (L : Finset IntegerWavevector) : ℝ :=
  9*jetBudget seed 0*(∑ wave ∈ L, rowBudget seed horizon wave)

theorem low_work_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (inside : time ∈ Icc 0 horizon)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (L : Finset IntegerWavevector) :
    ‖lowWork seed time F L‖ ≤ workBudget seed horizon L := by
  have row (output input : Coordinate) :
      ‖inner ℝ (-lowField L (stress seed time F output input))
        (physical (NativeWindowStressHeatBalance.nonlinearWindow seed time F output input))‖ ≤
        jetBudget seed 0*(∑ wave ∈ L, rowBudget seed horizon wave) := by
    rw [inner_neg_left,norm_neg,lowField_pairing]
    rw [Real.norm_eq_abs]
    apply (Complex.abs_re_le_norm _).trans
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro wave _
    rw [norm_mul,norm_star]
    have stressBound : ‖fourierRead wave (stress seed time F output input)‖ ≤ jetBudget seed 0 := by
      rw [← jet_zero]
      exact jet_bound seed time inside.1 F closed output input 0 wave
    exact mul_le_mul stressBound (nonlinear_coefficient_bound seed time horizon inside F closed output input wave)
      (norm_nonneg _) ((norm_nonneg _).trans stressBound)
  unfold lowWork
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun output _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun input _ => row output input)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,workBudget]
  ring

def highWork (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F L : Finset IntegerWavevector) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate,
    inner ℝ (NativeWindowStressHeatBalance.sigma seed F output input time+lowField L (stress seed time F output input))
      (physical (NativeWindowStressHeatBalance.nonlinearWindow seed time F output input))

theorem full_work_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F L : Finset IntegerWavevector) :
    NativeWindowStressHeatBalance.nonlinearWork seed time F = lowWork seed time F L+highWork seed time F L := by
  simp only [NativeWindowStressHeatBalance.nonlinearWork,lowWork,highWork,inner_add_left,inner_neg_left,Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  ring

theorem exists_uniform_low_work_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) (L : Finset IntegerWavevector) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ radius : ℕ, ∀ time : Icc (0:ℝ) horizon,
      ‖lowWork seed time (integerWaveFrequencyCube radius) L‖ ≤ C := by
  refine ⟨workBudget seed horizon L,?_,fun radius time =>
    low_work_bound seed time horizon time.property _ (cube_closed radius) L⟩
  exact (norm_nonneg _).trans (low_work_bound seed 0 horizon ⟨le_rfl,nonnegative⟩ ∅ (by simp) L)

theorem full_work_le_high (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (inside : time ∈ Icc 0 horizon)
    (radius : ℕ) (L : Finset IntegerWavevector) :
    NativeWindowStressHeatBalance.nonlinearWork seed time (integerWaveFrequencyCube radius) ≤
      workBudget seed horizon L+highWork seed time (integerWaveFrequencyCube radius) L := by
  rw [full_work_split]
  exact add_le_add ((le_abs_self _).trans (low_work_bound seed time horizon inside _ (cube_closed radius) L)) le_rfl

open SourceGeneratedNativeResponseDisposition
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem work_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (F L : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    (lowWork seed (step.2.clockAdvance+time) F L,highWork seed (step.2.clockAdvance+time) F L) =
      (lowWork step.1 time F L,highWork step.1 time F L) := by
  simp only [lowWork,highWork,NativeWindowStressHeatBalance.sigma,stress_next seed step generated time nonnegative,
    NativeWindowStressHeatBalance.nonlinearWindow_next seed step generated time nonnegative F closed]

end
end SaturationMonoid.NavierStokes.NativeWindowStressOseenLow
