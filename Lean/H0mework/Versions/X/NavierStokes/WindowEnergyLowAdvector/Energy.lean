import H0mework.Versions.X.NavierStokes.WindowEnergyLowAdvector.History

set_option autoImplicit false
open scoped Topology BigOperators ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowLowAdvectorEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativeCompleteStressAction NativeForwardWindowPairingReadout NativePhysicalFourier
open NativeWindowLowAdvectorHistory
noncomputable section
variable {nu : Viscosity}

private theorem bilinear_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (left right : Coordinate → FullSpace →L[ℝ] C(Torus,ℝ)) :
    MemLp (fun times : ℝ × ℝ => ∑ i : Coordinate, left i (NativeUnifiedCompleteSource.source seed (observation-times.1))*
    right i (NativeUnifiedCompleteSource.source seed (observation-times.2))) ∞ jointMeasure := by
  refine memLp_finsetSum (p := ∞) (μ := jointMeasure)
    (f := fun i times => left i (NativeUnifiedCompleteSource.source seed (observation-times.1))*
      right i (NativeUnifiedCompleteSource.source seed (observation-times.2))) Finset.univ ?_
  intro i _
  simpa only [Pi.mul_def] using (right_memLp seed observation (right i)).mul (r := ∞) (left_memLp seed observation (left i))

theorem pair_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) :
    MemLp (pairField seed observation F) ∞ jointMeasure := by
  unfold pairField
  simp only [NativeWindowCrossHistoryAction.pair,NativeWindowCrossHistoryAction.velocity,NativeWindowStressHeatTime.field_original]
  exact bilinear_memLp seed observation (NativeWindowFiniteGramFourier.read F) (NativeWindowFiniteGramFourier.read F)

theorem wedge_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (j : Coordinate) :
    MemLp (wedgeField seed observation F j) ∞ jointMeasure := by
  have left := bilinear_memLp seed observation (NativeWindowStressHeatSource.jetRead F j 1) (NativeWindowFiniteGramFourier.read F)
  have right := bilinear_memLp seed observation (NativeWindowFiniteGramFourier.read F) (NativeWindowStressHeatSource.jetRead F j 1)
  unfold wedgeField
  simpa only [NativeWindowCrossHistoryAction.wedge,NativeWindowCrossHistoryAction.pair,Pi.sub_def,
    NativeWindowCrossHistoryAction.gradient,NativeWindowCrossHistoryAction.velocity,NativeWindowStressHeatTime.field_original] using left.sub right

def lowRelative (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector)
    (times : ℝ × ℝ) : C(Torus,ℝ) := ∑ j : Coordinate,
  (NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) (observation-times.1) j-
    NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) (observation-times.2) j)*wedgeField seed observation F j times

private theorem relative_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F A : Finset IntegerWavevector) :
    MemLp (fun times : ℝ × ℝ => ∑ j : Coordinate,
      (NativeWindowCrossHistoryAction.velocity seed A (observation-times.1) j-
        NativeWindowCrossHistoryAction.velocity seed A (observation-times.2) j)*wedgeField seed observation F j times) ∞ jointMeasure := by
  simp only [NativeWindowCrossHistoryAction.velocity,NativeWindowStressHeatTime.field_original]
  refine memLp_finsetSum (p := ∞) (μ := jointMeasure)
    (f := fun j times => ((NativeWindowFiniteGramFourier.read A j)
        (NativeUnifiedCompleteSource.source seed (observation-times.1))-
      (NativeWindowFiniteGramFourier.read A j)
        (NativeUnifiedCompleteSource.source seed (observation-times.2)))*wedgeField seed observation F j times) Finset.univ ?_
  intro j _
  simpa only [Pi.mul_def,Pi.sub_def] using
    (wedge_memLp seed observation F j).mul (r := ∞)
      ((left_memLp seed observation (NativeWindowFiniteGramFourier.read A j)).sub
        (right_memLp seed observation (NativeWindowFiniteGramFourier.read A j)))

theorem lowRelative_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) :
    MemLp (lowRelative seed observation radius F) ∞ jointMeasure :=
  relative_memLp seed observation F (F ∩ wholeRestartModes radius)

def integrand (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector)
    (times : ℝ × ℝ) : C(Torus,ℝ) := (1/2 : ℝ) • (pairField seed observation F times*lowRelative seed observation radius F times)

theorem integrand_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) :
    Integrable (integrand seed observation radius F) jointMeasure := by
  have paid := ((lowRelative_memLp seed observation radius F).mul (r := ∞) (pair_memLp seed observation F)).const_smul (1/2 : ℝ)
  unfold integrand
  simpa only [Pi.mul_def,Pi.smul_def] using paid.integrable (by norm_num : (1 : ℝ≥0∞) ≤ ∞)

def field (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) : C(Torus,ℝ) :=
  ∫ times, integrand seed observation radius F times ∂jointMeasure

theorem field_apply (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) (point : Torus) :
    field seed observation radius F point = ∫ times, integrand seed observation radius F times point ∂jointMeasure :=
  ((ContinuousMap.evalCLM ℝ point).integral_comp_comm (integrand_integrable seed observation radius F)).symm

def massDensity (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) : C(Torus,ℝ) :=
  ∑ i : Coordinate, ∑ j : Coordinate, NativeWindowFiniteGramFourier.stress seed observation F i j^2

def coefficient (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) : ℝ :=
  3*NativeWindowTimeIncrementSource.lowCap seed radius^2/(4*nu.coeff)

theorem point_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) (point : Torus) :
    |field seed observation radius F point| ≤ nu.coeff*NativeWindowStressHeatSource.interaction seed observation F point+
      coefficient seed radius*massDensity seed observation F point := by
  rw [field_apply]
  change ‖∫ times, integrand seed observation radius F times point ∂jointMeasure‖ ≤ _
  have original : Integrable (fun times => integrand seed observation radius F times point) jointMeasure := by
    simpa only [ContinuousMap.evalCLM_apply] using (ContinuousMap.evalCLM ℝ point).integrable_comp (integrand_integrable seed observation radius F)
  have square := integrable_finsetSum Finset.univ (fun j _ => wedge_square_integrable seed observation F j point)
  have pairSquare := pair_square_integrable seed observation F point
  have upper := integral_mono original.norm ((square.const_mul (nu.coeff/4)).add (pairSquare.const_mul (coefficient seed radius))) (fun times => by
    have source := NativeWindowTimeIncrementSource.low_relative_absorption seed radius (observation-times.1) (observation-times.2) F point
    simpa only [integrand,lowRelative,coefficient,pairField,wedgeField,ContinuousMap.smul_apply,ContinuousMap.mul_apply,Pi.add_apply,
      ContinuousMap.sum_apply,ContinuousMap.sub_apply,smul_eq_mul,Real.norm_eq_abs,mul_assoc] using source)
  rw [integral_add' (square.const_mul (nu.coeff/4)) (pairSquare.const_mul (coefficient seed radius)),integral_const_mul,
    integral_const_mul,pair_square_integral] at upper
  have gradient := mul_le_mul_of_nonneg_left (wedge_square_bound seed observation F point) (show 0 ≤ nu.coeff/4 by positivity [nu.coeff_pos])
  simp only [massDensity,ContinuousMap.sum_apply,ContinuousMap.pow_apply]
  have bounded := (norm_integral_le_integral_norm _).trans upper
  nlinarith only [bounded,gradient]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def work (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) : ℝ :=
  -(∫ point : Torus, field seed observation radius F point)

private theorem continuous_integrable (value : C(Torus,ℝ)) : Integrable value :=
  value.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace value)

theorem massDensity_integral (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) :
    (∫ point : Torus, massDensity seed observation F point) = 2*NativeWindowStressHeatBalance.energy seed F observation := by
  have paid (i j : Coordinate) : Integrable (fun point => NativeWindowFiniteGramFourier.stress seed observation F i j point^2) :=
    continuous_integrable (NativeWindowFiniteGramFourier.stress seed observation F i j^2)
  have row (i j : Coordinate) : (∫ point : Torus, NativeWindowFiniteGramFourier.stress seed observation F i j point^2) =
      ‖NativeWindowStressHeatBalance.sigma seed F i j observation‖^2 := by
    rw [show (fun point => NativeWindowFiniteGramFourier.stress seed observation F i j point^2) =
        (fun point => NativeWindowFiniteGramFourier.stress seed observation F i j point*NativeWindowFiniteGramFourier.stress seed observation F i j point) by ext; ring]
    have same := NativeWindowStressHeatSource.physical_inner (NativeWindowFiniteGramFourier.stress seed observation F i j)
      (NativeWindowFiniteGramFourier.stress seed observation F i j)
    have square := real_inner_self_eq_norm_sq (NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed observation F i j))
    simpa only [NativeWindowStressHeatBalance.sigma,norm_neg] using same.symm.trans square
  simp only [massDensity,ContinuousMap.sum_apply,ContinuousMap.pow_apply]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => paid i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => paid _ j),row]
  simp only [NativeWindowStressHeatBalance.energy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem work_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) :
    work seed observation radius F = -(∫ times : ℝ × ℝ, (∫ point : Torus,
      integrand seed observation radius F times point) ∂jointMeasure) := by
  let mean : C(Torus,ℝ) →L[ℝ] ℝ := (innerSL ℝ (NativeWindowStressHeatSource.physical 1)).comp NativeWindowStressHeatSource.physical
  have read (value : C(Torus,ℝ)) : mean value = ∫ point : Torus, value point := by
    change inner ℝ (NativeWindowStressHeatSource.physical 1) (NativeWindowStressHeatSource.physical value) = _
    simp only [NativeWindowStressHeatSource.physical_inner,ContinuousMap.one_apply,one_mul]
  have commute := mean.integral_comp_comm (integrand_integrable seed observation radius F)
  simp only [read] at commute
  exact congrArg Neg.neg commute.symm

theorem work_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) :
    |work seed observation radius F| ≤ nu.coeff*(∫ point : Torus, NativeWindowStressHeatSource.interaction seed observation F point)+
      (3*NativeWindowTimeIncrementSource.lowCap seed radius^2/(2*nu.coeff))*NativeWindowStressHeatBalance.energy seed F observation := by
  rw [work,abs_neg]
  change ‖∫ point : Torus, field seed observation radius F point‖ ≤ _
  have first := (continuous_integrable (NativeWindowStressHeatSource.interaction seed observation F)).const_mul nu.coeff
  have last := (continuous_integrable (massDensity seed observation F)).const_mul (coefficient seed radius)
  have upper := integral_mono (continuous_integrable (field seed observation radius F)).norm (first.add last)
    (fun point => by simpa only [Real.norm_eq_abs,Pi.add_apply] using point_bound seed observation radius F point)
  rw [integral_add' first last,integral_const_mul,integral_const_mul,massDensity_integral] at upper
  apply ((norm_integral_le_integral_norm _).trans upper).trans_eq
  unfold coefficient
  ring

def highIntegrand (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector)
    (times : ℝ × ℝ) : C(Torus,ℝ) := (1/2 : ℝ) • (pairField seed observation F times*(∑ j : Coordinate,
      ((NativeWindowCrossHistoryAction.velocity seed F (observation-times.1) j-
        NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) (observation-times.1) j)-
      (NativeWindowCrossHistoryAction.velocity seed F (observation-times.2) j-
        NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) (observation-times.2) j))*wedgeField seed observation F j times))

def relativeIntegrand (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (times : ℝ × ℝ) : C(Torus,ℝ) := (1/2 : ℝ) • (pairField seed observation F times*
      NativeWindowCrossHistoryAction.increment (NativeWindowCrossHistoryAction.velocity seed F (observation-times.1))
        (NativeWindowCrossHistoryAction.velocity seed F (observation-times.2))
        (NativeWindowCrossHistoryAction.gradient seed F (observation-times.1))
        (NativeWindowCrossHistoryAction.gradient seed F (observation-times.2)))

theorem integrand_split (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector)
    (times : ℝ × ℝ) : relativeIntegrand seed observation F times =
      integrand seed observation radius F times+highIntegrand seed observation radius F times := by
  rw [relativeIntegrand,NativeWindowTimeIncrementSource.relative_split seed radius F (observation-times.1) (observation-times.2),mul_add,smul_add]
  rfl

theorem high_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) :
    Integrable (highIntegrand seed observation radius F) jointMeasure := by
  have base := ((relative_memLp seed observation F F).mul (r := ∞) (pair_memLp seed observation F)).const_smul (1/2 : ℝ)
  have relative : Integrable (relativeIntegrand seed observation F) jointMeasure := by
    unfold relativeIntegrand
    simpa only [NativeWindowCrossHistoryAction.increment,wedgeField,Pi.smul_def,Pi.mul_def] using base.integrable (by norm_num : (1 : ℝ≥0∞) ≤ ∞)
  have same : highIntegrand seed observation radius F = fun times => relativeIntegrand seed observation F times-integrand seed observation radius F times := by
    funext times
    rw [integrand_split]
    abel
  rw [same]
  exact relative.sub (integrand_integrable seed observation radius F)

def highWork (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) : ℝ :=
  -(∫ point : Torus, (∫ times, highIntegrand seed observation radius F times ∂jointMeasure) point)

def relativeWork (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) : ℝ :=
  -(∫ point : Torus, (∫ times, relativeIntegrand seed observation F times ∂jointMeasure) point)

theorem work_split (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (radius : ℕ) (F : Finset IntegerWavevector) :
    relativeWork seed observation F = work seed observation radius F+highWork seed observation radius F := by
  unfold relativeWork work highWork field
  simp_rw [integrand_split seed observation radius F]
  rw [integral_add (integrand_integrable seed observation radius F) (high_integrable seed observation radius F)]
  simp only [ContinuousMap.add_apply]
  rw [integral_add (continuous_integrable _) (continuous_integrable _)]
  ring

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime in
theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (radius : ℕ) (F : Finset IntegerWavevector) :
    (field seed (step.2.clockAdvance+time) radius F,work seed (step.2.clockAdvance+time) radius F,
      highWork seed (step.2.clockAdvance+time) radius F,relativeWork seed (step.2.clockAdvance+time) F) =
    (field step.1 time radius F,work step.1 time radius F,highWork step.1 time radius F,relativeWork step.1 time F) := by
  have rows : ∀ᵐ times ∂jointMeasure,
      (integrand seed (step.2.clockAdvance+time) radius F times,highIntegrand seed (step.2.clockAdvance+time) radius F times,
        relativeIntegrand seed (step.2.clockAdvance+time) F times) =
      (integrand step.1 time radius F times,highIntegrand step.1 time radius F times,relativeIntegrand step.1 time F times) := by
    filter_upwards [source_next_ae seed step generated time nonnegative] with times source
    simp only [integrand,highIntegrand,relativeIntegrand,lowRelative,pairField,wedgeField,
      NativeWindowCrossHistoryAction.pair,NativeWindowCrossHistoryAction.wedge,NativeWindowCrossHistoryAction.increment,
      NativeWindowCrossHistoryAction.velocity,NativeWindowStressHeatTime.field_original,NativeWindowCrossHistoryAction.gradient,
      source.1,source.2]
  have low := integral_congr_ae (rows.mono (fun _ same => congrArg (fun values => values.1) same))
  have high := integral_congr_ae (rows.mono (fun _ same => congrArg (fun values => values.2.1) same))
  have relative := integral_congr_ae (rows.mono (fun _ same => congrArg (fun values => values.2.2) same))
  dsimp only at low high relative
  unfold work highWork relativeWork field
  rw [low,high,relative]

end
end SaturationMonoid.NavierStokes.NativeWindowLowAdvectorEnergy
