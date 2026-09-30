import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.AllSlots
import H0mework.Versions.X.NavierStokes.UnheatedWriterHalf.Source

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticInput
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeEndpointVelocityCarrier NativeUnheatedQuarticAllSlots
noncomputable section
variable {nu : Viscosity}

def input (seed : GeneratedWholeRestartCurrent nu) (position index : Fin 4) (time : ℝ) : NativeUnheatedTriadSum.E :=
  wholeVelocityCLM (if index = position then NativeUnheatedHalfNonlinear.source seed time
    else (NativeUnifiedCompleteSource.source seed time).fst)

theorem input_bound (seed : GeneratedWholeRestartCurrent nu) (position index : Fin 4) (time : ℝ) :
    ‖input seed position index time‖ ≤ if index = position
      then NativeUnheatedHalfNonlinear.coefficient*NativeUnheatedSourceGradient.mass seed time
      else NativeUnifiedCompleteSource.budget seed := by
  by_cases same : index = position
  · simp only [input, if_pos same]
    exact (wholeVelocity_norm_le _).trans (NativeUnheatedHalfNonlinear.source_bound seed time)
  · simp only [input, if_neg same]
    exact (wholeVelocity_norm_le _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed time)

theorem input_measurable (seed : GeneratedWholeRestartCurrent nu) (position index : Fin 4) :
    AEStronglyMeasurable (input seed position index) (volume : Measure ℝ) := by
  change AEStronglyMeasurable (fun time => wholeVelocityCLM (if index = position then
    NativeUnheatedHalfNonlinear.source seed time else (NativeUnifiedCompleteSource.source seed time).fst)) volume
  by_cases same : index = position
  · simpa only [input, if_pos same] using!
      wholeVelocityCLM.continuous.comp_aestronglyMeasurable (NativeUnheatedHalfNonlinear.source_measurable seed)
  · simpa only [input, if_neg same] using!
      wholeVelocityCLM.continuous.comp_aestronglyMeasurable (NativeUnheatedSourceWeightedTail.velocity_measurable seed)

theorem input_product (seed : GeneratedWholeRestartCurrent nu) (position : Fin 4) (time : ℝ) :
    ‖input seed position 0 time‖*‖input seed position 1 time‖*‖input seed position 2 time‖*‖input seed position 3 time‖ ≤
      (NativeUnheatedHalfNonlinear.coefficient*NativeUnheatedSourceGradient.mass seed time)*NativeUnifiedCompleteSource.budget seed^3 := by
  have actual := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 4)))
    (fun index _ => norm_nonneg (input seed position index time)) (fun index _ => input_bound seed position index time)
  rw [Fin.prod_univ_four] at actual
  apply actual.trans_eq
  fin_cases position <;> simp only [Fin.prod_univ_four, Fin.ext_iff] <;> norm_num <;> ring

def kernel (nu : Viscosity) (slot : Fin 3) (position : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) : ℂ :=
  NativeUnheatedQuarticKernel.normalizer nu (slots slot wave i j outside l m index 0)
    (slots slot wave i j outside l m index 1) (slots slot wave i j outside l m index 2)
    (slots slot wave i j outside l m index 3) (tree nu slot wave i j response outside l m index) *
      (NativeUnheatedHalfNonlinear.quarter (slots slot wave i j outside l m index position).1 : ℂ)

def term (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (position : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  kernel nu slot position wave i j response outside l m index *
    (input seed position 0 time (slots slot wave i j outside l m index 0).1 (slots slot wave i j outside l m index 0).2 *
      input seed position 1 time (slots slot wave i j outside l m index 1).1 (slots slot wave i j outside l m index 1).2 *
      input seed position 2 time (slots slot wave i j outside l m index 2).1 (slots slot wave i j outside l m index 2).2 *
      input seed position 3 time (slots slot wave i j outside l m index 3).1 (slots slot wave i j outside l m index 3).2)

theorem original_quintic (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (time : ℝ) :
    quinticTerm seed slot wave i j response outside l m index time =
      ∑ position : Fin 4, term seed slot position wave i j response outside l m index time := by
  simp only [quinticTerm, NativeUnheatedQuarticNormalForm.quintic, NativeUnheatedQuarticTime.forcing,
    NativeUnheatedHalfNonlinear.source_action, NativeUnheatedTriadRows.velocity_original,
    Fin.sum_univ_four, term, kernel, input, Fin.ext_iff, wholeVelocityCLM_apply, Complex.real_smul]
  norm_num
  ring

theorem input_next (seed : GeneratedWholeRestartCurrent nu) (position index : Fin 4)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    input seed position index (responseStep.2.clockAdvance+time) = input responseStep.1 position index time := by
  simp only [input, NativeUnheatedHalfNonlinear.source_next seed responseStep generated time nonnegative,
    NativeUnifiedCompleteSource.source_generated_next seed responseStep generated time nonnegative]

theorem term_next (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (position : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    term seed slot position wave i j response outside l m index (responseStep.2.clockAdvance+time) =
      term responseStep.1 slot position wave i j response outside l m index time := by
  simp only [term, input_next seed position _ responseStep generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticInput
