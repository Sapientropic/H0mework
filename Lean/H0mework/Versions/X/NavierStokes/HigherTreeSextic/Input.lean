import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.PrimitiveKernel
import H0mework.Versions.X.NavierStokes.UnheatedWriterHalf.Source

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticInput
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeEndpointVelocityCarrier NativeUnheatedQuinticFiveRows
noncomputable section
variable {nu : Viscosity}

def input (seed : GeneratedWholeRestartCurrent nu) (position index : Fin 5) (time : ℝ) : NativeUnheatedTriadSum.E :=
  wholeVelocityCLM (if index=position then NativeUnheatedHalfNonlinear.source seed time
    else (NativeUnifiedCompleteSource.source seed time).fst)

theorem input_bound (seed : GeneratedWholeRestartCurrent nu) (position index : Fin 5) (time : ℝ) :
    ‖input seed position index time‖ ≤ if index=position
      then NativeUnheatedHalfNonlinear.coefficient*NativeUnheatedSourceGradient.mass seed time else NativeUnifiedCompleteSource.budget seed := by
  by_cases same : index=position
  · simp only [input, if_pos same]
    exact (wholeVelocity_norm_le _).trans (NativeUnheatedHalfNonlinear.source_bound seed time)
  · simp only [input, if_neg same]
    exact (wholeVelocity_norm_le _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed time)

theorem input_product (seed : GeneratedWholeRestartCurrent nu) (position : Fin 5) (time : ℝ) :
    (∏ index : Fin 5, ‖input seed position index time‖) ≤
      NativeUnheatedHalfNonlinear.coefficient*NativeUnheatedSourceGradient.mass seed time*NativeUnifiedCompleteSource.budget seed^4 := by
  have paid := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 5)))
    (fun index _ => norm_nonneg (input seed position index time)) (fun index _ => input_bound seed position index time)
  apply paid.trans_eq
  rw [Fin.prod_univ_succAbove _ position]
  simp only [if_true, Fin.succAbove_ne, if_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem sum_five (f : Fin 5 → ℂ) : (∑ position : Fin 5, f position) = f 0+f 1+f 2+f 3+f 4 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_four]
  change f 0+(f 1+f 2+f 3+f 4) = _
  ring

private theorem product_five (f : Fin 5 → ℂ) : (∏ position : Fin 5, f position) = f 0*f 1*f 2*f 3*f 4 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_four]
  change f 0*(f 1*f 2*f 3*f 4) = _
  ring

def kernel (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) : ℂ :=
  NativeUnheatedQuinticNormalForm.normalizer nu (nodes slot leaf wave i j outside l m p q index 0)
    (nodes slot leaf wave i j outside l m p q index 1) (nodes slot leaf wave i j outside l m p q index 2)
    (nodes slot leaf wave i j outside l m p q index 3) (nodes slot leaf wave i j outside l m p q index 4)
    (NativeUnheatedQuinticFiveRows.kernel nu slot leaf wave i j response outside l m p q index)*
      (NativeUnheatedHalfNonlinear.quarter (nodes slot leaf wave i j outside l m p q index position).1 : ℂ)

def multilinearTerm (inputs : Fin 5 → NativeUnheatedTriadSum.E) (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4)
    (position : Fin 5) (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) (index : Index) : ℂ :=
  kernel nu slot leaf position wave i j response outside l m p q index*
    ∏ number : Fin 5, inputs number (nodes slot leaf wave i j outside l m p q index number).1
      (nodes slot leaf wave i j outside l m p q index number).2

def term (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  multilinearTerm (fun number => input seed position number time) nu slot leaf position wave i j response outside l m p q index

theorem original_sextic (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) (time : ℝ) :
    NativeUnheatedQuinticPrimitiveKernel.sexticTerm seed slot leaf wave i j response outside l m p q index time =
      ∑ position : Fin 5, term seed slot leaf position wave i j response outside l m p q index time := by
  simp only [NativeUnheatedQuinticPrimitiveKernel.sexticTerm, NativeUnheatedQuinticNormalForm.sextic,
    NativeUnheatedQuinticTime.forcing, NativeUnheatedHalfNonlinear.source_action, NativeUnheatedTriadRows.velocity_original,
    sum_five, term, multilinearTerm, kernel, product_five,
    input, Fin.ext_iff, wholeVelocityCLM_apply, Complex.real_smul]
  norm_num
  ring

theorem input_measurable (seed : GeneratedWholeRestartCurrent nu) (position index : Fin 5) :
    AEStronglyMeasurable (input seed position index) (volume : Measure ℝ) := by
  change AEStronglyMeasurable (fun time => wholeVelocityCLM (if index=position then
    NativeUnheatedHalfNonlinear.source seed time else (NativeUnifiedCompleteSource.source seed time).fst)) volume
  by_cases same : index=position
  · simpa only [input, if_pos same] using! wholeVelocityCLM.continuous.comp_aestronglyMeasurable
      (NativeUnheatedHalfNonlinear.source_measurable seed)
  · simpa only [input, if_neg same] using! wholeVelocityCLM.continuous.comp_aestronglyMeasurable
      (NativeUnheatedSourceWeightedTail.velocity_measurable seed)

theorem input_next (seed : GeneratedWholeRestartCurrent nu) (position index : Fin 5)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    input seed position index (responseStep.2.clockAdvance+time) = input responseStep.1 position index time := by
  simp only [input, NativeUnheatedHalfNonlinear.source_next seed responseStep generated time nonnegative,
    NativeUnifiedCompleteSource.source_generated_next seed responseStep generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticInput
