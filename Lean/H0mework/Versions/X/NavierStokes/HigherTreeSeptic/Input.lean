import H0mework.Versions.X.NavierStokes.HigherTreeSextic.PrimitiveKernel
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Input

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSepticInput
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedSexticSixRows
noncomputable section
variable {nu : Viscosity}

def kernel (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (index : Index) : ℂ :=
  NativeUnheatedTreeInput.kernel nu (nodes slot leaf position wave i j outside l m p q r s index)
    (NativeUnheatedSexticSixRows.kernel nu slot leaf position wave i j response outside l m p q r s index) newest

def multilinearTerm (inputs : Fin 6 → NativeUnheatedTriadSum.E) (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4)
    (position : Fin 5) (newest : Fin 6) (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (index : Index) : ℂ :=
  NativeUnheatedTreeInput.multilinear inputs nu (nodes slot leaf position wave i j outside l m p q r s index)
    (NativeUnheatedSexticSixRows.kernel nu slot leaf position wave i j response outside l m p q r s index) newest

def term (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  multilinearTerm (fun number => NativeUnheatedTreeInput.input seed newest number time)
    nu slot leaf position newest wave i j response outside l m p q r s index

theorem original_septic (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (index : Index) (time : ℝ) :
    NativeUnheatedSexticPrimitiveKernel.septicTerm seed slot leaf position wave i j response outside l m p q r s index time =
      ∑ newest : Fin 6, term seed slot leaf position newest wave i j response outside l m p q r s index time :=
  NativeUnheatedTreeInput.next_original seed _ _ time

theorem input_product (seed : GeneratedWholeRestartCurrent nu) (newest : Fin 6) (time : ℝ) :
    (∏ number : Fin 6, ‖NativeUnheatedTreeInput.input seed newest number time‖) ≤
      NativeUnheatedHalfNonlinear.coefficient*NativeUnheatedSourceGradient.mass seed time*NativeUnifiedCompleteSource.budget seed^5 :=
  NativeUnheatedTreeInput.input_product seed newest time

theorem term_measurable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (index : Index) :
    AEStronglyMeasurable (term seed slot leaf position newest wave i j response outside l m p q r s index) (volume : Measure ℝ) :=
  NativeUnheatedTreeInput.term_measurable seed _ _ newest

theorem term_integrable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (index : Index) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (term seed slot leaf position newest wave i j response outside l m p q r s index) (volume.restrict (Icc 0 horizon)) :=
  NativeUnheatedTreeInput.term_integrable seed _ _ newest horizon nonnegative

theorem term_next (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (index : Index)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    term seed slot leaf position newest wave i j response outside l m p q r s index (responseStep.2.clockAdvance+time) =
      term responseStep.1 slot leaf position newest wave i j response outside l m p q r s index time :=
  NativeUnheatedTreeInput.term_next seed _ _ newest responseStep generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeUnheatedSepticInput
