import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Middle
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.OuterSource
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.NormalForm

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticAllSlots
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedSourceGradient NativeWholeH1Mixed
noncomputable section
variable {nu : Viscosity}
abbrev Index := NativeUnheatedQuarticRows.Pair × IntegerWavevector

def slots (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m : Coordinate)
    (index : Index) : Fin 4 → NativeUnheatedQuarticTime.Slot :=
  ![![(index.2,l), (index.1.2-index.2,m), (wave-index.1.1-index.1.2,j), (index.1.1,outside)],
    ![(index.2,l), (wave-index.1.1-index.1.2-index.2,m), (index.1.2,i), (index.1.1,outside)],
    ![(index.1.2,i), (wave-index.1.1-index.1.2,j), (index.2,l), (index.1.1-index.2,m)]] slot

def tree (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) : ℂ :=
  ![NativeUnheatedQuarticRows.tree nu wave i j response l m index.1,
    NativeUnheatedQuarticMiddle.tree nu wave i j response l m index.1,
    NativeUnheatedQuarticOuterRows.tree nu wave i j response outside l m index.1] slot

def term (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  ![NativeUnheatedQuarticRows.term seed wave i j response outside l m index.1 index.2 time,
    NativeUnheatedQuarticMiddle.term seed wave i j response outside l m index.1 index.2 time,
    NativeUnheatedQuarticOuterRows.term seed wave i j response outside l m index.1 index.2 time] slot

theorem term_original (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (time : ℝ) :
    term seed slot wave i j response outside l m index time = tree nu slot wave i j response outside l m index *
      NativeUnheatedQuarticTime.product seed (slots slot wave i j outside l m index 0)
        (slots slot wave i j outside l m index 1) (slots slot wave i j outside l m index 2)
        (slots slot wave i j outside l m index 3) time := by
  fin_cases slot <;> rfl

theorem source_fiber (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (outer : NativeUnheatedQuarticRows.Pair) :
    NativeUnheatedTriadSource.row seed slot wave i j response outside outer time =
      ∑ l : Coordinate, ∑ m : Coordinate, ∑' inside,
        term seed slot wave i j response outside l m (outer,inside) time := by
  fin_cases slot
  · exact NativeUnheatedQuarticRows.source_fiber seed time nonnegative regular wave i j response outside outer
  · exact NativeUnheatedQuarticMiddle.source_fiber seed time nonnegative regular wave i j response outside outer
  · exact NativeUnheatedQuarticOuterRows.source_fiber seed time nonnegative regular wave i j response outside outer

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) :
    Summable (fun index => ‖term seed slot wave i j response outside l m index time‖) := by
  fin_cases slot
  · exact NativeUnheatedQuarticSource.absolute_summable seed time nonnegative regular wave i j response outside l m
  · exact NativeUnheatedQuarticMiddle.absolute_summable seed time nonnegative regular wave i j response outside l m
  · exact NativeUnheatedQuarticOuterSource.absolute_summable seed time nonnegative regular wave i j response outside l m

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) :
    (∑' index, ‖term seed slot wave i j response outside l m index time‖) ≤
      NativeUnheatedQuarticSource.bound seed*mass seed time := by
  fin_cases slot
  · exact NativeUnheatedQuarticSource.absolute_bound seed time nonnegative regular wave i j response outside l m
  · exact NativeUnheatedQuarticMiddle.absolute_bound seed time nonnegative regular wave i j response outside l m
  · exact NativeUnheatedQuarticOuterSource.absolute_bound seed time nonnegative regular wave i j response outside l m

def primitiveTerm (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedQuarticNormalForm.primitive seed (slots slot wave i j outside l m index 0)
    (slots slot wave i j outside l m index 1) (slots slot wave i j outside l m index 2)
    (slots slot wave i j outside l m index 3) (tree nu slot wave i j response outside l m index) time

def quinticTerm (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedQuarticNormalForm.quintic seed (slots slot wave i j outside l m index 0)
    (slots slot wave i j outside l m index 1) (slots slot wave i j outside l m index 2)
    (slots slot wave i j outside l m index 3) (tree nu slot wave i j response outside l m index) time

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    primitiveTerm seed slot wave i j response outside l m index finish -
      primitiveTerm seed slot wave i j response outside l m index start =
        ∫ time in start..finish, quinticTerm seed slot wave i j response outside l m index time -
          term seed slot wave i j response outside l m index time := by
  simp_rw [term_original]
  exact NativeUnheatedQuarticNormalForm.row_write seed _ _ _ _ _ start finish start0 finish0

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (order : ℕ) (observation origin start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    (∫ time in start..finish, NativeUnheatedStressPairEvolution.kernelWeight order observation origin time •
      term seed slot wave i j response outside l m index time) =
    (∫ time in start..finish, NativeUnheatedStressPairEvolution.kernelWeight order observation origin time •
      quinticTerm seed slot wave i j response outside l m index time) -
    (∫ time in start..finish, NativeUnheatedStressPairEvolution.kernelWeight (order+1) observation origin time •
      primitiveTerm seed slot wave i j response outside l m index time) -
    (NativeUnheatedStressPairEvolution.kernelWeight order observation origin finish •
      primitiveTerm seed slot wave i j response outside l m index finish -
      NativeUnheatedStressPairEvolution.kernelWeight order observation origin start •
        primitiveTerm seed slot wave i j response outside l m index start) := by
  simp_rw [term_original]
  exact NativeUnheatedQuarticNormalForm.weighted_write seed _ _ _ _ _ order observation origin start finish start0 finish0

theorem term_next (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    term seed slot wave i j response outside l m index (responseStep.2.clockAdvance+time) =
      term responseStep.1 slot wave i j response outside l m index time := by
  rw [term_original, term_original, NativeUnheatedQuarticTime.product_next seed _ _ _ _ responseStep generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticAllSlots
