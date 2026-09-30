import H0mework.Versions.X.NavierStokes.HigherTreeSeptic.PrimitiveKernel
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Input

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticEightRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedTreeTime
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeUnheatedSourceGradient
noncomputable section
variable {nu : Viscosity}

abbrev OldIndex := NativeUnheatedSepticSevenRows.Index
abbrev Index := OldIndex × IntegerWavevector

variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate)

def parent (index : OldIndex) : Fin 7 → Slot :=
  NativeUnheatedSepticSevenRows.nodes slot leaf position newest wave i j outside l m p q r s u v index

def base (nu : Viscosity) (index : OldIndex) : ℂ :=
  NativeUnheatedTreeNormalForm.normalizer nu (parent slot leaf position newest wave i j outside l m p q r s u v index)
    (NativeUnheatedSepticSevenRows.kernel nu slot leaf position newest wave i j response outside l m p q r s u v index)

variable (selected : Fin 7) (a b : Coordinate)

def nodes (index : Index) : Fin 8 → Slot :=
  NativeUnheatedTreeLeaf.slots (parent slot leaf position newest wave i j outside l m p q r s u v index.1) selected a b index.2

theorem nodes_frequency (index : Index) :
    (∑ number : Fin 8, (nodes slot leaf position newest wave i j outside l m p q r s u v selected a b index number).1) = wave :=
  (NativeUnheatedTreeLeaf.slots_frequency _ selected a b index.2).trans
    (NativeUnheatedSepticSevenRows.nodes_frequency slot leaf position newest wave i j outside l m p q r s u v index.1)

def kernel (nu : Viscosity) (index : Index) : ℂ :=
  NativeUnheatedTreeLeaf.kernel (base slot leaf position newest wave i j response outside l m p q r s u v nu index.1)
    (parent slot leaf position newest wave i j outside l m p q r s u v index.1) selected a b

def term (seed : GeneratedWholeRestartCurrent nu) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeLeaf.term seed (parent slot leaf position newest wave i j outside l m p q r s u v index.1)
    (base slot leaf position newest wave i j response outside l m p q r s u v nu index.1) selected a b index.2 time

theorem term_product (seed : GeneratedWholeRestartCurrent nu) (index : Index) (time : ℝ) :
    term slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time =
      kernel slot leaf position newest wave i j response outside l m p q r s u v selected a b nu index*
        product seed (nodes slot leaf position newest wave i j outside l m p q r s u v selected a b index) time :=
  NativeUnheatedTreeLeaf.term_product seed _ _ selected a b index.2 time

theorem fiber_summable (seed : GeneratedWholeRestartCurrent nu) (index : OldIndex) (time : ℝ) :
    Summable (fun inside => term slot leaf position newest wave i j response outside l m p q r s u v selected a b seed (index,inside) time) :=
  NativeUnheatedTreeLeaf.raw_summable (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    (parent slot leaf position newest wave i j outside l m p q r s u v index)
    (base slot leaf position newest wave i j response outside l m p q r s u v nu index) selected a b

theorem fiber_absolute (seed : GeneratedWholeRestartCurrent nu) (index : OldIndex) (time : ℝ) :
    Summable (fun inside => ‖term slot leaf position newest wave i j response outside l m p q r s u v selected a b seed (index,inside) time‖) :=
  (fiber_summable slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time).norm

theorem original_octic (seed : GeneratedWholeRestartCurrent nu) (index : OldIndex) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    NativeUnheatedSepticPrimitiveKernel.octicTerm seed slot leaf position newest wave i j response outside l m p q r s u v index time =
      ∑ selected : Fin 7, ∑ a : Coordinate, ∑ b : Coordinate, ∑' inside,
        term slot leaf position newest wave i j response outside l m p q r s u v selected a b seed (index,inside) time :=
  NativeUnheatedTreeLeaf.source_expansion seed _ _ time nonnegative regular

theorem term_next (seed : GeneratedWholeRestartCurrent nu) (index : Index)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    term slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index (step.2.clockAdvance+time) =
      term slot leaf position newest wave i j response outside l m p q r s u v selected a b step.1 index time :=
  NativeUnheatedTreeLeaf.term_next seed _ _ selected a b index.2 step generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticEightRows
