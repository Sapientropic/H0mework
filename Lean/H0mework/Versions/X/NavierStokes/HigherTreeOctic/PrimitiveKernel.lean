import H0mework.Versions.X.NavierStokes.HigherTreeOctic.EightRows
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.RateTransfer

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticPrimitiveKernel
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedTreeTime NativeUnheatedStressPairEvolution
open NativeUnheatedOcticEightRows
noncomputable section
variable {nu : Viscosity}
variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)

def primitive (seed : GeneratedWholeRestartCurrent nu) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeNormalForm.primitive seed (nodes slot leaf position newest wave i j outside l m p q r s u v selected a b index)
    (kernel slot leaf position newest wave i j response outside l m p q r s u v selected a b nu index) time

def nextForcing (seed : GeneratedWholeRestartCurrent nu) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeNormalForm.nextForcing seed (nodes slot leaf position newest wave i j outside l m p q r s u v selected a b index)
    (kernel slot leaf position newest wave i j response outside l m p q r s u v selected a b nu index) time

theorem primitive_original (seed : GeneratedWholeRestartCurrent nu) (index : Index) (time : ℝ) :
    primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time =
      (sumRate nu (nodes slot leaf position newest wave i j outside l m p q r s u v selected a b index))⁻¹ •
        term slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time := by
  rw [term_product]
  exact NativeUnheatedTreeNormalForm.primitive_original seed _ _ time

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (index : Index) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index last-
      primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index first =
    ∫ time in first..last, nextForcing slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time-
      term slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time := by
  simp only [term_product]
  exact NativeUnheatedTreeNormalForm.row_write seed _ _ first last first0 last0

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (index : Index) (order : ℕ)
    (observation shift first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    (∫ time in first..last, kernelWeight order observation shift time •
      nextForcing slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time) =
    kernelWeight order observation shift last •
      primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index last-
    kernelWeight order observation shift first •
      primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index first+
    (∫ time in first..last, kernelWeight (order+1) observation shift time •
      primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time)+
    ∫ time in first..last, kernelWeight order observation shift time •
      term slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time := by
  have generated := NativeUnheatedTreeNormalForm.weighted_write seed
    (nodes slot leaf position newest wave i j outside l m p q r s u v selected a b index)
    (kernel slot leaf position newest wave i j response outside l m p q r s u v selected a b nu index)
    order observation shift first last first0 last0
  simp only [term_product, primitive, nextForcing]
  linear_combination -generated

theorem primitive_transfer (seed : GeneratedWholeRestartCurrent nu) (index : Index) (time : ℝ) :
    primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index time =
    (1+NativeUnheatedTreeRateTransfer.ratio (nu := nu)
      (parent slot leaf position newest wave i j outside l m p q r s u v index.1) selected a b index.2) •
      NativeUnheatedTreeLeaf.term seed (parent slot leaf position newest wave i j outside l m p q r s u v index.1)
        (NativeUnheatedTreeNormalForm.normalizer nu (parent slot leaf position newest wave i j outside l m p q r s u v index.1)
          (base slot leaf position newest wave i j response outside l m p q r s u v nu index.1)) selected a b index.2 time :=
  NativeUnheatedTreeRateTransfer.primitive_transfer seed _ selected _ a b index.2 time

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu) (index : Index)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index (step.2.clockAdvance+time) =
      primitive slot leaf position newest wave i j response outside l m p q r s u v selected a b step.1 index time :=
  NativeUnheatedTreeNormalForm.primitive_next seed _ _ step generated time nonnegative

theorem nextForcing_next (seed : GeneratedWholeRestartCurrent nu) (index : Index)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    nextForcing slot leaf position newest wave i j response outside l m p q r s u v selected a b seed index (step.2.clockAdvance+time) =
      nextForcing slot leaf position newest wave i j response outside l m p q r s u v selected a b step.1 index time :=
  NativeUnheatedTreeNormalForm.nextForcing_next seed _ _ step generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticPrimitiveKernel
