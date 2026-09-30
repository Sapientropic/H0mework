import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Input
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Kernel
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.SumPermutations

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedQuinticInput
open NativeUnheatedQuarticAllSlots (Index)
noncomputable section
variable {nu : Viscosity}

theorem kernel_original (slot : Fin 3) (position : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) :
    kernel nu slot position wave i j response outside l m index =
      NativeUnheatedQuinticKernel.kernel nu slot wave i j response outside l m index position := rfl

theorem source_kernel_bound (slot : Fin 3) (position : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) :
    ‖kernel nu slot position wave i j response outside l m index‖ ≤ NativeUnheatedQuinticWeights.cap nu *
      NativeUnheatedQuinticWeights.eta (NativeUnheatedQuinticKernel.spectators slot wave index 0) *
      NativeUnheatedQuinticWeights.eta (NativeUnheatedQuinticKernel.spectators slot wave index 1) :=
  NativeUnheatedQuinticKernel.kernel_bound nu slot wave i j response outside l m index position

theorem term_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (position : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (time : ℝ) :
    Summable (fun index => ‖term seed slot position wave i j response outside l m index time‖) := by
  fin_cases slot
  · exact NativeUnheatedQuinticSum.absolute_summable _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => source_kernel_bound 0 position wave i j response outside l m index) l m j outside
      (input seed position 0 time) (input seed position 1 time) (input seed position 2 time) (input seed position 3 time)
  · exact NativeUnheatedQuinticSum.middle_absolute_summable _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => source_kernel_bound 1 position wave i j response outside l m index) l m i outside
      (input seed position 0 time) (input seed position 1 time) (input seed position 2 time) (input seed position 3 time)
  · exact NativeUnheatedQuinticSum.outer_absolute_summable _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => source_kernel_bound 2 position wave i j response outside l m index) i j l m
      (input seed position 0 time) (input seed position 1 time) (input seed position 2 time) (input seed position 3 time)

def factor (nu : Viscosity) : ℝ := 3*NativeUnheatedQuinticWeights.cap nu*‖NativeUnheatedQuinticSum.etaL2‖^2

theorem factor_nonnegative (nu : Viscosity) : 0 ≤ factor nu := by
  unfold factor
  positivity [NativeUnheatedQuinticWeights.cap_nonnegative nu]

def bound (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  factor nu*NativeUnheatedHalfNonlinear.coefficient*NativeUnifiedCompleteSource.budget seed^3

theorem bound_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ bound seed := by
  have velocity := NativeUnheatedSourceWeightedTail.velocity_bound seed (0 : ℝ)
  have positive := (norm_nonneg _).trans velocity
  unfold bound
  positivity [factor_nonnegative nu, NativeUnheatedHalfNonlinear.coefficient_nonnegative]

theorem term_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (position : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (time : ℝ) :
    (∑' index, ‖term seed slot position wave i j response outside l m index time‖) ≤
      bound seed*NativeUnheatedSourceGradient.mass seed time := by
  have generic : (∑' index, ‖term seed slot position wave i j response outside l m index time‖) ≤
      factor nu*‖input seed position 0 time‖*‖input seed position 1 time‖*‖input seed position 2 time‖*‖input seed position 3 time‖ := by
    fin_cases slot
    · exact NativeUnheatedQuinticSum.absolute_bound _ (NativeUnheatedQuinticWeights.cap nu) wave
        (fun index => source_kernel_bound 0 position wave i j response outside l m index) l m j outside
        (input seed position 0 time) (input seed position 1 time) (input seed position 2 time) (input seed position 3 time)
    · exact NativeUnheatedQuinticSum.middle_absolute_bound _ (NativeUnheatedQuinticWeights.cap nu) wave
        (fun index => source_kernel_bound 1 position wave i j response outside l m index) l m i outside
        (input seed position 0 time) (input seed position 1 time) (input seed position 2 time) (input seed position 3 time)
    · exact NativeUnheatedQuinticSum.outer_absolute_bound _ (NativeUnheatedQuinticWeights.cap nu) wave
        (fun index => source_kernel_bound 2 position wave i j response outside l m index) i j l m
        (input seed position 0 time) (input seed position 1 time) (input seed position 2 time) (input seed position 3 time)
  have paid := mul_le_mul_of_nonneg_left (input_product seed position time) (factor_nonnegative nu)
  apply generic.trans
  calc
    _ = factor nu*(‖input seed position 0 time‖*‖input seed position 1 time‖*
        ‖input seed position 2 time‖*‖input seed position 3 time‖) := by ring
    _ ≤ _ := paid
    _ = _ := by unfold bound; ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticSource
