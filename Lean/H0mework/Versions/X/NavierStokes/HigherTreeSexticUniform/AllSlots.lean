import H0mework.Versions.X.NavierStokes.HigherTreeSexticUniform.Outer
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.AllSlots

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformAllSlots
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedSexticCombKernel (coefficient coefficient_nonnegative)
open NativeUnheatedSexticInput
noncomputable section
variable {nu : Viscosity}

def cap (nu : Viscosity) : ℝ := NativeUnheatedSexticAllSlots.cap nu

theorem cap_nonnegative (nu : Viscosity) : 0 ≤ cap nu := NativeUnheatedSexticAllSlots.cap_nonnegative nu

theorem generic_summable (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) :
    Summable (fun index => ‖multilinearTerm inputs nu slot leaf position wave i j response outside l m p q index‖) :=
  NativeUnheatedSexticAllSlots.generic_summable inputs slot leaf position wave i j response outside l m p q

theorem generic_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) :
    (∑' index, ‖multilinearTerm inputs nu slot leaf position wave i j response outside l m p q index‖) ≤
      cap nu*(∏ number : Fin 5, ‖inputs number‖) := by
  let total := ∑' index, ‖multilinearTerm inputs nu slot leaf position wave i j response outside l m p q index‖
  have product0 : 0 ≤ ∏ number : Fin 5, ‖inputs number‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have accept (number : Fin 4) (paid : total ≤ NativeUnheatedSexticAllSlots.budgets nu number*(∏ number : Fin 5, ‖inputs number‖)) :
      total ≤ cap nu*(∏ number : Fin 5, ‖inputs number‖) :=
    paid.trans (mul_le_mul_of_nonneg_right (NativeUnheatedSexticAllSlots.budgets_le nu number) product0)
  have outer (paid : total ≤ 48*coefficient nu*34560*(∏ number : Fin 5, ‖inputs number‖)) :
      total ≤ cap nu*(∏ number : Fin 5, ‖inputs number‖) := by
    apply accept 3
    have constant : 48*coefficient nu*34560 ≤ NativeUnheatedSexticAllSlots.budgets nu 3 :=
      mul_le_mul_of_nonneg_left (by norm_num : (34560 : ℝ) ≤ 400000)
        (mul_nonneg (by norm_num) (coefficient_nonnegative nu))
    exact paid.trans (mul_le_mul_of_nonneg_right constant product0)
  fin_cases slot <;> fin_cases leaf
  · exact accept 0 (NativeUnheatedSexticCombSource.generic_bound inputs 0 0 position wave i j response outside l m p q)
  · exact accept 0 (NativeUnheatedSexticCombSource.generic_bound inputs 0 1 position wave i j response outside l m p q)
  · exact accept 1 (NativeUnheatedSexticBalancedSource.generic_bound inputs 0 0 position wave i j response outside l m p q)
  · exact accept 1 (NativeUnheatedSexticBalancedSource.generic_bound inputs 0 1 position wave i j response outside l m p q)
  · exact accept 0 (NativeUnheatedSexticCombSource.generic_bound inputs 1 0 position wave i j response outside l m p q)
  · exact accept 0 (NativeUnheatedSexticCombSource.generic_bound inputs 1 1 position wave i j response outside l m p q)
  · exact accept 1 (NativeUnheatedSexticBalancedSource.generic_bound inputs 1 0 position wave i j response outside l m p q)
  · exact accept 1 (NativeUnheatedSexticBalancedSource.generic_bound inputs 1 1 position wave i j response outside l m p q)
  · exact accept 2 (NativeUnheatedSexticRootBalancedSource.generic_bound inputs 0 position wave i j response outside l m p q)
  · exact accept 2 (NativeUnheatedSexticRootBalancedSource.generic_bound inputs 1 position wave i j response outside l m p q)
  · exact outer (NativeUnheatedSexticUniformOuter.generic_bound inputs 0 position wave i j response outside l m p q)
  · exact outer (NativeUnheatedSexticUniformOuter.generic_bound inputs 1 position wave i j response outside l m p q)

def budget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  cap nu*NativeUnheatedHalfNonlinear.coefficient*NativeUnifiedCompleteSource.budget seed^4

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ budget seed := by
  unfold budget
  positivity [cap_nonnegative nu, NativeUnheatedHalfNonlinear.coefficient_nonnegative]

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) (time : ℝ) :
    Summable (fun index => ‖term seed slot leaf position wave i j response outside l m p q index time‖) :=
  generic_summable (nu := nu) (fun number => input seed position number time) slot leaf position wave i j response outside l m p q

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) (time : ℝ) :
    (∑' index, ‖term seed slot leaf position wave i j response outside l m p q index time‖) ≤
      budget seed*NativeUnheatedSourceGradient.mass seed time := by
  have full := generic_bound (nu := nu) (fun number => input seed position number time) slot leaf position wave i j response outside l m p q
  have paid := mul_le_mul_of_nonneg_left (input_product seed position time) (cap_nonnegative nu)
  exact full.trans (paid.trans_eq (by unfold budget; ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformAllSlots
