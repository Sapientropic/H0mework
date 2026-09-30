import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CombSource
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.BalancedSource
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.RootBalancedSource
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.OuterCombSource

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticAllSlots
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeUnheatedSexticLatticePower
open NativeUnheatedSexticCombKernel (coefficient coefficient_nonnegative)
open NativeUnheatedSexticInput
noncomputable section
variable {nu : Viscosity}

def budgets (nu : Viscosity) : Fin 4 → ℝ :=
  ![24576*coefficient nu,
    3*coefficient nu*NativeUnheatedSexticBalancedSum.gain*NativeUnheatedSexticQuarterSchur.cap 0,
    192*coefficient nu*NativeUnheatedSexticShiftSchur.cap 0,
    48*coefficient nu*400000]

theorem budgets_nonnegative (nu : Viscosity) (number : Fin 4) : 0 ≤ budgets nu number := by
  fin_cases number
  · exact mul_nonneg (by norm_num) (coefficient_nonnegative nu)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (coefficient_nonnegative nu))
      NativeUnheatedSexticBalancedSum.gain_nonnegative) (NativeUnheatedSexticQuarterSchur.cap_nonnegative 0)
  · exact mul_nonneg (mul_nonneg (by norm_num) (coefficient_nonnegative nu)) (NativeUnheatedSexticShiftSchur.cap_nonnegative 0)
  · exact mul_nonneg (mul_nonneg (by norm_num) (coefficient_nonnegative nu)) (by norm_num)

def cap (nu : Viscosity) : ℝ := ∑ number : Fin 4, budgets nu number

theorem cap_nonnegative (nu : Viscosity) : 0 ≤ cap nu := Finset.sum_nonneg fun number _ => budgets_nonnegative nu number

theorem budgets_le (nu : Viscosity) (number : Fin 4) : budgets nu number ≤ cap nu :=
  Finset.single_le_sum (fun number _ => budgets_nonnegative nu number) (Finset.mem_univ number)

theorem radical_one (wave : IntegerWavevector) : 1 ≤ radical wave := by
  simpa only [radical, Real.sqrt_one] using Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (mass_one wave))

theorem generic_summable (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) :
    Summable (fun index => ‖multilinearTerm inputs nu slot leaf position wave i j response outside l m p q index‖) := by
  fin_cases slot <;> fin_cases leaf
  · exact NativeUnheatedSexticCombSource.generic_summable inputs 0 0 position wave i j response outside l m p q
  · exact NativeUnheatedSexticCombSource.generic_summable inputs 0 1 position wave i j response outside l m p q
  · exact NativeUnheatedSexticBalancedSource.generic_summable inputs 0 0 position wave i j response outside l m p q
  · exact NativeUnheatedSexticBalancedSource.generic_summable inputs 0 1 position wave i j response outside l m p q
  · exact NativeUnheatedSexticCombSource.generic_summable inputs 1 0 position wave i j response outside l m p q
  · exact NativeUnheatedSexticCombSource.generic_summable inputs 1 1 position wave i j response outside l m p q
  · exact NativeUnheatedSexticBalancedSource.generic_summable inputs 1 0 position wave i j response outside l m p q
  · exact NativeUnheatedSexticBalancedSource.generic_summable inputs 1 1 position wave i j response outside l m p q
  · exact NativeUnheatedSexticRootBalancedSource.generic_summable inputs 0 position wave i j response outside l m p q
  · exact NativeUnheatedSexticRootBalancedSource.generic_summable inputs 1 position wave i j response outside l m p q
  · exact NativeUnheatedSexticOuterCombSource.generic_summable inputs 0 position wave i j response outside l m p q
  · exact NativeUnheatedSexticOuterCombSource.generic_summable inputs 1 position wave i j response outside l m p q

theorem generic_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) :
    (∑' index, ‖multilinearTerm inputs nu slot leaf position wave i j response outside l m p q index‖) ≤
      cap nu*radical wave*(∏ number : Fin 5, ‖inputs number‖) := by
  let total := ∑' index, ‖multilinearTerm inputs nu slot leaf position wave i j response outside l m p q index‖
  have product0 : 0 ≤ ∏ number : Fin 5, ‖inputs number‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have ordinary (number : Fin 4) (paid : total ≤ budgets nu number*(∏ number : Fin 5, ‖inputs number‖)) :
      total ≤ cap nu*radical wave*(∏ number : Fin 5, ‖inputs number‖) := by
    apply paid.trans
    have grown := mul_le_mul_of_nonneg_left (radical_one wave) (budgets_nonnegative nu number)
    rw [mul_one] at grown
    exact mul_le_mul_of_nonneg_right (grown.trans (mul_le_mul_of_nonneg_right (budgets_le nu number) (radical_positive wave).le)) product0
  have outer (paid : total ≤ budgets nu 3*radical wave*(∏ number : Fin 5, ‖inputs number‖)) :
      total ≤ cap nu*radical wave*(∏ number : Fin 5, ‖inputs number‖) :=
    paid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (budgets_le nu 3) (radical_positive wave).le) product0)
  fin_cases slot <;> fin_cases leaf
  · exact ordinary 0 (NativeUnheatedSexticCombSource.generic_bound inputs 0 0 position wave i j response outside l m p q)
  · exact ordinary 0 (NativeUnheatedSexticCombSource.generic_bound inputs 0 1 position wave i j response outside l m p q)
  · exact ordinary 1 (NativeUnheatedSexticBalancedSource.generic_bound inputs 0 0 position wave i j response outside l m p q)
  · exact ordinary 1 (NativeUnheatedSexticBalancedSource.generic_bound inputs 0 1 position wave i j response outside l m p q)
  · exact ordinary 0 (NativeUnheatedSexticCombSource.generic_bound inputs 1 0 position wave i j response outside l m p q)
  · exact ordinary 0 (NativeUnheatedSexticCombSource.generic_bound inputs 1 1 position wave i j response outside l m p q)
  · exact ordinary 1 (NativeUnheatedSexticBalancedSource.generic_bound inputs 1 0 position wave i j response outside l m p q)
  · exact ordinary 1 (NativeUnheatedSexticBalancedSource.generic_bound inputs 1 1 position wave i j response outside l m p q)
  · exact ordinary 2 (NativeUnheatedSexticRootBalancedSource.generic_bound inputs 0 position wave i j response outside l m p q)
  · exact ordinary 2 (NativeUnheatedSexticRootBalancedSource.generic_bound inputs 1 position wave i j response outside l m p q)
  · apply outer
    have paid := NativeUnheatedSexticOuterCombSource.generic_bound (nu := nu) inputs 0 position wave i j response outside l m p q
    exact paid.trans_eq (by change _ = 48*coefficient nu*400000*radical wave*(∏ number : Fin 5, ‖inputs number‖); unfold NativeUnheatedSexticShiftSchur.cap; ring)
  · apply outer
    have paid := NativeUnheatedSexticOuterCombSource.generic_bound (nu := nu) inputs 1 position wave i j response outside l m p q
    exact paid.trans_eq (by change _ = 48*coefficient nu*400000*radical wave*(∏ number : Fin 5, ‖inputs number‖); unfold NativeUnheatedSexticShiftSchur.cap; ring)

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticAllSlots
