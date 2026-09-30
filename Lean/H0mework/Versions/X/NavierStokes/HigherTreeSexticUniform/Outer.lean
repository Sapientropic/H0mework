import H0mework.Versions.X.NavierStokes.HigherTreeSextic.OuterCombSource
import H0mework.Versions.X.NavierStokes.HigherTreeSexticUniform.Sum

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformOuter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeUnheatedSexticOuterCombKernel NativeUnheatedSexticInput
open NativeUnheatedSexticCombKernel (coefficient coefficient_nonnegative)
open NativeUnheatedSexticCombSource (rows)
open NativeUnheatedSexticOuterCombSource (majorant majorant_summable indexEquiv fiber_bound)
noncomputable section
variable {nu : Viscosity}

theorem generic_summable (inputs : Fin 5 → NativeUnheatedTriadSum.E) (leaf : Fin 2) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) :
    Summable (fun index => ‖multilinearTerm inputs nu 2 (originalLeaf leaf) position wave i j response outside l m p q index‖) :=
  NativeUnheatedSexticOuterCombSource.generic_summable inputs leaf position wave i j response outside l m p q

theorem generic_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (leaf : Fin 2) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate) :
    (∑' index, ‖multilinearTerm inputs nu 2 (originalLeaf leaf) position wave i j response outside l m p q index‖) ≤
      48*coefficient nu*34560*(∏ number : Fin 5, ‖inputs number‖) := by
  have sums := generic_summable (nu := nu) inputs leaf position wave i j response outside l m p q
  rw [sums.tsum_prod]
  have compare := sums.prod.tsum_le_tsum
    (fun index => fiber_bound (nu := nu) inputs leaf position wave i j response outside l m p q index)
    (majorant_summable (nu := nu) inputs leaf position wave)
  simp_rw [majorant] at compare
  rw [tsum_mul_left, (indexEquiv leaf wave).tsum_eq] at compare
  have sumBound := NativeUnheatedSexticUniformSum.critical_bound wave (rows inputs 4) (rows inputs 2) (rows inputs 3)
  simp only [rows, NativeUnheatedTriadSum.rowNorms_norm] at sumBound
  have paid := mul_le_mul_of_nonneg_left sumBound
    (by positivity [coefficient_nonnegative nu] : (0 : ℝ) ≤ 3*coefficient nu*‖inputs 0‖*‖inputs 1‖)
  apply (compare.trans paid).trans_eq
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_three]
  change _ = 48*coefficient nu*34560*(‖inputs 0‖*(‖inputs 1‖*(‖inputs 2‖*‖inputs 3‖*‖inputs 4‖)))
  ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformOuter
