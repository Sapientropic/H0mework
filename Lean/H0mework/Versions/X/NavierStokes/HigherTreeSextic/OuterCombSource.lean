import H0mework.Versions.X.NavierStokes.HigherTreeSextic.OuterCombKernel
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CombSource

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticOuterCombSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedSexticOuterCombKernel NativeUnheatedSexticInput
open NativeUnheatedSexticCombKernel (coefficient coefficient_nonnegative)
open NativeUnheatedSexticCombSource (rows)
noncomputable section
variable {nu : Viscosity}

def indexEquiv (leaf : Fin 2) (wave : IntegerWavevector) : Index ≃ (IntegerWavevector × IntegerWavevector) × IntegerWavevector where
  toFun index := ((first index,middle wave index),last leaf index)
  invFun index := ((wave-index.1.1-index.1.2,index.1.1),
    if leaf=0 then wave-index.1.1-index.1.2-index.2 else index.2)
  left_inv := by
    rintro ⟨⟨c,a⟩,d⟩
    by_cases chosen : leaf=0
    all_goals simp only [first, middle, last, chosen, if_true, if_false]
    all_goals congr 1 <;> (congr 1; abel)
  right_inv := by
    rintro ⟨⟨a,b⟩,r⟩
    by_cases chosen : leaf=0
    all_goals simp only [first, middle, last, chosen, if_true, if_false]
    all_goals congr 1 <;> (congr 1; abel)

theorem remaining_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (leaf : Fin 2) (position : Fin 5)
    (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index)  :
    ‖NativeUnheatedSexticCollapse.remaining inputs 2 (originalLeaf leaf) position wave i j outside l m index‖ ≤
      |rows inputs 2 (first index)| *|rows inputs 3 (middle wave index)| *
        |rows inputs 4 (last leaf index)| := by
  rw [NativeUnheatedSexticCollapse.remaining, norm_prod]
  have point (number : Fin 3) : ‖inputs number.succ.succ
      (NativeUnheatedQuarticAllSlots.slots 2 wave i j outside l m index ((originalLeaf leaf).succAbove number)).1
      (NativeUnheatedQuarticAllSlots.slots 2 wave i j outside l m index ((originalLeaf leaf).succAbove number)).2‖ ≤
        ‖inputs number.succ.succ (![first index,middle wave index,last leaf index] number)‖ := by
    rw [← remaining_waves leaf wave i j outside l m index number]
    exact norm_le_pi_norm _ _
  have paid := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3))) (fun number _ => norm_nonneg _) (fun number _ => point number)
  apply paid.trans_eq
  rw [Fin.prod_univ_three]
  change ‖inputs 2 (first index)‖*‖inputs 3 (middle wave index)‖*
    ‖inputs 4 (last leaf index)‖ = _
  simp only [rows, NativeUnheatedTriadSum.rowNorms, abs_norm]

def majorant (inputs : Fin 5 → NativeUnheatedTriadSum.E) (leaf : Fin 2) (_position : Fin 5) (wave : IntegerWavevector)
     (index : Index) : ℝ :=
  (3*coefficient nu*‖inputs 0‖*‖inputs 1‖)*
    NativeUnheatedSexticShiftCriticalSum.term wave (rows inputs 4) (rows inputs 2) (rows inputs 3)
      (indexEquiv leaf wave index)

theorem fiber_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index)  :
    (∑' inside, ‖multilinearTerm inputs nu 2 (originalLeaf leaf) position wave i j response outside l m p q (index,inside)‖) ≤
      majorant (nu := nu) inputs leaf position wave index := by
  have generated := NativeUnheatedSexticCollapse.fiber_bound (nu := nu) inputs 2 (originalLeaf leaf) position
    wave i j response outside l m p q index
  have firstPaid := mul_le_mul_of_nonneg_right (kernel_bound (nu := nu) leaf wave i j outside l m index)
    (show 0 ≤ 3*‖inputs 0‖*‖inputs 1‖ by positivity)
  have paid := mul_le_mul firstPaid (remaining_bound inputs leaf position wave i j outside l m index) (norm_nonneg _)
    (by positivity [coefficient_nonnegative nu, NativeUnheatedSexticShiftCriticalSum.profile_nonnegative wave (last leaf index) (first index) (middle wave index)])
  exact generated.trans (paid.trans_eq (by
    unfold majorant NativeUnheatedSexticShiftCriticalSum.term NativeUnheatedSchurThree.term
    change _ = (3*coefficient nu*‖inputs 0‖*‖inputs 1‖)*
      (NativeUnheatedSexticShiftCriticalSum.profile wave (last leaf index) (first index) (middle wave index)*
        |rows inputs 4 (last leaf index)| *|rows inputs 2 (first index)| *|rows inputs 3 (middle wave index)|)
    ring))

theorem majorant_summable (inputs : Fin 5 → NativeUnheatedTriadSum.E) (leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)  :
    Summable (majorant (nu := nu) inputs leaf position wave) := by
  exact ((indexEquiv leaf wave).summable_iff.mpr (NativeUnheatedSexticShiftCriticalSum.summable wave
    (rows inputs 4) (rows inputs 2) (rows inputs 3))).mul_left _

theorem generic_summable (inputs : Fin 5 → NativeUnheatedTriadSum.E) (leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate)  :
    Summable (fun index => ‖multilinearTerm inputs nu 2 (originalLeaf leaf) position wave i j response outside l m p q index‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun index => NativeUnheatedSexticCollapse.fiber_summable (nu := nu) inputs 2 (originalLeaf leaf) position wave i j response outside l m p q index,
    (majorant_summable (nu := nu) inputs leaf position wave).of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
      (fun index => fiber_bound inputs leaf position wave i j response outside l m p q index)⟩

theorem generic_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) :
    (∑' index, ‖multilinearTerm inputs nu 2 (originalLeaf leaf) position wave i j response outside l m p q index‖) ≤
      48*coefficient nu*NativeUnheatedSexticShiftSchur.cap wave*(∏ number : Fin 5, ‖inputs number‖) := by
  have sums := generic_summable (nu := nu) inputs leaf position wave i j response outside l m p q
  rw [sums.tsum_prod]
  have compare := sums.prod.tsum_le_tsum (fun index => fiber_bound (nu := nu) inputs leaf position wave i j response outside l m p q index)
    (majorant_summable (nu := nu) inputs leaf position wave)
  simp_rw [majorant] at compare
  rw [tsum_mul_left, (indexEquiv leaf wave).tsum_eq] at compare
  have sumBound := NativeUnheatedSexticShiftCriticalSum.bound wave (rows inputs 4) (rows inputs 2) (rows inputs 3)
  simp only [rows, NativeUnheatedTriadSum.rowNorms_norm] at sumBound
  have paid := mul_le_mul_of_nonneg_left sumBound
    (by positivity [coefficient_nonnegative nu] : (0 : ℝ) ≤ 3*coefficient nu*‖inputs 0‖*‖inputs 1‖)
  apply (compare.trans paid).trans_eq
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_three]
  change _ = 48*coefficient nu*NativeUnheatedSexticShiftSchur.cap wave*(‖inputs 0‖*(‖inputs 1‖*(‖inputs 2‖*‖inputs 3‖*‖inputs 4‖)))
  ring

def budget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  48*coefficient nu*400000*NativeUnheatedHalfNonlinear.coefficient*NativeUnifiedCompleteSource.budget seed^4

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (time : ℝ) :
    Summable (fun index => ‖term seed 2 (originalLeaf leaf) position wave i j response outside l m p q index time‖) :=
  generic_summable (nu := nu) (fun number => input seed position number time) leaf position wave i j response outside l m p q

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (time : ℝ) :
    (∑' index, ‖term seed 2 (originalLeaf leaf) position wave i j response outside l m p q index time‖) ≤
      budget seed*NativeUnheatedSexticLatticePower.radical wave*NativeUnheatedSourceGradient.mass seed time := by
  have full := generic_bound (nu := nu) (fun number => input seed position number time) leaf position wave i j response outside l m p q
  have paid := mul_le_mul_of_nonneg_left (input_product seed position time)
    (by positivity [coefficient_nonnegative nu, NativeUnheatedSexticShiftSchur.cap_nonnegative wave] :
      (0 : ℝ) ≤ 48*coefficient nu*NativeUnheatedSexticShiftSchur.cap wave)
  exact full.trans (paid.trans_eq (by unfold budget NativeUnheatedSexticShiftSchur.cap; ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticOuterCombSource
