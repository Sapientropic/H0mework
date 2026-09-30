import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CriticalSum
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CombKernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticCombSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedSexticCombKernel NativeUnheatedSexticInput
noncomputable section
variable {nu : Viscosity}

abbrev Index := NativeUnheatedQuarticAllSlots.Index

def indexEquiv (slot leaf : Fin 2) (wave : IntegerWavevector) : Index ≃ (IntegerWavevector × IntegerWavevector) × IntegerWavevector where
  toFun index := ((middle slot wave index,index.1.1),first slot leaf wave index)
  invFun index := ((index.1.2,if slot=0 then wave-index.1.2-index.1.1 else index.1.1),
    if leaf=0 then wave-index.1.2-index.1.1-index.2 else index.2)
  left_inv := by
    rintro ⟨⟨c,a⟩,d⟩
    by_cases firstSlot : slot=0 <;> by_cases firstLeaf : leaf=0
    all_goals simp only [middle, first, firstSlot, firstLeaf, if_true, if_false]
    all_goals congr 1 <;> (congr 1; abel)
  right_inv := by
    rintro ⟨⟨b,c⟩,r⟩
    by_cases firstSlot : slot=0 <;> by_cases firstLeaf : leaf=0
    all_goals simp only [middle, first, firstSlot, firstLeaf, if_true, if_false]
    all_goals congr 1 <;> (congr 1; abel)

def rows (inputs : Fin 5 → NativeUnheatedTriadSum.E) (number : Fin 5) :
    NativeUnheatedSchur.Space IntegerWavevector := NativeUnheatedTriadSum.rowNorms (inputs number)

theorem remaining_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot leaf : Fin 2) (position : Fin 5)
    (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index)  :
    ‖NativeUnheatedSexticCollapse.remaining inputs (originalSlot slot) (originalLeaf leaf) position wave i j outside l m index‖ ≤
      |rows inputs 2 (first slot leaf wave index)| *|rows inputs 3 (middle slot wave index)| *
        |rows inputs 4 index.1.1| := by
  rw [NativeUnheatedSexticCollapse.remaining, norm_prod]
  have point (number : Fin 3) : ‖inputs number.succ.succ
      (NativeUnheatedQuarticAllSlots.slots (originalSlot slot) wave i j outside l m index ((originalLeaf leaf).succAbove number)).1
      (NativeUnheatedQuarticAllSlots.slots (originalSlot slot) wave i j outside l m index ((originalLeaf leaf).succAbove number)).2‖ ≤
        ‖inputs number.succ.succ (![first slot leaf wave index,middle slot wave index,index.1.1] number)‖ := by
    rw [← remaining_waves slot leaf wave i j outside l m index number]
    exact norm_le_pi_norm _ _
  have paid := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3))) (fun number _ => norm_nonneg _) (fun number _ => point number)
  apply paid.trans_eq
  rw [Fin.prod_univ_three]
  change ‖inputs 2 (first slot leaf wave index)‖*‖inputs 3 (middle slot wave index)‖*
    ‖inputs 4 index.1.1‖ = _
  simp only [rows, NativeUnheatedTriadSum.rowNorms, abs_norm]

def majorant (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot leaf : Fin 2) (_position : Fin 5) (wave : IntegerWavevector)
     (index : Index) : ℝ :=
  (3*coefficient nu*‖inputs 0‖*‖inputs 1‖)*
    NativeUnheatedSexticCriticalSum.term (rows inputs 2) (rows inputs 3) (rows inputs 4)
      (indexEquiv slot leaf wave index)

theorem fiber_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index)  :
    (∑' inside, ‖multilinearTerm inputs nu (originalSlot slot) (originalLeaf leaf) position wave i j response outside l m p q (index,inside)‖) ≤
      majorant (nu := nu) inputs slot leaf position wave index := by
  have generated := NativeUnheatedSexticCollapse.fiber_bound (nu := nu) inputs (originalSlot slot) (originalLeaf leaf) position
    wave i j response outside l m p q index
  have firstPaid := mul_le_mul_of_nonneg_right (kernel_bound (nu := nu) slot leaf wave i j outside l m index)
    (show 0 ≤ 3*‖inputs 0‖*‖inputs 1‖ by positivity)
  have paid := mul_le_mul firstPaid (remaining_bound inputs slot leaf position wave i j outside l m index) (norm_nonneg _)
    (by positivity [coefficient_nonnegative nu, NativeUnheatedSexticCriticalSum.profile_nonnegative (first slot leaf wave index) (middle slot wave index) index.1.1])
  exact generated.trans (paid.trans_eq (by
    unfold majorant NativeUnheatedSexticCriticalSum.term NativeUnheatedSchurThree.term
    change _ = (3*coefficient nu*‖inputs 0‖*‖inputs 1‖)*
      (NativeUnheatedSexticCriticalSum.profile (first slot leaf wave index) (middle slot wave index) index.1.1*
        |rows inputs 2 (first slot leaf wave index)| *|rows inputs 3 (middle slot wave index)| *|rows inputs 4 index.1.1|)
    ring))

theorem majorant_summable (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)  :
    Summable (majorant (nu := nu) inputs slot leaf position wave) := by
  exact ((indexEquiv slot leaf wave).summable_iff.mpr (NativeUnheatedSexticCriticalSum.summable
    (rows inputs 2) (rows inputs 3) (rows inputs 4))).mul_left _

theorem generic_summable (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate)  :
    Summable (fun index => ‖multilinearTerm inputs nu (originalSlot slot) (originalLeaf leaf) position wave i j response outside l m p q index‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun index => NativeUnheatedSexticCollapse.fiber_summable (nu := nu) inputs (originalSlot slot) (originalLeaf leaf) position wave i j response outside l m p q index,
    (majorant_summable (nu := nu) inputs slot leaf position wave).of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
      (fun index => fiber_bound inputs slot leaf position wave i j response outside l m p q index)⟩

theorem generic_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) :
    (∑' index, ‖multilinearTerm inputs nu (originalSlot slot) (originalLeaf leaf) position wave i j response outside l m p q index‖) ≤
      24576*coefficient nu*(∏ number : Fin 5, ‖inputs number‖) := by
  have sums := generic_summable (nu := nu) inputs slot leaf position wave i j response outside l m p q
  rw [sums.tsum_prod]
  have compare := sums.prod.tsum_le_tsum (fun index => fiber_bound (nu := nu) inputs slot leaf position wave i j response outside l m p q index)
    (majorant_summable (nu := nu) inputs slot leaf position wave)
  simp_rw [majorant] at compare
  rw [tsum_mul_left, (indexEquiv slot leaf wave).tsum_eq] at compare
  have sumBound := NativeUnheatedSexticCriticalSum.bound (rows inputs 2) (rows inputs 3) (rows inputs 4)
  simp only [rows, NativeUnheatedTriadSum.rowNorms_norm] at sumBound
  have paid := mul_le_mul_of_nonneg_left sumBound
    (by positivity [coefficient_nonnegative nu] : (0 : ℝ) ≤ 3*coefficient nu*‖inputs 0‖*‖inputs 1‖)
  apply (compare.trans paid).trans_eq
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_three]
  change _ = 24576*coefficient nu*(‖inputs 0‖*(‖inputs 1‖*(‖inputs 2‖*‖inputs 3‖*‖inputs 4‖)))
  ring

def budget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  24576*coefficient nu*NativeUnheatedHalfNonlinear.coefficient*NativeUnifiedCompleteSource.budget seed^4

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (slot leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (time : ℝ) :
    Summable (fun index => ‖term seed (originalSlot slot) (originalLeaf leaf) position wave i j response outside l m p q index time‖) :=
  generic_summable (nu := nu) (fun number => input seed position number time) slot leaf position wave i j response outside l m p q

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (slot leaf : Fin 2) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (time : ℝ) :
    (∑' index, ‖term seed (originalSlot slot) (originalLeaf leaf) position wave i j response outside l m p q index time‖) ≤
      budget seed*NativeUnheatedSourceGradient.mass seed time := by
  have full := generic_bound (nu := nu) (fun number => input seed position number time) slot leaf position wave i j response outside l m p q
  have paid := mul_le_mul_of_nonneg_left (input_product seed position time)
    (by positivity [coefficient_nonnegative nu] : (0 : ℝ) ≤ 24576*coefficient nu)
  exact full.trans (paid.trans_eq (by unfold budget; ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticCombSource
