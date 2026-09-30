import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.FiveLeaf
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Source

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticFiveRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeUnheatedSourceGradient NativeUnheatedQuarticAllSlots
noncomputable section
variable {nu : Viscosity}

abbrev Index := NativeUnheatedQuarticAllSlots.Index × IntegerWavevector

def base (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : NativeUnheatedQuarticAllSlots.Index) : ℂ :=
  NativeUnheatedQuarticKernel.normalizer nu (slots slot wave i j outside l m index 0)
    (slots slot wave i j outside l m index 1) (slots slot wave i j outside l m index 2)
    (slots slot wave i j outside l m index 3) (tree nu slot wave i j response outside l m index)

def nodes (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j outside l m p q : Coordinate) (index : Index) : Fin 5 → NativeUnheatedQuinticTime.Slot :=
  NativeUnheatedQuinticLeaf.slots (slots slot wave i j outside l m index.1) leaf p q index.2

theorem frequency (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j outside l m p q : Coordinate) (index : Index) :
    (∑ position : Fin 5, (nodes slot leaf wave i j outside l m p q index position).1) = wave := by
  let old := slots slot wave i j outside l m index.1
  have split : (∑ position : Fin 5, (nodes slot leaf wave i j outside l m p q index position).1) =
      ∑ position : Fin 4, (old position).1 := by
    rw [Fin.sum_univ_succAbove (fun position => (old position).1) leaf]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, ← add_assoc]
    change index.2+((old leaf).1-index.2)+(old (leaf.succAbove 0)).1+
      (old (leaf.succAbove 1)).1+(old (leaf.succAbove 2)).1 = _
    abel
  rw [split, Fin.sum_univ_four]
  fin_cases slot
  · change index.1.2+(index.1.1.2-index.1.2)+(wave-index.1.1.1-index.1.1.2)+index.1.1.1 = wave
    abel
  · change index.1.2+(wave-index.1.1.1-index.1.1.2-index.1.2)+index.1.1.2+index.1.1.1 = wave
    abel
  · change index.1.1.2+(wave-index.1.1.1-index.1.1.2)+index.1.2+(index.1.1.1-index.1.2) = wave
    abel

def kernel (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) : ℂ :=
  NativeUnheatedQuinticLeaf.kernel (base nu slot wave i j response outside l m index.1)
    (slots slot wave i j outside l m index.1) leaf p q

def term (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedQuinticLeaf.term seed (slots slot wave i j outside l m index.1)
    (base nu slot wave i j response outside l m index.1) leaf p q index.2 time

theorem term_original (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) (time : ℝ) :
    term seed slot leaf wave i j response outside l m p q index time =
      kernel nu slot leaf wave i j response outside l m p q index * NativeUnheatedQuinticTime.product seed
        (nodes slot leaf wave i j outside l m p q index 0) (nodes slot leaf wave i j outside l m p q index 1)
        (nodes slot leaf wave i j outside l m p q index 2) (nodes slot leaf wave i j outside l m p q index 3)
        (nodes slot leaf wave i j outside l m p q index 4) time :=
  NativeUnheatedQuinticLeaf.term_original seed _ _ leaf p q index.2 time

def packed (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector) (i j response outside l m : Coordinate)
    (inputs : Fin 4 → NativeUnheatedTriadSum.E) (index : NativeUnheatedQuarticAllSlots.Index) : ℂ :=
  NativeUnheatedQuinticInput.kernel nu slot leaf wave i j response outside l m index *
    ∏ position : Fin 4, inputs position (slots slot wave i j outside l m index position).1
      (slots slot wave i j outside l m index position).2

theorem packed_summable (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector) (i j response outside l m : Coordinate)
    (inputs : Fin 4 → NativeUnheatedTriadSum.E) :
    Summable (fun index => ‖packed (nu := nu) slot leaf wave i j response outside l m inputs index‖) := by
  simp only [packed, Fin.prod_univ_four]
  fin_cases slot
  · exact NativeUnheatedQuinticSum.absolute_summable _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => NativeUnheatedQuinticSource.source_kernel_bound 0 leaf wave i j response outside l m index)
      l m j outside (inputs 0) (inputs 1) (inputs 2) (inputs 3)
  · exact NativeUnheatedQuinticSum.middle_absolute_summable _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => NativeUnheatedQuinticSource.source_kernel_bound 1 leaf wave i j response outside l m index)
      l m i outside (inputs 0) (inputs 1) (inputs 2) (inputs 3)
  · exact NativeUnheatedQuinticSum.outer_absolute_summable _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => NativeUnheatedQuinticSource.source_kernel_bound 2 leaf wave i j response outside l m index)
      i j l m (inputs 0) (inputs 1) (inputs 2) (inputs 3)

theorem packed_bound (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector) (i j response outside l m : Coordinate)
    (inputs : Fin 4 → NativeUnheatedTriadSum.E) :
    (∑' index, ‖packed (nu := nu) slot leaf wave i j response outside l m inputs index‖) ≤
      NativeUnheatedQuinticSource.factor nu*‖inputs 0‖*‖inputs 1‖*‖inputs 2‖*‖inputs 3‖ := by
  simp only [packed, Fin.prod_univ_four]
  fin_cases slot
  · exact NativeUnheatedQuinticSum.absolute_bound _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => NativeUnheatedQuinticSource.source_kernel_bound 0 leaf wave i j response outside l m index)
      l m j outside (inputs 0) (inputs 1) (inputs 2) (inputs 3)
  · exact NativeUnheatedQuinticSum.middle_absolute_bound _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => NativeUnheatedQuinticSource.source_kernel_bound 1 leaf wave i j response outside l m index)
      l m i outside (inputs 0) (inputs 1) (inputs 2) (inputs 3)
  · exact NativeUnheatedQuinticSum.outer_absolute_bound _ (NativeUnheatedQuinticWeights.cap nu) wave
      (fun index => NativeUnheatedQuinticSource.source_kernel_bound 2 leaf wave i j response outside l m index)
      i j l m (inputs 0) (inputs 1) (inputs 2) (inputs 3)

theorem fiber_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : NativeUnheatedQuarticAllSlots.Index) (time : ℝ) :
    Summable (fun inside => term seed slot leaf wave i j response outside l m p q (index,inside) time) :=
  NativeUnheatedQuinticLeaf.raw_summable (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    (slots slot wave i j outside l m index) (base nu slot wave i j response outside l m index) leaf p q

theorem fiber_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : NativeUnheatedQuarticAllSlots.Index) (time : ℝ)
    (nonnegative : 0 ≤ time) (regular : H1 (physical seed time nonnegative)) :
    (∑' inside, ‖term seed slot leaf wave i j response outside l m p q (index,inside) time‖) ≤
      ‖packed (nu := nu) slot leaf wave i j response outside l m
        (NativeUnheatedQuinticPositive.input (physical seed time nonnegative) regular leaf) index‖ :=
  NativeUnheatedQuinticLeaf.fiber_bound (physical seed time nonnegative) regular
    (slots slot wave i j outside l m index) (base nu slot wave i j response outside l m index) leaf p q

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    Summable (fun index => ‖term seed slot leaf wave i j response outside l m p q index time‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun index => (fiber_summable seed slot leaf wave i j response outside l m p q index time).norm,
    (packed_summable (nu := nu) slot leaf wave i j response outside l m _).of_nonneg_of_le
      (fun _ => tsum_nonneg fun _ => norm_nonneg _)
      (fun index => fiber_bound seed slot leaf wave i j response outside l m p q index time nonnegative regular)⟩

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    (∑' index, ‖term seed slot leaf wave i j response outside l m p q index time‖) ≤
      NativeUnheatedQuinticSource.bound seed*mass seed time := by
  let inputs := NativeUnheatedQuinticPositive.input (physical seed time nonnegative) regular leaf
  have sums := absolute_summable seed slot leaf wave i j response outside l m p q time nonnegative regular
  rw [sums.tsum_prod]
  have compare := sums.prod.tsum_le_tsum
    (fun index => fiber_bound seed slot leaf wave i j response outside l m p q index time nonnegative regular)
    (packed_summable (nu := nu) slot leaf wave i j response outside l m inputs)
  apply (compare.trans (packed_bound (nu := nu) slot leaf wave i j response outside l m inputs)).trans
  have positive := NativeUnheatedQuinticPositive.input_product (physical seed time nonnegative) regular leaf
  have velocity : ‖wholeVelocity (physical seed time nonnegative).1‖ ≤ NativeUnifiedCompleteSource.budget seed :=
    (wholeVelocity_norm_le _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed time)
  have paid := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) velocity 3)
      (mul_nonneg NativeUnheatedHalfNonlinear.coefficient_nonnegative (show 0 ≤ gradientMass (physical seed time nonnegative) from tsum_nonneg (gradient_nonnegative _))))
    (NativeUnheatedQuinticSource.factor_nonnegative nu)
  have total := (mul_le_mul_of_nonneg_left positive (NativeUnheatedQuinticSource.factor_nonnegative nu))
  rw [physical_mass] at total paid
  calc
    _ = NativeUnheatedQuinticSource.factor nu*(‖inputs 0‖*‖inputs 1‖*‖inputs 2‖*‖inputs 3‖) := by ring
    _ ≤ _ := total
    _ ≤ _ := by convert! paid using 1; ring
    _ = _ := by unfold NativeUnheatedQuinticSource.bound; ring

theorem original_row (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : NativeUnheatedQuarticAllSlots.Index) (time : ℝ)
    (nonnegative : 0 ≤ time) (regular : H1 (physical seed time nonnegative)) :
    quinticTerm seed slot wave i j response outside l m index time =
      ∑ leaf : Fin 4, ∑ p : Coordinate, ∑ q : Coordinate, ∑' inside,
        term seed slot leaf wave i j response outside l m p q (index,inside) time :=
  NativeUnheatedQuinticLeaf.source_expansion seed _ _ time nonnegative regular

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticFiveRows
