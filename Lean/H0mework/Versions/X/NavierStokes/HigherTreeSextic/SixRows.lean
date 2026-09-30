import H0mework.Versions.X.NavierStokes.HigherTreeSexticUniform.AllSlots
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Leaf

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticSixRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeUnheatedSourceGradient
noncomputable section
variable {nu : Viscosity}

abbrev Index := NativeUnheatedQuinticFiveRows.Index × IntegerWavevector

def base (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : NativeUnheatedQuinticFiveRows.Index) : ℂ :=
  NativeUnheatedQuinticNormalForm.normalizer nu
    (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index 0)
    (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index 1)
    (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index 2)
    (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index 3)
    (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index 4)
    (NativeUnheatedQuinticFiveRows.kernel nu slot leaf wave i j response outside l m p q index)

def nodes (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j outside l m p q r s : Coordinate) (index : Index) : Fin 6 → NativeUnheatedQuinticTime.Slot :=
  NativeUnheatedTreeLeaf.slots (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index.1)
    position r s index.2

theorem frequency (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j outside l m p q r s : Coordinate) (index : Index) :
    (∑ number : Fin 6, (nodes slot leaf position wave i j outside l m p q r s index number).1) = wave :=
  (NativeUnheatedTreeLeaf.slots_frequency _ position r s index.2).trans
    (NativeUnheatedQuinticFiveRows.frequency slot leaf wave i j outside l m p q index.1)

def kernel (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : Index) : ℂ :=
  NativeUnheatedTreeLeaf.kernel (base nu slot leaf wave i j response outside l m p q index.1)
    (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index.1) position r s

def term (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeLeaf.term seed (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index.1)
    (base nu slot leaf wave i j response outside l m p q index.1) position r s index.2 time

theorem term_product (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : Index) (time : ℝ) :
    term seed slot leaf position wave i j response outside l m p q r s index time =
      kernel nu slot leaf position wave i j response outside l m p q r s index*
        ∏ number : Fin 6, NativeUnheatedTriadRows.velocity seed time
          (nodes slot leaf position wave i j outside l m p q r s index number).1
          (nodes slot leaf position wave i j outside l m p q r s index number).2 :=
  NativeUnheatedTreeLeaf.term_product seed _ _ position r s index.2 time

theorem fiber_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate)
    (index : NativeUnheatedQuinticFiveRows.Index) (time : ℝ) :
    Summable (fun inside => term seed slot leaf position wave i j response outside l m p q r s (index,inside) time) :=
  NativeUnheatedTreeLeaf.raw_summable (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index)
    (base nu slot leaf wave i j response outside l m p q index) position r s

theorem fiber_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate)
    (index : NativeUnheatedQuinticFiveRows.Index) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    (∑' inside, ‖term seed slot leaf position wave i j response outside l m p q r s (index,inside) time‖) ≤
      ‖NativeUnheatedSexticInput.multilinearTerm (NativeUnheatedTreeLeaf.positiveInput (physical seed time nonnegative) regular position)
        nu slot leaf position wave i j response outside l m p q index‖ :=
  NativeUnheatedTreeLeaf.fiber_bound (physical seed time nonnegative) regular
    (NativeUnheatedQuinticFiveRows.nodes slot leaf wave i j outside l m p q index)
    (base nu slot leaf wave i j response outside l m p q index) position r s

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (time : ℝ)
    (nonnegative : 0 ≤ time) (regular : H1 (physical seed time nonnegative)) :
    Summable (fun index => ‖term seed slot leaf position wave i j response outside l m p q r s index time‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun index => (fiber_summable seed slot leaf position wave i j response outside l m p q r s index time).norm,
    (NativeUnheatedSexticUniformAllSlots.generic_summable _ slot leaf position wave i j response outside l m p q).of_nonneg_of_le
      (fun _ => tsum_nonneg fun _ => norm_nonneg _)
      (fun index => fiber_bound seed slot leaf position wave i j response outside l m p q r s index time nonnegative regular)⟩

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate) (time : ℝ)
    (nonnegative : 0 ≤ time) (regular : H1 (physical seed time nonnegative)) :
    (∑' index, ‖term seed slot leaf position wave i j response outside l m p q r s index time‖) ≤
      NativeUnheatedSexticUniformAllSlots.budget seed*mass seed time := by
  let inputs := NativeUnheatedTreeLeaf.positiveInput (physical seed time nonnegative) regular position
  have sums := absolute_summable seed slot leaf position wave i j response outside l m p q r s time nonnegative regular
  rw [sums.tsum_prod]
  have compare := sums.prod.tsum_le_tsum
    (fun index => fiber_bound seed slot leaf position wave i j response outside l m p q r s index time nonnegative regular)
    (NativeUnheatedSexticUniformAllSlots.generic_summable inputs slot leaf position wave i j response outside l m p q)
  have generated := NativeUnheatedSexticUniformAllSlots.generic_bound (nu := nu) inputs slot leaf position wave i j response outside l m p q
  have velocity : ‖wholeVelocity (physical seed time nonnegative).1‖ ≤ NativeUnifiedCompleteSource.budget seed :=
    (wholeVelocity_norm_le _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed time)
  have positive := NativeUnheatedTreeLeaf.input_product (physical seed time nonnegative) regular position
  have paid := positive.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) velocity 4)
    (mul_nonneg NativeUnheatedHalfNonlinear.coefficient_nonnegative (tsum_nonneg (gradient_nonnegative _))))
  rw [physical_mass] at paid
  exact (compare.trans generated).trans ((mul_le_mul_of_nonneg_left paid
    (NativeUnheatedSexticUniformAllSlots.cap_nonnegative nu)).trans_eq (by
      unfold NativeUnheatedSexticUniformAllSlots.budget; ring))

theorem five_forcing (seed : GeneratedWholeRestartCurrent nu) (old : Fin 5 → NativeUnheatedTreeTime.Slot) (time : ℝ) :
    NativeUnheatedQuinticTime.forcing seed (old 0) (old 1) (old 2) (old 3) (old 4) time =
      NativeUnheatedTreeTime.forcing seed old time := by
  have cofactor (leaf : Fin 5) : NativeUnheatedTreeTime.cofactor seed old leaf time =
      NativeUnheatedTreeLeaf.remaining (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) old leaf := by
    simp only [NativeUnheatedTreeTime.cofactor, NativeUnheatedTreeLeaf.remaining_erase,
      NativeUnheatedTriadRows.velocity_original]
  simp only [NativeUnheatedTreeTime.forcing, cofactor]
  rw [Fin.sum_univ_succ, Fin.sum_univ_four]
  simp only [NativeUnheatedTreeLeaf.remaining, Fin.prod_univ_four, NativeUnheatedQuinticTime.forcing,
    NativeUnheatedTriadRows.velocity_original]
  let v (number : Fin 5) := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (old number).1 (old number).2
  let a (number : Fin 5) := NativeUnheatedTriadRows.action seed time (old number).1 (old number).2
  change _ = a 0*(v 1*v 2*v 3*v 4)+(a 1*(v 0*v 2*v 3*v 4)+a 2*(v 0*v 1*v 3*v 4)+
    a 3*(v 0*v 1*v 2*v 4)+a 4*(v 0*v 1*v 2*v 3))
  dsimp only [v, a]
  ring

theorem original_row (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate)
    (index : NativeUnheatedQuinticFiveRows.Index) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    NativeUnheatedQuinticPrimitiveKernel.sexticTerm seed slot leaf wave i j response outside l m p q index time =
      ∑ position : Fin 5, ∑ r : Coordinate, ∑ s : Coordinate, ∑' inside,
        term seed slot leaf position wave i j response outside l m p q r s (index,inside) time := by
  change base nu slot leaf wave i j response outside l m p q index *
    NativeUnheatedQuinticTime.forcing seed _ _ _ _ _ time = _
  rw [five_forcing]
  exact NativeUnheatedTreeLeaf.source_expansion seed _ _ time nonnegative regular

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticSixRows
