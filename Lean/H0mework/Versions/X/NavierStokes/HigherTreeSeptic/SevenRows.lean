import H0mework.Versions.X.NavierStokes.HigherTreeSeptic.Input
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Leaf

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSepticSevenRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeUnheatedSourceGradient
noncomputable section
variable {nu : Viscosity}

abbrev Index := NativeUnheatedSexticSixRows.Index × IntegerWavevector

def base (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : NativeUnheatedSexticSixRows.Index) : ℂ :=
  NativeUnheatedTreeNormalForm.normalizer nu
    (NativeUnheatedSexticSixRows.nodes slot leaf position wave i j outside l m p q r s index)
    (NativeUnheatedSexticSixRows.kernel nu slot leaf position wave i j response outside l m p q r s index)

def nodes (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6) (wave : IntegerWavevector)
    (i j outside l m p q r s u v : Coordinate) (index : Index) : Fin 7 → NativeUnheatedTreeTime.Slot :=
  NativeUnheatedTreeLeaf.slots (NativeUnheatedSexticSixRows.nodes slot leaf position wave i j outside l m p q r s index.1)
    newest u v index.2

theorem nodes_frequency (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6) (wave : IntegerWavevector)
    (i j outside l m p q r s u v : Coordinate) (index : Index) :
    (∑ number : Fin 7, (nodes slot leaf position newest wave i j outside l m p q r s u v index number).1) = wave :=
  (NativeUnheatedTreeLeaf.slots_frequency _ newest u v index.2).trans
    (NativeUnheatedSexticSixRows.frequency slot leaf position wave i j outside l m p q r s index.1)

def kernel (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6) (wave : IntegerWavevector)
    (i j response outside l m p q r s u v : Coordinate) (index : Index) : ℂ :=
  NativeUnheatedTreeLeaf.kernel (base nu slot leaf position wave i j response outside l m p q r s index.1)
    (NativeUnheatedSexticSixRows.nodes slot leaf position wave i j outside l m p q r s index.1) newest u v

def term (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeLeaf.term seed
    (NativeUnheatedSexticSixRows.nodes slot leaf position wave i j outside l m p q r s index.1)
    (base nu slot leaf position wave i j response outside l m p q r s index.1) newest u v index.2 time

theorem term_product (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index) (time : ℝ) :
    term seed slot leaf position newest wave i j response outside l m p q r s u v index time =
      kernel nu slot leaf position newest wave i j response outside l m p q r s u v index*
        NativeUnheatedTreeTime.product seed (nodes slot leaf position newest wave i j outside l m p q r s u v index) time :=
  NativeUnheatedTreeLeaf.term_product seed _ _ newest u v index.2 time

theorem fiber_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate)
    (index : NativeUnheatedSexticSixRows.Index) (time : ℝ) :
    Summable (fun inside => term seed slot leaf position newest wave i j response outside l m p q r s u v (index,inside) time) :=
  NativeUnheatedTreeLeaf.raw_summable (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    (NativeUnheatedSexticSixRows.nodes slot leaf position wave i j outside l m p q r s index)
    (base nu slot leaf position wave i j response outside l m p q r s index) newest u v

theorem fiber_absolute_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate)
    (index : NativeUnheatedSexticSixRows.Index) (time : ℝ) :
    Summable (fun inside => ‖term seed slot leaf position newest wave i j response outside l m p q r s u v (index,inside) time‖) :=
  (fiber_summable seed slot leaf position newest wave i j response outside l m p q r s u v index time).norm

theorem fiber_positive_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate)
    (index : NativeUnheatedSexticSixRows.Index) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    (∑' inside, ‖term seed slot leaf position newest wave i j response outside l m p q r s u v (index,inside) time‖) ≤
      ‖NativeUnheatedSepticInput.multilinearTerm (NativeUnheatedTreeLeaf.positiveInput (physical seed time nonnegative) regular newest)
        nu slot leaf position newest wave i j response outside l m p q r s index‖ :=
  NativeUnheatedTreeLeaf.fiber_bound (physical seed time nonnegative) regular
    (NativeUnheatedSexticSixRows.nodes slot leaf position wave i j outside l m p q r s index)
    (base nu slot leaf position wave i j response outside l m p q r s index) newest u v

theorem fiber_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate)
    (index : NativeUnheatedSexticSixRows.Index) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    (∑' inside, ‖term seed slot leaf position newest wave i j response outside l m p q r s u v (index,inside) time‖) ≤
      ‖NativeUnheatedSepticInput.kernel nu slot leaf position newest wave i j response outside l m p q r s index‖*
        (NativeUnheatedHalfNonlinear.coefficient*mass seed time*NativeUnifiedCompleteSource.budget seed^5) := by
  apply (fiber_positive_bound seed slot leaf position newest wave i j response outside l m p q r s u v index time nonnegative regular).trans
  apply (NativeUnheatedTreeInput.multilinear_norm _ _ _ newest).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have paid := NativeUnheatedTreeLeaf.input_product (physical seed time nonnegative) regular newest
  have velocity : ‖wholeVelocity (physical seed time nonnegative).1‖ ≤ NativeUnifiedCompleteSource.budget seed :=
    (wholeVelocity_norm_le _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed time)
  rw [physical_mass] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) velocity 5)
    (mul_nonneg NativeUnheatedHalfNonlinear.coefficient_nonnegative (mass_nonnegative seed time)))

theorem fiber_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ slot leaf position newest wave i j response outside l m p q r s u v index,
      (∑' inside, ‖term seed slot leaf position newest wave i j response outside l m p q r s u v (index,inside) time‖) ≤
        ‖NativeUnheatedSepticInput.kernel nu slot leaf position newest wave i j response outside l m p q r s index‖*
          (NativeUnheatedHalfNonlinear.coefficient*mass seed time*NativeUnifiedCompleteSource.budget seed^5) := by
  filter_upwards [physical_H1_ae seed] with time actual nonnegative slot leaf position newest wave i j response outside l m p q r s u v index
  exact fiber_bound seed slot leaf position newest wave i j response outside l m p q r s u v index time nonnegative (actual nonnegative)

theorem original_septicrow (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q r s : Coordinate)
    (index : NativeUnheatedSexticSixRows.Index) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    NativeUnheatedSexticPrimitiveKernel.septicTerm seed slot leaf position wave i j response outside l m p q r s index time =
      ∑ newest : Fin 6, ∑ u : Coordinate, ∑ v : Coordinate, ∑' inside,
        term seed slot leaf position newest wave i j response outside l m p q r s u v (index,inside) time :=
  NativeUnheatedTreeLeaf.source_expansion seed _ _ time nonnegative regular

theorem original_septicrow_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ slot leaf position wave i j response outside l m p q r s index,
      NativeUnheatedSexticPrimitiveKernel.septicTerm seed slot leaf position wave i j response outside l m p q r s index time =
        ∑ newest : Fin 6, ∑ u : Coordinate, ∑ v : Coordinate, ∑' inside,
          term seed slot leaf position newest wave i j response outside l m p q r s u v (index,inside) time := by
  filter_upwards [physical_H1_ae seed] with time actual nonnegative slot leaf position wave i j response outside l m p q r s index
  exact original_septicrow seed slot leaf position wave i j response outside l m p q r s index time nonnegative (actual nonnegative)

theorem term_next (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    term seed slot leaf position newest wave i j response outside l m p q r s u v index (responseStep.2.clockAdvance+time) =
      term responseStep.1 slot leaf position newest wave i j response outside l m p q r s u v index time :=
  NativeUnheatedTreeLeaf.term_next seed _ _ newest u v index.2 responseStep generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeUnheatedSepticSevenRows
