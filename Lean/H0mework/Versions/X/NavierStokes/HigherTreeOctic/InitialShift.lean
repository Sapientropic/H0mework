import H0mework.Versions.X.NavierStokes.HigherTreeOctic.KernelBound
import H0mework.Versions.X.NavierStokes.WindowSourceSobolev.PreparationSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator.ButterflyStackedExpansionMaterial
noncomputable section

theorem original_velocity_zero (wave : IntegerWavevector) (coordinate : Coordinate)
    (outside : wave ∉ butterflyFirstStackModes) :
    NativeUnheatedTriadRows.velocity stackedShortCurrent 0 wave coordinate = 0 := by
  rw [NativeUnheatedTriadRows.velocity_original,
    NativeWindowPreparedSobolevSource.initial_row,
    NativeWindowPreparationInitial.velocity_original]
  simp [ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.finiteStateVelocityCoefficient,
    stackedSeedState, butterflyFirstStackPhysicalState_supported (-1) wave outside]

theorem original_product_zero (slots : Fin 7 → NativeUnheatedTreeTime.Slot)
    (position : Fin 7) (outside : (slots position).1 ∉ butterflyFirstStackModes) :
    NativeUnheatedTreeTime.product stackedShortCurrent slots 0 = 0 := by
  unfold NativeUnheatedTreeTime.product
  exact Finset.prod_eq_zero (Finset.mem_univ position)
    (original_velocity_zero (slots position).1 (slots position).2 outside)

noncomputable def originalShiftSupport : Finset IntegerWavevector := by
  classical
  exact (Finset.univ : Finset (Fin 7 → {wave : IntegerWavevector // wave ∈ butterflyFirstStackModes})).image
    (fun waves => ∑ position : Fin 7, (waves position).1)

theorem slots_initial_shift_supported
    (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (i j outside l m p q r s u v : Coordinate) (selected : Fin 7) (b : Coordinate)
    (entry : Address)
    (supported : ∀ number : Fin 7,
      ((slots slot leaf position newest i j outside l m p q r s u v selected b entry) number).1 ∈ butterflyFirstStackModes) :
    entry.1-entry.2.2 ∈ originalShiftSupport := by
  classical
  let waves : Fin 7 → {wave : IntegerWavevector // wave ∈ butterflyFirstStackModes} :=
    fun number => ⟨((slots slot leaf position newest i j outside l m p q r s u v selected b entry) number).1,
      supported number⟩
  have total : (∑ number : Fin 7, (waves number).1) = entry.1-entry.2.2 :=
    slots_frequency slot leaf position newest i j outside l m p q r s u v selected b entry
  unfold originalShiftSupport
  exact Finset.mem_image.mpr ⟨waves, Finset.mem_univ _, total⟩

theorem original_product_zero_of_shift_outside
    (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (i j outside l m p q r s u v : Coordinate) (selected : Fin 7) (b : Coordinate)
    (entry : Address) (outsideShift : entry.1-entry.2.2 ∉ originalShiftSupport) :
    NativeUnheatedTreeTime.product stackedShortCurrent
      (slots slot leaf position newest i j outside l m p q r s u v selected b entry) 0 = 0 := by
  by_contra nonzero
  have supported (number : Fin 7) :
      ((slots slot leaf position newest i j outside l m p q r s u v selected b entry) number).1 ∈ butterflyFirstStackModes := by
    by_contra outsideMode
    exact nonzero (original_product_zero
      (slots slot leaf position newest i j outside l m p q r s u v selected b entry) number outsideMode)
  exact outsideShift (slots_initial_shift_supported slot leaf position newest i j outside l m p q r s u v
    selected b entry supported)

theorem vector_initial_restrict
    (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)
    (test : Test) (observed : Finset Address) :
    vector slot leaf position newest i j response outside l m p q r s u v selected a b test
      stackedShortCurrent observed 0 =
    vector slot leaf position newest i j response outside l m p q r s u v selected a b test
      stackedShortCurrent (observed.filter (fun entry => entry.1-entry.2.2 ∈ originalShiftSupport)) 0 := by
  classical
  rw [vector_source, vector_source, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases supported : entry.1-entry.2.2 ∈ originalShiftSupport
  · simp [supported]
  · simp [supported, original_product_zero_of_shift_outside slot leaf position newest i j outside l m p q r s u v
      selected b entry supported]

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
