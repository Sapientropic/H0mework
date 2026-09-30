import H0mework.Chemistry.LAlanineTrueTube.SourceData
import H0mework.Chemistry.LAlanineContinuousSource.CellGeometry

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeChecks

open TrueTubeSource SourceGaussianModel SourceSignedEvaluator IntervalParameterMap
noncomputable section

theorem step_value : stepSize = 1 / 32 := by decide +kernel
theorem step_positive : 0 < stepSize := by decide +kernel
theorem directions : sign 0 = -1 ∧ sign 1 = 1 := by decide +kernel
theorem direction_units : ∀ d : Direction, |sign d| = 1 ∧ sign d * sign d = 1 := by decide +kernel

theorem first_initial_cells : ∀ d : Direction, ∀ axis : Fin 3,
    initialBox d 0 axis = SourceCellGeometry.initialJetBox.position axis := by decide +kernel

theorem first_initial_eq (d : Direction) :
    initialBox d 0 = SourceCellGeometry.initialJetBox.position :=
  funext (first_initial_cells d)

theorem initial_field_cells : ∀ d : Direction, ∀ axis : Fin 3,
    box 0 axis = initialBox d 0 axis := by decide +kernel
theorem initial_field_eq (d : Direction) : box 0 = initialBox d 0 :=
  funext (initial_field_cells d)

theorem first_tube_field_cells : ∀ d : Direction, ∀ axis : Fin 3,
    box (firstTubeField d) axis = tubeBox d 0 axis := by decide +kernel
theorem first_tube_field_eq (d : Direction) : box (firstTubeField d) = tubeBox d 0 :=
  funext (first_tube_field_cells d)

theorem initial_ordered : ∀ d : Direction, ∀ i : Step, ∀ axis : Fin 3,
    (initialBox d i axis).1 ≤ (initialBox d i axis).2 := by decide +kernel
theorem tube_ordered : ∀ d : Direction, ∀ i : Step, ∀ axis : Fin 3,
    (tubeBox d i axis).1 ≤ (tubeBox d i axis).2 := by decide +kernel
theorem endpoint_ordered : ∀ d : Direction, ∀ i : Step, ∀ axis : Fin 3,
    (endpointBox d i axis).1 ≤ (endpointBox d i axis).2 := by decide +kernel

theorem endpoint_next_initial_cells : ∀ d : Direction, ∀ i : Fin 15, ∀ axis : Fin 3,
    endpointBox d i.castSucc axis = initialBox d i.succ axis := by decide +kernel
theorem endpoint_next_initial (d : Direction) (i : Fin 15) :
    endpointBox d i.castSucc = initialBox d i.succ := funext (endpoint_next_initial_cells d i)

theorem time_step : ∀ d : Direction, ∀ i : Step,
    elapsedStop d i - elapsedStart d i = sign d * stepSize := by decide +kernel
theorem time_next_start : ∀ d : Direction, ∀ i : Fin 15,
    elapsedStop d i.castSucc = elapsedStart d i.succ := by decide +kernel
theorem time_endpoints : ∀ d : Direction,
    elapsedStart d 0 = 0 ∧ elapsedStop d 15 = sign d / 2 := by decide +kernel

theorem actual_row_addresses : ∀ d : Direction, ∀ i : Step,
    rowIndex d i = 512 + 16 * d.val + i.val ∧
      initialCall d i = 1024 + 2 * (16 * d.val + i.val) ∧ tubeCall d i = initialCall d i + 1 := by
  decide +kernel

theorem complete_source_joins :
    type_of% first_initial_eq ∧ type_of% initial_field_eq ∧ type_of% first_tube_field_eq ∧
    type_of% endpoint_next_initial ∧ type_of% time_step ∧ type_of% time_next_start ∧
    type_of% time_endpoints ∧ type_of% actual_row_addresses :=
  ⟨first_initial_eq, initial_field_eq, first_tube_field_eq, endpoint_next_initial,
    time_step, time_next_start, time_endpoints, actual_row_addresses⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
