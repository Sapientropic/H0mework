import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedInteraction.Flux
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondRenewal.Contract

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace CPS1AddressedInteraction
noncomputable section
open CPS1Deformation CPS1AddressedTransfer
open CPS1AddressedBondRenewal
open scoped BigOperators
variable {frame : CPS1Recycling.Frame}

def stepChannel {current : Source.Occurrence frame}
    (admission : NativeSource.Admission current) (index : Nat) :
    Channel (trajectory (NativeSource.initial admission) index).material.reference :=
  (signed_channel_exists
    (trajectory (NativeSource.initial admission) index).material
    (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
    (NativeSource.timeAt (NativeSource.initial admission) index)
    (NativeSource.generated_time_positive admission index)
    (NativeSource.generated_step_signed admission index)).choose

theorem step_channel_signed {current : Source.Occurrence frame}
    (admission : NativeSource.Admission current) (index : Nat) :
    let state := (trajectory (NativeSource.initial admission) index).material
    let nuclear := (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
    let time := NativeSource.timeAt (NativeSource.initial admission) index
    0 < responseFlux state nuclear 0 * contribution state nuclear time (stepChannel admission index) ∧
      contribution state nuclear time (stepChannel admission index) ≠ 0 := by
  dsimp only
  have member := (signed_channel_exists
    (trajectory (NativeSource.initial admission) index).material
    (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
    (NativeSource.timeAt (NativeSource.initial admission) index)
    (NativeSource.generated_time_positive admission index)
    (NativeSource.generated_step_signed admission index)).choose_spec
  have signed :
      0 < responseFlux (trajectory (NativeSource.initial admission) index).material
          (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear 0 *
        contribution (trajectory (NativeSource.initial admission) index).material
          (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
          (NativeSource.timeAt (NativeSource.initial admission) index) (stepChannel admission index) :=
    (Finset.mem_filter.mp member).2
  exact ⟨signed,fun zero => by rw [zero,mul_zero] at signed; exact lt_irrefl _ signed⟩

theorem step_channel_complete {current : Source.Occurrence frame}
    (admission : NativeSource.Admission current) (index : Nat) :
    let state := (trajectory (NativeSource.initial admission) index).material
    let nuclear := (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
    let time := NativeSource.timeAt (NativeSource.initial admission) index
    contribution state nuclear time (stepChannel admission index) +
      residual state nuclear time (stepChannel admission index) = responseFlux state nuclear time :=
  selected_and_residual _ _ _ _

def currentChannel? (current : Source.Occurrence frame) (index : Nat) :
    Option ((state : Material frame) × Channel state.reference) :=
  (CPS1AddressedBondResponse.NativeSource.autoBondResponse? current).map
    (fun admission => ⟨(trajectory (NativeSource.initial admission) index).material,stepChannel admission index⟩)

def InteractionAt (current : Source.Occurrence frame) (depth : Nat) : Prop :=
  match CPS1AddressedBondResponse.NativeSource.autoBondResponse? current with
  | none =>
      currentChannel? current depth = none ∧
      NativeSource.next current depth = Source.resume frame current [] []
  | some admission =>
      SeriesProperties admission depth ∧
      NativeSource.next current depth = NativeSource.continued admission depth ∧
      ∀ index < depth,
        let state := (trajectory (NativeSource.initial admission) index).material
        let nuclear := (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
        let time := NativeSource.timeAt (NativeSource.initial admission) index
        currentChannel? current index = some ⟨state,stepChannel admission index⟩ ∧
        addressSupport state.reference (stepChannel admission index) =
          (nuclearSupport state.reference (stepChannel admission index)).map
            (fun address => (state.reference.geometry.nuclei.get address).particle.address) ∧
        0 < responseFlux state nuclear 0 * contribution state nuclear time (stepChannel admission index) ∧
        contribution state nuclear time (stepChannel admission index) ≠ 0 ∧
        channelMatrix state.reference (state.movedPositions time) (seedOccupation state time)
          (stepChannel admission index) ≠ 0 ∧
        contribution state nuclear time (stepChannel admission index) +
          residual state nuclear time (stepChannel admission index) = responseFlux state nuclear time

/-- Admission is generated from the actual current. The same original finite
trajectory pays the prefix, all fields/number/energy, and complete pending suffix. -/
theorem source_generated_interaction (current : Source.Occurrence frame) (depth : Nat) :
    InteractionAt current depth := by
  cases generated : CPS1AddressedBondResponse.NativeSource.autoBondResponse? current with
  | none =>
    simp only [InteractionAt,generated,currentChannel?,Option.map_none,true_and]
    simpa only [CPS1AddressedBondRenewal.CurrentResult,generated] using current_result current depth
  | some admission =>
    simp only [InteractionAt,generated]
    refine ⟨series_properties admission depth,?_,?_⟩
    · have paid := current_result current depth
      simp only [CPS1AddressedBondRenewal.CurrentResult,generated] at paid
      exact paid.1
    · intro index _
      refine ⟨?_,actual_address_support _ _,(step_channel_signed admission index).1,
        (step_channel_signed admission index).2,
        contribution_source_nonzero _ _ _ _ (step_channel_signed admission index).2,
        step_channel_complete admission index⟩
      simp only [currentChannel?,generated,Option.map_some]

end
end CPS1AddressedInteraction
