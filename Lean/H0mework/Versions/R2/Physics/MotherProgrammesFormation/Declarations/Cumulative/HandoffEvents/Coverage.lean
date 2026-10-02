import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffEvents.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffEvents
open MotherArenaNetwork
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}

private theorem zero_test (p : Prop) : (if p then (0 : ℝ) else 1) = 0 ↔ p := by
  by_cases present : p <;> simp only [present, if_true, if_false, one_ne_zero, iff_self]

structure Presentation (I : Type) (events : I → Type) (emit : (index : I) → events index) (value : Value rank) where
  context : I ≃ Context value.1
  event : ∀ index, events index ≃ Event value.1 (context index)
  emit_eq : ∀ index, value.2 (context index) = event index (emit index)

theorem every_carrier (I : Type) (events : I → Type)
    (indexCode : I ↪ MotherArenaHigher.Base rank)
    (eventCode : (Sigma events) ↪ MotherArenaHigher.Base rank) :
    ∃ base : MotherArenaHigher.Material rank,
      ∃ context : I ≃ Context base,
      Nonempty ((index : I) → events index ≃ Event base (context index)) := by
  let domain (address : MotherArenaHigher.Base rank) := ∃ index, indexCode index = address
  let fibers (address : MotherArenaHigher.Base rank) := ∃ point : Sigma events,
    indexCode point.1 = (MotherArenaHigher.unpair rank address).1 ∧
      eventCode point = (MotherArenaHigher.unpair rank address).2
  obtain ⟨base, readback⟩ := MotherArenaHigher.read_surjective rank (fun address tag =>
    if tag = 0 then (if domain address then 0 else 1) else (if fibers address then 0 else 1))
  have at_domain (address : MotherArenaHigher.Base rank) : bit base 0 address ↔ domain address := by
    simp only [bit, readback, ite_true]
    by_cases present : domain address <;> simp only [present, if_true, if_false, one_ne_zero, iff_self]
  let context := MotherArenaNetworkOrigin.imageEquiv indexCode (bit base 0) at_domain
  have at_event (index : I) (address : MotherArenaHigher.Base rank) :
      r2 base 1 (context index).val address ↔ ∃ event : events index, eventCode ⟨index, event⟩ = address := by
    simp only [r2, bit, readback, show ¬ (1 : Nat) = 0 from by decide, if_false]
    have represented : fibers (MotherArenaHigher.pair rank ((context index).val, address)) ↔
        ∃ event : events index, eventCode ⟨index, event⟩ = address := by
      simp only [fibers, MotherArenaHigher.unpair_pair]
      change (∃ point : Sigma events, indexCode point.1 = indexCode index ∧ eventCode point = address) ↔ _
      constructor
      · rintro ⟨⟨other, event⟩, same, encoded⟩
        have same := indexCode.injective same
        cases same
        exact ⟨event, encoded⟩
      · rintro ⟨event, encoded⟩
        exact ⟨⟨index, event⟩, rfl, encoded⟩
    exact (zero_test _).trans represented
  exact ⟨base, context, ⟨fun index => MotherArenaNetworkOrigin.imageEquiv
    ((Function.Embedding.sigmaMk index).trans eventCode)
    (r2 base 1 (context index).val) (at_event index)⟩⟩

theorem every_events_at (I : Type) (events : I → Type) (emit : (index : I) → events index)
    (indexCode : I ↪ MotherArenaHigher.Base rank)
    (eventCode : (Sigma events) ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank, ∃ value : Value rank,
      formEvents material = some value ∧ Nonempty (Presentation I events emit value) := by
  obtain ⟨base, context, ⟨eventsAcross⟩⟩ := every_carrier I events indexCode eventCode
  let eventMap : ((index : I) → events index) ≃ ((index : Context base) → Event base index) :=
    (Equiv.piCongrRight eventsAcross).trans (Equiv.piCongrLeft (Event base) context)
  let generated := eventMap emit
  obtain ⟨material, formed⟩ := every_emit base generated
  refine ⟨material, ⟨base, generated⟩, formed, ⟨{
    context := context
    event := eventsAcross
    emit_eq := fun index => ?_ }⟩⟩
  exact Equiv.piCongrLeft_apply_apply (Event base) context (fun index => eventsAcross index (emit index)) index

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffEvents
