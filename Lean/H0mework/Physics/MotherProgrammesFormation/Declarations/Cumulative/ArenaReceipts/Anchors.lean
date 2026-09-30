import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaObligation.FullConsumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Anchors

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
open MotherArenaNetwork MotherObligationOrigin ResponsibilityLifecycle ComplementObservation
open scoped Classical
open MotherObligationOrigin
open MotherRestructuringReceipts
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {Observation : ComplementObservationCarrier.{0}} {Scope Lineage I : Type}
    (index : I ↪ MotherArenaHigher.Base rank) (observation : Observation.Carrier ↪ MotherArenaHigher.Base rank)
    (left right : I → MinimalRegistrableSourceAnchor Observation Scope Lineage)

def AnchorMapCheck (material : M) : Prop :=
  ∀ i point, ∃! result, r2 material 0 ((MotherArenaHigher.pair rank) (index i, observation point)) (observation result)

def anchorMaps (material : M) (checked : AnchorMapCheck index observation material) :
    I → Observation.Carrier → Observation.Carrier := fun i point => Classical.choose (checked i point)

def formAnchorSection (material : M) : Option ((i : I) → SourceAnchorTransport (left i) (right i)) :=
  if checked : AnchorMapCheck index observation material then
    let maps := anchorMaps index observation material checked
    if laws : AnchorLaws left right maps then some (anchorSection left right maps laws) else none
  else none

private theorem anchor_ext {a b : MinimalRegistrableSourceAnchor Observation Scope Lineage}
    (first second : SourceAnchorTransport a b) (same : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- The entire function section is formed by its graph on context × whole
observation carrier. No address of a function space or receipt is assumed. -/
theorem every_anchor_section (original : (i : I) → SourceAnchorTransport (left i) (right i)) :
    ∃ material : M, formAnchorSection index observation left right material = some original := by
  let graph : B → B → Prop := fun input output => ∃ (i : I) (point : Observation.Carrier),
    (MotherArenaHigher.pair rank) (index i, observation point) = input ∧ observation ((original i).toFun point) = output
  obtain ⟨material, hm⟩ := every_binary_graph 0 graph
  have at_graph (i : I) (point result : Observation.Carrier) :
      r2 material 0 ((MotherArenaHigher.pair rank) (index i, observation point)) (observation result) ↔
        result = (original i).toFun point := by
    rw [hm]
    constructor
    · rintro ⟨j, other, inputEq, outputEq⟩
      have pairEq := (MotherArenaHigher.pairEquiv rank).injective inputEq
      have same := index.injective (congrArg Prod.fst pairEq)
      cases same
      have same := observation.injective (congrArg Prod.snd pairEq)
      cases same
      exact observation.injective outputEq.symm
    · intro same
      cases same
      exact ⟨i, point, rfl, rfl⟩
  have checked : AnchorMapCheck index observation material := fun i point =>
    ⟨(original i).toFun point, (at_graph i point _).mpr rfl, fun result selected => (at_graph i point result).mp selected⟩
  have recovered : anchorMaps index observation material checked = fun i => (original i).toFun := by
    funext i point
    exact (at_graph i point _).mp (Classical.choose_spec (checked i point)).1
  have laws : AnchorLaws left right (anchorMaps index observation material checked) := by
    rw [recovered]
    exact {
      injective := fun i => (original i).injective
      identity := fun i => (original i).map_identity
      complement := fun i => (original i).map_complement
      scope := fun i => (original i).scope_eq
      lineage := fun i => (original i).lineage_eq }
  refine ⟨material, ?_⟩
  simp only [formAnchorSection, dif_pos checked, dif_pos laws]
  congr 1
  funext i
  exact anchor_ext _ _ (congrFun recovered i)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
