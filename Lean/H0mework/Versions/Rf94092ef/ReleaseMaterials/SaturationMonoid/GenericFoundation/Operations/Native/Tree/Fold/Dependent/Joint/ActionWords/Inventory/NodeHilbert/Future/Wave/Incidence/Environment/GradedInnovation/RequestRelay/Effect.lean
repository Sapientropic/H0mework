import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.RequestRelay

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated

open SourceOperationEffects
open SourceOperationInquiry.Context.Installation (executedEnvironmentIncrement)

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (packet next : RelayPacket (K := K) X)
variable (literal : next = Action.packetTransport packet.2.2.2.down (Action.sourceBorn (factory read) packet))
variable (prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint))
variable (present : packet.2.1.1.inventory = some prior)
variable (event : Fin prior.trace.length)
variable (item : Fin (Feed.eventItems (relayedEvent read packet next literal prior present event)).length)

/-- The carried request is executed by the literal next material, with its actual signed item. -/
theorem relayed_column_action :
    let occurrence := S.actualOccurrence next.2.1.1
    let material := I.materialAt (A.epoch next.2.1.1) occurrence
    let entry := (Feed.eventItems (relayedEvent read packet next literal prior present event)).get item
    let index := relayedRequest read packet next literal prior present event item
    let increment := executedEnvironmentIncrement (A.epoch next.2.1.1) occurrence
    columnAction read next.1 (A.epoch next.2.1.1) occurrence index =
      (entry.2 • columnRead read next.1 (entry.1.eval material.raw.environment,0),
       entry.2 • columnRead read next.1 (0,entry.1.effect material.raw.environment increment)) := by
  have actual := actual_column_action_components read next.1 (A.epoch next.2.1.1) (S.actualOccurrence next.2.1.1)
    (relayedRequest read packet next literal prior present event item)
  have address := relayed_request_read read packet next literal prior present event item
  simpa only [address] using actual

end PaidSourceContentEnvironment.GradedInnovation.Integrated
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
