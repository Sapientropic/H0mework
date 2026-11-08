import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Recursive

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private abbrev operationDecidableEq : DecidableEq (Operation Actor Good Technology Instrument) := by
  intro left right
  cases left <;> cases right <;> (try simp only [Operation.produce.injEq,Operation.transfer.injEq,Operation.use.injEq,
    Operation.issue.injEq,Operation.assign.injEq,Operation.settle.injEq,Operation.revise.injEq,reduceCtorEq]) <;> infer_instance
private abbrev actionDecidableEq : DecidableEq JointAction := by
  letI := operationDecidableEq
  intro left right
  cases left;cases right
  simp only [Institutions.Capitalism.Universal.Source.Program.Request.mk.injEq]
  infer_instance
attribute [local instance] actionDecidableEq

def publicEvidence (query : Query) : List (Slot×Evidence) :=
  (selected query).map fun slot => (slot,restrict (fields query) (originalEvidence slot))

def publicPackets (items : List PublicItem) (actor : Party) (query : Query) : List (List (Slot×Evidence)) :=
  items.flatMap fun access => items.filterMap fun fee =>
    if access.request=liftAudit access.before (accessRequest actor query) ∧ access.accepted=true ∧
      fee.request=liftAudit fee.before deliveryFee ∧ fee.accepted=true ∧ fee.index=access.index+1
    then some (publicEvidence query) else none

@[simp] private theorem attached_filterMap {α β : Type} (items : List α) (f : α → Option β) :
    items.attach.filterMap (fun item => f item.val)=items.filterMap f := by
  change items.attach.filterMap (f ∘ Subtype.val)=items.filterMap f
  rw [←List.filterMap_map,List.attach_map_subtype_val]

@[simp] private theorem attached_flatMap {α β : Type} (items : List α) (f : α → List β) :
    items.attach.flatMap (fun item => f item.val)=items.flatMap f := by
  rw [←List.flatMap_map,List.attach_map_subtype_val]

theorem actual_packets_are_read_from_the_complete_public_trace (scope : Scope) (before : Current)
    (actions : List JointAction) (actor : Party) (query : Query) :
    (packets scope before actions actor query).map Packet.evidence=
      publicPackets (publicItems scope before actions 0) actor query := by
  simp [packets,Packet.evidence,publicPackets,publicEvidence,publicItems,List.map_flatMap,
    List.flatMap_map,List.map_filterMap,List.filterMap_map,cachedItems_exact,RawLaw.rawItems,
    publicize,rebuild,liftAudit,liftAuditOperation,apply_dite,accessRequest,deliveryFee,attached_filterMap,attached_flatMap]
  rw [cachedItems_exact]
  let items := ((law scope).execute before 0 actions).items
  let f := fun (access fee : ExecutionItem Actor Good Port Technology Instrument) =>
    if access.request=liftAudit access.before (accessRequest actor query) ∧ (law scope).Valid access.before access.request ∧
      fee.request=liftAudit fee.before deliveryFee ∧ (law scope).Valid fee.before fee.request ∧ fee.index=access.index+1
    then some (publicEvidence query) else none
  change items.attach.flatMap (fun access => items.attach.filterMap (fun fee => f access.val fee.val))=
    items.flatMap (fun access => items.filterMap (f access))
  calc
    _ = items.attach.flatMap (fun access => items.filterMap (f access.val)) := by
      apply congrArg (List.flatMap · items.attach)
      funext access
      exact attached_filterMap items (f access.val)
    _ = _ := attached_flatMap items (fun access => items.filterMap (f access))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy
