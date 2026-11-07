import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Observation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root Lean

private abbrev operationDecidableEq : DecidableEq (Operation Party Good (Mandate.State Party Technology) Unit) := by
  intro left right
  cases left <;> cases right <;> (try simp only [Operation.produce.injEq,Operation.transfer.injEq,Operation.use.injEq,
    Operation.issue.injEq,Operation.assign.injEq,Operation.settle.injEq,Operation.revise.injEq,reduceCtorEq]) <;> infer_instance
private abbrev actionDecidableEq : DecidableEq Action := by
  letI := operationDecidableEq
  intro left right
  cases left
  cases right
  simp only [Institutions.Capitalism.Universal.Source.Program.Request.mk.injEq]
  infer_instance
attribute [local instance] actionDecidableEq

def queryJson (query : Query) : Json := Json.mkObj [("slots",toJson query.slots.val),("fields",toJson query.fields.val)]
def evidenceJson (slot : Slot) (evidence : Evidence) : Json :=
  Json.mkObj [("slot",toJson slot.val),
    ("admission",match evidence.admission with
      | none => .null
      | some event => Json.mkObj [("slot",toJson event.slot),("ordinal",toJson event.ordinal)]),
    ("payment",match evidence.payment with
      | none => .null
      | some event => Json.mkObj [("slot",toJson event.slot),("visit",toJson event.visit),("row",toJson event.row),
        ("available",toJson (toString event.available)),("start",toJson (toString event.start)),("finish",toJson (toString event.finish))])]

def packetJson (actor : Party) (query : Query) (access : Item) : Json := Json.mkObj
  [("index",toJson access.index),("actor",toJson actor),
   ("query",queryJson query),("unit",toJson ("energy" : String)),
   ("accessEnergy",toJson ("1" : String)),("deliveryEnergy",toJson ("1" : String)),
   ("clock",toJson (toString access.before.clock)),("version",toJson access.before.technology.version),
   ("evidence",toJson ((selected query).map fun slot => evidenceJson slot (restrict (fields query) (originalEvidence slot))))]

def rawLink (sourceLaw : RawLaw Party Good AuditPort (Mandate.State Party Technology) Unit)
    (actor : Party) (query : Query) (access fee : Item) : Option Json :=
  if access.request = accessRequest actor query ∧ sourceLaw.Valid access.before access.request ∧
    fee.request = deliveryFee ∧ sourceLaw.Valid fee.before fee.request ∧ fee.index = access.index+1
  then some (packetJson actor query access) else none

def link (scope : Scope) := rawLink (law scope)

def packets (scope : Scope) (actor : Party) (query : Query) (items : List Item) : List Json :=
  items.flatMap fun access => items.filterMap (link scope actor query access)

theorem ItemTwin.packet {left right : Item} (same : ItemTwin left right) (actor : Party) (query : Query) :
    packetJson actor query left = packetJson actor query right := by
  simp only [packetJson,same.index,same.before.clock,same.before.technology]

theorem ItemTwin.link {la ra lf rf : Item} (access : ItemTwin la ra) (fee : ItemTwin lf rf)
    (scope : Scope) (cost : scope.revisionCost = [(.energy,1)]) (actor : Party) (query : Query) :
    link scope actor query la lf = link scope actor query ra rf := by
  have accessPaid := access.before.valid scope la.request (energy_public _ cost _ _ access.energy)
  have feePaid := fee.before.valid scope lf.request (energy_public _ cost _ _ fee.energy)
  simp only [Privacy.link,rawLink,← access.request,← fee.request,accessPaid,feePaid,
    access.index,fee.index,access.packet actor query]

theorem packets_eq {xs ys : List Item} (items : List.Forall₂ ItemTwin xs ys)
    (scope : Scope) (cost : scope.revisionCost = [(.energy,1)]) (actor : Party) (query : Query) :
    packets scope actor query xs = packets scope actor query ys := by
  have inner : ∀ {access fee : Item},ItemTwin access fee →
      xs.filterMap (link scope actor query access) = ys.filterMap (link scope actor query fee) := by
    intro access fee same
    induction items with
    | nil => rfl
    | cons head _ ih => simp only [List.filterMap_cons,same.link head scope cost actor query,ih]
  unfold packets
  have outer : ∀ {as bs : List Item},List.Forall₂ ItemTwin as bs →
      (as.flatMap fun access => xs.filterMap (link scope actor query access)) =
      (bs.flatMap fun access => ys.filterMap (link scope actor query access)) := by
    intro as bs related
    induction related with
    | nil => rfl
    | cons head _ ih => simp only [List.flatMap_cons,inner head,ih]
  exact outer items

theorem Twin.packets {left right : AuditCurrent} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost = [(.energy,1)]) (word : List Action)
    (energy : ∀ action ∈ word,EnergyAction action) (actor : Party) (query : Query) :
    packets scope actor query ((law scope).rawItems left word) =
      packets scope actor query ((law scope).rawItems right word) :=
  packets_eq (same.items scope cost word energy 0) scope cost actor query

/-- This equality consumes the original dependent Delivery constructor, including both real fees. -/
theorem handoff_packets_are_original {plan : Plan} (seed : Handoff.Seed plan)
    (actor : Party) (query : Query) (before : AuditCurrent) (word : List Action) :
    (Handoff.deliveries seed actor before word query).map (fun delivery => packetJson actor query delivery.access.val) =
      packets seed.scope actor query (seed.law.rawItems before word) := by
  unfold Handoff.deliveries packets link
  simp only [List.map_flatMap,List.map_filterMap]
  let items := seed.law.rawItems before word
  trans items.attach.flatMap (fun access => items.attach.filterMap (fun fee => rawLink seed.law actor query access.val fee.val))
  · apply List.flatMap_congr
    intro access _
    apply List.filterMap_congr
    intro fee _
    unfold rawLink
    simp only [apply_dite,Option.map_some,Option.map_none,dite_eq_ite]
  · have inner : ∀ access : {item // item ∈ items},
        items.attach.filterMap (fun fee => rawLink seed.law actor query access.val fee.val) =
          items.filterMap (rawLink seed.law actor query access.val) := by
      intro access
      change items.attach.filterMap (rawLink seed.law actor query access.val ∘ Subtype.val) = _
      rw [← List.filterMap_map]
      simp
    simp only [inner]
    change items.attach.flatMap (fun access => items.filterMap (rawLink seed.law actor query access.val)) = _
    rw [← List.flatMap_map Subtype.val (fun access => items.filterMap (rawLink seed.law actor query access)) items.attach]
    rw [List.attach_map_subtype_val]
    rfl

theorem continuation_packets_are_original {plan : Plan} (seed : Continuation.Window plan)
    (query : Query) (before : AuditCurrent) (word : List Action) :
    (Continuation.deliveries seed before word query).map (fun delivery => packetJson plan.candidate query delivery.access.val) =
      packets seed.scope plan.candidate query (seed.law.rawItems before word) := by
  unfold Continuation.deliveries packets link
  simp only [List.map_flatMap,List.map_filterMap]
  let items := seed.law.rawItems before word
  trans items.attach.flatMap (fun access => items.attach.filterMap (fun fee => rawLink seed.law plan.candidate query access.val fee.val))
  · apply List.flatMap_congr
    intro access _
    apply List.filterMap_congr
    intro fee _
    unfold rawLink
    simp only [apply_dite,Option.map_some,Option.map_none,dite_eq_ite]
  · have inner : ∀ access : {item // item ∈ items},
        items.attach.filterMap (fun fee => rawLink seed.law plan.candidate query access.val fee.val) =
          items.filterMap (rawLink seed.law plan.candidate query access.val) := by
      intro access
      change items.attach.filterMap (rawLink seed.law plan.candidate query access.val ∘ Subtype.val) = _
      rw [← List.filterMap_map]
      simp
    simp only [inner]
    change items.attach.flatMap (fun access => items.filterMap (rawLink seed.law plan.candidate query access.val)) = _
    rw [← List.flatMap_map Subtype.val (fun access => items.filterMap (rawLink seed.law plan.candidate query access)) items.attach]
    rw [List.attach_map_subtype_val]
    rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
