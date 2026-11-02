import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Common
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}


variable {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
  (all : Candidates source catalogue) (index : Index prepared)
abbrev Scope := Whole.Scope (initial input prepared.saved[index].point) input.pricing input.future
  (reference input prepared.saved[index].point) input.actor input.position
abbrev NativeScope (owner : Ready all) := Whole.Scope
  (initial input owner.release.programme.paid.family.saved[paidIndex owner.release.programme.paid.funding index].point)
  input.pricing input.future (reference input owner.release.programme.paid.family.saved[paidIndex owner.release.programme.paid.funding index].point)
  input.actor input.position
abbrev Cell := Sigma fun owner : Ready all => NativeScope all index owner
abbrev Entry := { entry : ((quota : catalogue.Quota) × Record prepared quota.val) // entry ∈ all.entries }

def scopeAt (owner : Ready all) {units : Nat} (attempt : EscrowBudget.Attempt owner.release.programme.paid.family units) :
    Option (NativeScope all index owner) :=
  match Comparison.stageAt attempt (paidIndex owner.release.programme.paid.funding index) with
  | .ready scope => some scope
  | .stopped _ | .blocked _ => none

def forQuotas (owner : Ready all) (quotas : List owner.release.programme.actual.catalogue.Quota) : List (Cell all index) :=
  (quotas.filterMap fun quota => scopeAt all index owner (Comparison.enter owner.release.programme.actual.catalogue quota).attempt).map (Sigma.mk owner)
def forOwners (owners : List (Ready all)) : List (Cell all index) := owners.flatMap fun owner =>
  forQuotas all index owner owner.release.programme.actual.catalogue.quotas
def cells := forOwners all index (ready all)
private def transfer {first second : NativePoint input} (same : first = second)
    (scope : Whole.Scope (initial input first) input.pricing input.future (reference input first) input.actor input.position) :
    Whole.Scope (initial input second) input.pricing input.future (reference input second) input.actor input.position := by
  cases same;exact scope

def project (cell : Cell all index) : Scope index := transfer (paid_point cell.1.release.programme.paid.funding index) cell.2

def scopes : List (Scope index) := (cells all index).map (project all index)

theorem local_is_the_original_pool_scopes (owner : Ready all) :
    forQuotas all index owner owner.release.programme.actual.catalogue.quotas =
      (owner.release.programme.actual.pool.scopes (paidIndex owner.release.programme.paid.funding index)).map (Sigma.mk owner) := by
  rw [Comparison.Pool.scopes,owner.release.programme.actual.pool.generated]
  simp only [Comparison.entries,List.filterMap_map,forQuotas,scopeAt,Function.comp_def]
  apply congrArg (List.map (Sigma.mk owner))
  apply congrArg (fun f => owner.release.programme.actual.catalogue.quotas.filterMap f)
  funext quota
  split
  all_goals rename_i left_eq
  all_goals split
  all_goals rename_i right_eq
  all_goals have same := left_eq.symm.trans right_eq
  all_goals cases same <;> rfl

private theorem transport_scope {first second : NativePoint input} (same : first = second) (view : Local first) :
    (same ▸ view : Local second).scope = transfer same view.scope := by cases same;rfl

theorem every_offer_scope_is_included (offer : Offer all) : (offer.view index).scope ∈ scopes all index := by
  have native := (offer.branch index).scope_included
  have contained : (⟨offer.ready,(offer.branch index).scope⟩ : Cell all index) ∈ cells all index := by
    apply List.mem_flatMap.mpr
    refine ⟨offer.ready,every_ready_record_is_retained all offer.ready,?_⟩
    rw [local_is_the_original_pool_scopes]
    exact List.mem_map.mpr ⟨(offer.branch index).scope,native,rfl⟩
  apply List.mem_map.mpr
  refine ⟨⟨offer.ready,(offer.branch index).scope⟩,contained,?_⟩
  exact (transport_scope (paid_point offer.funding index) (offer.paidLocal (offer.actualIndex index))).symm

inductive Cursor where
  | outer (remaining : List (Entry all))
  | quotas (owner : Ready all) (remaining : List owner.release.programme.actual.catalogue.Quota) (tail : List (Entry all))
  | entered (owner : Ready all) (quota : owner.release.programme.actual.catalogue.Quota)
      (entry : Comparison.Entry owner.release.programme.actual.catalogue quota)
      (generated : entry = Comparison.enter owner.release.programme.actual.catalogue quota)
      (remaining : List owner.release.programme.actual.catalogue.Quota) (tail : List (Entry all))
def start : Cursor all := .outer all.entries.attach

def outerCells (remaining : List (Entry all)) := forOwners all index (remaining.filterMap (readyOf all))
def Cursor.denote : Cursor all → List (Cell all index)
  | .outer remaining => outerCells all index remaining
  | .quotas owner remaining tail => forQuotas all index owner remaining++outerCells all index tail
  | .entered owner _ entry _ remaining tail =>
      (scopeAt all index owner entry.attempt).toList.map (Sigma.mk owner)++forQuotas all index owner remaining++outerCells all index tail

inductive Event where
  | outer (entry : Entry all)
  | enter (owner : Ready all) (quota : owner.release.programme.actual.catalogue.Quota)
  | stage (owner : Ready all) (quota : owner.release.programme.actual.catalogue.Quota) (scope : Option (NativeScope all index owner))
  | close

def step : Cursor all → Option (Cursor all × Option (Cell all index) × Event all index)
  | .outer [] => none
  | .outer (entry::tail) => match readyOf all entry with
    | none => some (.outer tail,none,.outer entry)
    | some owner => some (.quotas owner owner.release.programme.actual.catalogue.quotas tail,none,.outer entry)
  | .quotas _ [] tail => some (.outer tail,none,.close)
  | .quotas owner (quota::remaining) tail => some
      (.entered owner quota (Comparison.enter owner.release.programme.actual.catalogue quota) rfl remaining tail,none,.enter owner quota)
  | .entered owner quota entry _ remaining tail =>
      let actual := scopeAt all index owner entry.attempt
      some (.quotas owner remaining tail,actual.map (Sigma.mk owner),.stage owner quota actual)

theorem initial_denote : (start all).denote all index = cells all index := rfl

theorem one_step_conserves {before after : Cursor all} {yielded : Option (Cell all index)} {event : Event all index}
    (observed : step all index before = some (after,yielded,event)) :
    before.denote all index = yielded.toList++after.denote all index := by
  cases before with
  | outer remaining =>
    cases remaining with
    | nil => cases observed
    | cons entry tail =>
      dsimp only [step] at observed
      split at observed
      all_goals cases Option.some.inj observed
      all_goals simp only [Cursor.denote,outerCells,List.filterMap_cons, *,forOwners,List.flatMap_cons,Option.toList_none,List.nil_append]
  | quotas owner remaining tail =>
    cases remaining with
    | nil => cases Option.some.inj observed;rfl
    | cons quota remaining =>
      cases Option.some.inj observed
      simp only [Cursor.denote,forQuotas,List.filterMap_cons,Option.toList_none,List.nil_append,List.append_assoc]
      cases scopeAt all index owner (Comparison.enter owner.release.programme.actual.catalogue quota).attempt <;> rfl
  | entered owner quota entry generated remaining tail =>
    cases Option.some.inj observed
    simp only [Cursor.denote,List.append_assoc]
    cases scopeAt all index owner entry.attempt <;> rfl

def outerRank (remaining : List (Entry all)) : Nat := (remaining.map fun entry => match readyOf all entry with
  | none => 1
  | some owner => 2+2*owner.release.programme.actual.catalogue.quotas.length).sum
def Cursor.rank : Cursor all → Nat
  | .outer remaining => outerRank all remaining
  | .quotas _ remaining tail => 1+2*remaining.length+outerRank all tail
  | .entered _ _ _ _ remaining tail => 2+2*remaining.length+outerRank all tail

theorem step_decreases_rank {before after : Cursor all} {yielded : Option (Cell all index)} {event : Event all index}
    (observed : step all index before = some (after,yielded,event)) : after.rank all+1 = before.rank all := by
  cases before with
  | outer remaining =>
    cases remaining with
    | nil => cases observed
    | cons entry tail =>
      dsimp only [step] at observed;split at observed
      all_goals cases Option.some.inj observed
      all_goals simp_all [Cursor.rank,outerRank]
      all_goals first | omega | ring
  | quotas owner remaining tail =>
    cases remaining <;> cases Option.some.inj observed
    all_goals simp only [Cursor.rank,List.length_nil,List.length_cons];omega
  | entered owner quota entry generated remaining tail =>
    cases Option.some.inj observed
    simp only [Cursor.rank];omega

theorem stopped_has_no_residual (before : Cursor all) (stopped : step all index before = none) : before.denote all index = [] := by
  cases before with
  | outer remaining =>
    cases remaining with
    | nil => rfl
    | cons entry tail => dsimp only [step] at stopped;split at stopped <;> cases stopped
  | quotas owner remaining tail => cases remaining <;> cases stopped
  | entered => cases stopped

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Common
