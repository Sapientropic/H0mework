import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Comparison.Joint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
namespace Comparison

variable {units : Nat}
def Continued : EscrowBudget.Attempt prepared units → Type
  | .empty .. | .unpaid .. => Unit
  | .running made => EscrowBudget.Programme.Outcome made

def continueAttempt : (attempt : EscrowBudget.Attempt prepared units) → Continued attempt
  | .empty .. | .unpaid .. => ()
  | .running made => made.release

def chargeAt (attempt : EscrowBudget.Attempt prepared units) (index : Index prepared) :
    EscrowBudget.Charge units prepared.saved[index].stage :=
  match attempt with
  | .empty absent => False.elim (by have bounded := index.isLt; change index.val < prepared.saved.length at bounded; have zero := congrArg List.length absent; simp only [List.length_nil] at zero; omega)
  | .unpaid funding .. => funding.resultAt index
  | .running made => made.funding.resultAt index

def stageAt (attempt : EscrowBudget.Attempt prepared units) (index : Index prepared) : Stage input prepared.saved[index].point :=
  (chargeAt attempt index).endpoint

theorem stageAt_is_the_original_installed_stage (attempt : EscrowBudget.Attempt prepared units) (index : Index prepared) :
    stageAt attempt index = stageFor input (.reserved prepared.recipe units) prepared.saved[index].point := by
  cases attempt with
  | empty absent => have bounded := index.isLt;change index.val < prepared.saved.length at bounded;have zero := congrArg List.length absent; simp only [List.length_nil] at zero; omega
  | unpaid funding _ _ _ => exact funding.alignment index
  | running made => exact made.funding.alignment index

variable (catalogue : Catalogue snapshot)
structure Entry (quota : catalogue.Quota) where
  private mk ::
  attempt : EscrowBudget.Attempt prepared quota.val
  generated : attempt = catalogue.offer quota
  continuation : Continued attempt
  continuation_exact : continuation = continueAttempt attempt

def enter (quota : catalogue.Quota) : Entry catalogue quota :=
  let attempt := catalogue.offer quota
  ⟨attempt,rfl,continueAttempt attempt,rfl⟩
abbrev Cached := Sigma (Entry catalogue)
def entries : List (Cached catalogue) := catalogue.quotas.map fun quota => ⟨quota,enter catalogue quota⟩
structure Pool where
  private mk ::
  cached : List (Cached catalogue)
  generated : cached = entries catalogue
  keys_exact : cached.map Sigma.fst = catalogue.quotas

def generate : Pool catalogue := ⟨entries catalogue,rfl,by
  simp only [entries,List.map_map,Function.comp_def]
  exact List.map_id catalogue.quotas⟩

namespace Pool
variable {catalogue} (pool : Pool catalogue)
theorem length : pool.cached.length = catalogue.bound+1 := by
  have sizes := congrArg List.length pool.keys_exact
  simpa only [List.length_map,Catalogue.quotas,List.length_finRange] using sizes

def cachedIndex (quota : catalogue.Quota) : Fin pool.cached.length := ⟨quota.val,by rw [pool.length];exact quota.isLt⟩
theorem cached_key (quota : catalogue.Quota) : pool.cached[pool.cachedIndex quota].1 = quota := by
  have selected : (pool.cached.map Sigma.fst)[quota.val]? = some quota := by
    rw [pool.keys_exact]
    change (List.finRange (catalogue.bound+1))[quota.val]? = some quota
    rw [List.getElem?_eq_getElem (by simpa only [List.length_finRange] using quota.isLt)]
    congr 1
    apply Fin.ext
    simp only [List.getElem_finRange,Fin.val_cast]
  obtain ⟨bounded,same⟩ := List.getElem?_eq_some_iff.mp selected
  simpa only [List.getElem_map,Fin.getElem_fin,cachedIndex] using same

def resultAt (quota : catalogue.Quota) : Entry catalogue quota :=
  pool.cached_key quota ▸ pool.cached[pool.cachedIndex quota].2

theorem every_quota_keeps_its_own_original_paid_attempt (quota : catalogue.Quota) :
    (pool.resultAt quota).attempt = EscrowBudget.generate prepared quota.val := (pool.resultAt quota).generated

def scopes (index : Index prepared) : List (Whole.Scope (initial input prepared.saved[index].point) input.pricing input.future
    (reference input prepared.saved[index].point) input.actor input.position) :=
  pool.cached.filterMap fun cached => match stageAt cached.2.attempt index with
    | .ready scope => some scope
    | .stopped _ | .blocked _ => none

theorem each_cached_ready_scope_is_included (entry : Cached catalogue) (listed : entry ∈ pool.cached)
    (index : Index prepared) (scope : Whole.Scope (initial input prepared.saved[index].point) input.pricing input.future
      (reference input prepared.saved[index].point) input.actor input.position)
    (ready : stageAt entry.2.attempt index = .ready scope) : scope ∈ pool.scopes index :=
  List.mem_filterMap.mpr ⟨entry,listed,by rw [ready]⟩

inductive Debt (pool : Pool catalogue) where
  | prior (debt : SourceQuota.Debt prepared)
  | old (obligation : Policy.Obligation prepared)
  | candidate (entry : Cached catalogue)
  | source (index : Index prepared)
  | frameConstruction
  | comparison
  | verification
  | storage

def pending : List (Debt pool) :=
  ((Policy.obligations prepared).map SourceQuota.Debt.original ++ snapshot.cached.map SourceQuota.Debt.source ++
    (keys prepared).map SourceQuota.Debt.lookup ++ ([.quotaEnumeration,.comparison,.storage] : List (SourceQuota.Debt prepared))).map Debt.prior ++
  (Policy.obligations prepared).map Debt.old ++ pool.cached.map Debt.candidate ++
    (keys prepared).map Debt.source ++ [.frameConstruction,.comparison,.verification,.storage]
end Pool
end Comparison
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.Comparison
namespace Acquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

variable {snapshot : Snapshot prepared} {catalogue : Catalogue snapshot}
private def quotaList (catalogue : Catalogue snapshot) (limit : Nat) (bound : limit = catalogue.bound) : List catalogue.Quota :=
  (List.finRange (limit+1)).map fun quota => ⟨quota.val,by rw [←bound];exact quota.isLt⟩
private theorem quotaList_exact (catalogue : Catalogue snapshot) (limit : Nat) (bound : limit = catalogue.bound) :
    quotaList catalogue limit bound = catalogue.quotas := by
  subst limit;simp only [quotaList,Catalogue.quotas];exact List.map_id _
private theorem canonical (pool : Pool catalogue) : pool = generate catalogue := by
  rcases pool with ⟨cached,generated,keys⟩;cases generated;rfl
inductive State (catalogue : Catalogue snapshot) where
  | reading (cached : List (Cached catalogue)) (remaining : List catalogue.Quota)
      (conserved : cached++remaining.map (fun quota => ⟨quota,enter catalogue quota⟩) = entries catalogue)
  | finished (pool : Pool catalogue) (generated : pool = generate catalogue)
def initial (catalogue : Catalogue snapshot) (limit : Nat) (bound : limit = catalogue.bound) : State catalogue :=
  .reading [] (quotaList catalogue limit bound) (by rw [quotaList_exact];rfl)
inductive Event (catalogue : Catalogue snapshot) where
  | entered (quota : catalogue.Quota) (entry : Entry catalogue quota) (actual : entry = enter catalogue quota)
  | installed (pool : Pool catalogue) (generated : pool = generate catalogue)
def move : State catalogue → Option (State catalogue × Event catalogue)
  | .reading cached (quota::rest) conserved =>
      let entry := enter catalogue quota
      some (.reading (cached++[⟨quota,entry⟩]) rest (by
        simpa only [List.map_cons,List.append_assoc,List.singleton_append] using conserved),.entered quota entry rfl)
  | .reading cached [] conserved =>
      let generated : cached = entries catalogue := by simpa only [List.map_nil,List.append_nil] using conserved
      let pool : Pool catalogue := ⟨cached,generated,by rw [generated];exact (generate catalogue).keys_exact⟩
      some (.finished pool (canonical pool),.installed pool (canonical pool))
  | .finished .. => none
def State.rank : State catalogue → Nat | .reading _ remaining _ => remaining.length+1 | .finished .. => 0
def State.done : State catalogue → Bool | .finished .. => true | _ => false
theorem initial_rank (catalogue : Catalogue snapshot) (limit : Nat) (bound : limit = catalogue.bound) :
    (initial catalogue limit bound).rank = catalogue.quotas.length+1 := by
  simp only [initial,State.rank,quotaList_exact]
theorem progress {before after : State catalogue} {event : Event catalogue}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | reading cached remaining conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,List.length_cons];omega
  | finished => cases actual
theorem no_move_iff_done (before : State catalogue) : move before = none ↔ before.done = true := by
  cases before with
  | reading cached remaining conserved => cases remaining <;> simp [move,State.done]
  | finished => simp [move,State.done]
end Acquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.Comparison

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.Comparison
namespace EntryAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared} {catalogue : Catalogue snapshot}

private theorem canonical {quota : catalogue.Quota} (entry : Entry catalogue quota) : entry = enter catalogue quota := by
  rcases entry with ⟨attempt,generated,continuation,exact⟩;cases generated;cases exact;rfl
inductive State (catalogue : Catalogue snapshot) (quota : catalogue.Quota) where
  | offering (cursor : EscrowBudget.OfferAcquisition.State prepared quota.val)
  | continuing (made : EscrowBudget.Programme prepared quota.val) (generated : EscrowBudget.Attempt.running made = catalogue.offer quota)
      (cursor : EscrowBudget.Programme.ContinuationAcquisition.State made)
  | sealing (attempt : EscrowBudget.Attempt prepared quota.val) (generated : attempt = catalogue.offer quota)
      (continuation : Continued attempt) (exact : continuation = continueAttempt attempt)
  | finished (entry : Entry catalogue quota) (generated : entry = enter catalogue quota)
def initial (catalogue : Catalogue snapshot) (quota : catalogue.Quota) : State catalogue quota :=
  .offering (EscrowBudget.OfferAcquisition.initial prepared quota.val)
inductive Event (catalogue : Catalogue snapshot) (quota : catalogue.Quota) where
  | offer (event : EscrowBudget.OfferAcquisition.Event prepared quota.val)
  | offered (attempt : EscrowBudget.Attempt prepared quota.val) (generated : attempt = catalogue.offer quota)
  | continuation (made : EscrowBudget.Programme prepared quota.val) (event : EscrowBudget.Programme.ContinuationAcquisition.Event made)
  | continued (attempt : EscrowBudget.Attempt prepared quota.val) (continuation : Continued attempt)
  | cached (entry : Entry catalogue quota) (generated : entry = enter catalogue quota)
def move {quota : catalogue.Quota} : State catalogue quota → Option (State catalogue quota × Event catalogue quota)
  | .offering (.finished (.empty absent) generated) =>
      some (.sealing (.empty absent) generated () rfl,.offered (.empty absent) generated)
  | .offering (.finished (.unpaid funding same index broken) generated) =>
      some (.sealing (.unpaid funding same index broken) generated () rfl,.offered (.unpaid funding same index broken) generated)
  | .offering (.finished (.running made) generated) =>
      some (.continuing made generated (EscrowBudget.Programme.ContinuationAcquisition.initial made),.offered (.running made) generated)
  | .offering cursor@(.opening) | .offering cursor@(.funding ..) | .offering cursor@(.checking ..) | .offering cursor@(.calculating ..) =>
      match _step : EscrowBudget.OfferAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.offering after,.offer event)
  | .continuing made generated (.finished outcome exact) =>
      some (.sealing (.running made) generated outcome exact,.continued (.running made) outcome)
  | .continuing made generated cursor@(.opening) | .continuing made generated cursor@(.execution ..) =>
      match _step : EscrowBudget.Programme.ContinuationAcquisition.move made cursor with
      | none => none
      | some (after,event) => some (.continuing made generated after,.continuation made event)
  | .sealing attempt generated continuation exact =>
      let entry : Entry catalogue _ := ⟨attempt,generated,continuation,exact⟩
      some (.finished entry (canonical entry),.cached entry (canonical entry))
  | .finished .. => none
def afterOffer (catalogue : Catalogue snapshot) (quota : catalogue.Quota) :=
  match catalogue.offer quota with
  | .running made => (EscrowBudget.Programme.ContinuationAcquisition.initial made).rank made
  | _ => 0
private theorem afterOffer_exact (quota : catalogue.Quota) (made : EscrowBudget.Programme prepared quota.val)
    (generated : EscrowBudget.Attempt.running made = catalogue.offer quota) :
    afterOffer catalogue quota = (EscrowBudget.Programme.ContinuationAcquisition.initial made).rank made := by simp only [afterOffer,←generated]
def State.rank {quota : catalogue.Quota} : State catalogue quota → Nat
  | .offering cursor => cursor.rank+afterOffer catalogue quota+3
  | .continuing made _ cursor => cursor.rank made+2
  | .sealing .. => 1
  | .finished .. => 0
def State.done {quota : catalogue.Quota} : State catalogue quota → Bool | .finished .. => true | _ => false
theorem progress {quota : catalogue.Quota} {before after : State catalogue quota} {event : Event catalogue quota}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | offering cursor =>
      cases cursor with
      | finished attempt generated =>
          cases attempt with
          | empty | unpaid =>
              all_goals dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,EscrowBudget.OfferAcquisition.State.rank];omega
          | running made =>
              dsimp only [move] at actual;cases Option.some.inj actual
              simp only [State.rank,EscrowBudget.OfferAcquisition.State.rank,afterOffer_exact _ made generated];omega
      | opening | funding | checking | calculating =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := EscrowBudget.OfferAcquisition.progress step;simp only [State.rank];omega)
  | continuing made generated cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,EscrowBudget.Programme.ContinuationAcquisition.State.rank];omega
      | opening | execution =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := EscrowBudget.Programme.ContinuationAcquisition.progress made step;simp only [State.rank];omega)
  | sealing => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done {quota : catalogue.Quota} (before : State catalogue quota) : move before = none ↔ before.done = true := by
  cases before with
  | offering cursor =>
      cases cursor with
      | finished attempt => cases attempt <;> simp [move,State.done]
      | opening | funding | checking | calculating =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (EscrowBudget.OfferAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | continuing made generated cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | opening | execution =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (EscrowBudget.Programme.ContinuationAcquisition.no_move_iff_done made _).mp stopped;cases done)
            | simp
  | sealing | finished => simp [move,State.done]
end EntryAcquisition

namespace OfferAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

variable {snapshot : Snapshot prepared} {catalogue : Catalogue snapshot}
private def quotaList (catalogue : Catalogue snapshot) (limit : Nat) (bound : limit = catalogue.bound) : List catalogue.Quota :=
  (List.finRange (limit+1)).map fun quota => ⟨quota.val,by rw [←bound];exact quota.isLt⟩
private theorem quotaList_exact (catalogue : Catalogue snapshot) (limit : Nat) (bound : limit = catalogue.bound) :
    quotaList catalogue limit bound = catalogue.quotas := by
  subst limit;simp only [quotaList,Catalogue.quotas];exact List.map_id _
private theorem canonical (pool : Pool catalogue) : pool = generate catalogue := by
  rcases pool with ⟨cached,generated,keys⟩;cases generated;rfl
inductive State (catalogue : Catalogue snapshot) where
  | reading (cached : List (Cached catalogue)) (remaining : List catalogue.Quota)
      (conserved : cached++remaining.map (fun quota => ⟨quota,enter catalogue quota⟩) = entries catalogue)
  | working (cached : List (Cached catalogue)) (quota : catalogue.Quota) (rest : List catalogue.Quota)
      (conserved : cached++(quota::rest).map (fun quota => ⟨quota,enter catalogue quota⟩) = entries catalogue)
      (cursor : EntryAcquisition.State catalogue quota)
  | finished (pool : Pool catalogue) (generated : pool = generate catalogue)
def initial (catalogue : Catalogue snapshot) (limit : Nat) (bound : limit = catalogue.bound) : State catalogue :=
  .reading [] (quotaList catalogue limit bound) (by rw [quotaList_exact];rfl)
inductive Event (catalogue : Catalogue snapshot) where
  | opened (quota : catalogue.Quota)
  | entryStep (quota : catalogue.Quota) (event : EntryAcquisition.Event catalogue quota)
  | entered (quota : catalogue.Quota) (entry : Entry catalogue quota) (actual : entry = enter catalogue quota)
  | installed (pool : Pool catalogue) (generated : pool = generate catalogue)
def move : State catalogue → Option (State catalogue × Event catalogue)
  | .reading cached (quota::rest) conserved =>
      some (.working cached quota rest conserved (EntryAcquisition.initial catalogue quota),.opened quota)
  | .working cached quota rest conserved (.finished entry generated) =>
      some (.reading (cached++[⟨quota,entry⟩]) rest (by
        simpa only [generated,List.map_cons,List.append_assoc,List.singleton_append] using conserved),.entered quota entry generated)
  | .working cached quota rest conserved cursor@(.offering ..)
  | .working cached quota rest conserved cursor@(.continuing ..)
  | .working cached quota rest conserved cursor@(.sealing ..) =>
      match _step : EntryAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.working cached quota rest conserved after,.entryStep quota event)
  | .reading cached [] conserved =>
      let generated : cached = entries catalogue := by simpa only [List.map_nil,List.append_nil] using conserved
      let pool : Pool catalogue := ⟨cached,generated,by rw [generated];exact (generate catalogue).keys_exact⟩
      some (.finished pool (canonical pool),.installed pool (canonical pool))
  | .finished .. => none
def quotaWeight (quota : catalogue.Quota) := (EntryAcquisition.initial catalogue quota).rank+3
def remainingWeight (catalogue : Catalogue snapshot) (remaining : List catalogue.Quota) := (remaining.map quotaWeight).sum
def State.rank : State catalogue → Nat
  | .reading _ remaining _ => remainingWeight catalogue remaining+1
  | .working _ _ rest _ cursor => remainingWeight catalogue rest+cursor.rank+2
  | .finished .. => 0
def State.done : State catalogue → Bool | .finished .. => true | _ => false
theorem initial_rank (catalogue : Catalogue snapshot) (limit : Nat) (bound : limit = catalogue.bound) :
    (initial catalogue limit bound).rank = remainingWeight catalogue catalogue.quotas+1 := by
  simp only [initial,State.rank,quotaList_exact]
theorem progress {before after : State catalogue} {event : Event catalogue}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | reading cached remaining conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,remainingWeight,quotaWeight,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil];omega
  | working cached quota rest conserved cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,EntryAcquisition.State.rank];omega
      | offering | continuing | sealing =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := EntryAcquisition.progress step;simp only [State.rank];omega)
  | finished => cases actual
theorem no_move_iff_done (before : State catalogue) : move before = none ↔ before.done = true := by
  cases before with
  | reading cached remaining conserved => cases remaining <;> simp [move,State.done]
  | working cached quota rest conserved cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | offering | continuing | sealing =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (EntryAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | finished => simp [move,State.done]
end OfferAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.Comparison
