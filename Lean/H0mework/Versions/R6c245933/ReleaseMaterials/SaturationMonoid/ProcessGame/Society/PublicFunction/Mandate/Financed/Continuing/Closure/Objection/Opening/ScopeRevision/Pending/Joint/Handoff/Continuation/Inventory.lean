import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Challenge

/-! The joint after-cut inventory saves all old native states together with
the new scope's births. An append consumes exactly one actual source visit. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.BalanceConservation
noncomputable section
section Source
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {past : List (List Action)} (fresh : Handoff.Ready bound past)
abbrev currentAt (inputs : List (List Action)) := OutstandingSource.History.currentAt (source fresh) inputs (inputs.length + 2)
abbrev inputAt (inputs : List (List Action)) := OutstandingSource.History.input (source fresh) inputs

def boundarySource (inputs : List (List Action)) : Mandate.Challenge.ScopeBoundary.Source base :=
  ⟨fresh.scope,newBound fresh,inputs⟩
end Source

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)

abbrev oldInputs := (Future.advance authority inventory .revision).inputs
abbrev oldInventory := Future.advance authority inventory .revision

structure Inventory where
  private mk ::
  inputs : List (List Action)
  oldGrants : List (Sigma fun record : Mandate.Challenge.Cross.GrantResident (Pending.B authority) (oldInputs authority inventory) => Grant.Saved fresh record)
  oldChallenges : List (Sigma fun record : Mandate.Challenge.Cross.Resident (Pending.B authority) (oldInputs authority inventory) => Challenge.Saved fresh record)
  oldServices : (index : (Pending.B authority).source.Slot) →
    OutstandingSource.History.NativeService.Expired.Continuation (Pending.B authority).source ((oldInventory authority inventory).services index)
  grants : List (Mandate.Challenge.Cross.GrantResident (newBound fresh) inputs)
  objections : List (Mandate.Challenge.Cross.Resident (newBound fresh) inputs)
  services : (index : (source fresh).Slot) →
    OutstandingSource.History.NativeService.Thread (source fresh) (epochInputs fresh) index inputs
  finance : Pending.Joint.Finance.Account
  compatible : ∀ targetInputs, Compatible Pending.Joint.Finance.sources (inputAt fresh targetInputs) finance.current
  matrix : Financial.Family.ledgerClaims Pending.Joint.Finance.sources finance.current = (currentAt fresh inputs).claims

def initial (epoch : EpochDisposition authority inventory fresh) : Inventory authority inventory fresh :=
  ⟨epochInputs fresh,
    epoch.oldGrants.map (fun entry => ⟨entry.original,Grant.initial entry⟩),
    epoch.oldChallenges.map (fun entry => ⟨entry.original,Challenge.initial entry⟩),
    epoch.oldServices,epoch.grants,epoch.objections,
    fun index => OutstandingSource.History.NativeService.Thread.initial (source fresh) index,
    epoch.account,(by
      intro targetInputs
      rw [epoch.account_exact]
      exact continueVisits_compatible _ (Handoff.I fresh) 0 4 _
        (Handoff.Finance.original_compatible authority inventory fresh)),epoch.matrix⟩

variable {authority inventory fresh}

def receipts (saved : Inventory authority inventory fresh) (word : List Action) :=
  Mandate.Challenge.ScopeBoundary.receiptsAt (boundarySource fresh (saved.inputs ++ [word])) (saved.inputs.length + 2)

def observations (saved : Inventory authority inventory fresh) (word : List Action) :=
  (OutstandingSource.History.NativeService.ExpiredInput.read (Pending.B authority).source (source fresh)
    (saved.inputs ++ [word]) (saved.inputs.length + 1)).toList

def nextFinance (saved : Inventory authority inventory fresh) (word : List Action) :=
  Financial.Family.consumeVisit Pending.Joint.Finance.sources (inputAt fresh (saved.inputs ++ [word])) (saved.inputs.length + 2) saved.finance

def submit (saved : Inventory authority inventory fresh) (word : List Action) : Inventory authority inventory fresh :=
  ⟨saved.inputs ++ [word],
    saved.oldGrants.map (fun entry => ⟨entry.1,entry.2.consume (boundarySource fresh (saved.inputs ++ [word])) (receipts saved word)⟩),
    saved.oldChallenges.map (fun entry => ⟨entry.1,entry.2.consume (boundarySource fresh (saved.inputs ++ [word]))
      (Handoff.Challenge.laterWindow fresh) (receipts saved word)⟩),
    fun index => (saved.oldServices index).consume (Pending.B authority).source (observations saved word),
    Mandate.Challenge.Cross.advanceGrants (newBound fresh) saved.grants word,
    Mandate.Challenge.Cross.advanceAll (newBound fresh) saved.objections word,
    fun index => (saved.services index).advance (source fresh) word,
    nextFinance saved word,(by
      intro targetInputs
      exact consumeVisit_compatible _ (inputAt fresh (saved.inputs ++ [word])) _ _ (saved.compatible _)),(by
      have matched : Financial.Family.ledgerClaims Pending.Joint.Finance.sources saved.finance.current =
          (OutstandingSource.History.currentAt (source fresh) (saved.inputs ++ [word]) (saved.inputs.length + 2)).claims := by
        have before : OutstandingSource.History.currentAt (source fresh) (saved.inputs ++ [word]) (saved.inputs.length + 2) =
            currentAt fresh saved.inputs := Mandate.Challenge.Cross.emitted_word_uses_actual_cut (newBound fresh) saved.inputs word
        rw [before]
        exact saved.matrix
      simpa only [nextFinance,currentAt,OutstandingSource.History.currentAt,inputAt,Pending.Joint.Finance.sources,id_eq,
        List.length_append,List.length_singleton,Nat.add_assoc,Nat.reduceAdd] using
        consumeVisit_claims_source_next Pending.Joint.Finance.sources (inputAt fresh (saved.inputs ++ [word]))
          (saved.inputs.length + 2) saved.finance (saved.compatible _) matched)⟩

def actual (saved : Inventory authority inventory fresh) (word : List Action) :=
  OutstandingSource.History.actualExecution (source fresh) (submit saved word).inputs (saved.inputs.length + 1)

theorem actual_word_and_cut (saved : Inventory authority inventory fresh) (word : List Action) :
    (actual saved word).submitted = word ∧ (actual saved word).before = currentAt fresh saved.inputs :=
  ⟨Mandate.Challenge.Cross.emitted_word_is_actual (newBound fresh) saved.inputs word,
    Mandate.Challenge.Cross.emitted_word_uses_actual_cut (newBound fresh) saved.inputs word⟩

def financialRun (saved : Inventory authority inventory fresh) (word : List Action) :
    (Financial.Family.process Pending.Joint.Finance.sources).Run saved.finance.current (submit saved word).finance.current :=
  Financial.Family.visitRun _ _ _ _

def financialMigration (saved : Inventory authority inventory fresh) (word : List Action)
    (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary Pending.Joint.Finance.sources))
    (present : saved.finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow _ (financialRun saved word) index slot present

theorem every_saved_grant_keeps_its_original_record_in_order (saved : Inventory authority inventory fresh) (word : List Action) :
    (submit saved word).oldGrants.map Sigma.fst = saved.oldGrants.map Sigma.fst := by
  simp only [submit,List.map_map]
  rfl

theorem every_saved_challenge_keeps_its_original_record_in_order (saved : Inventory authority inventory fresh) (word : List Action) :
    (submit saved word).oldChallenges.map Sigma.fst = saved.oldChallenges.map Sigma.fst := by
  simp only [submit,List.map_map]
  rfl

theorem only_actual_new_grants_are_added (saved : Inventory authority inventory fresh) (word : List Action) :
    (submit saved word).grants = saved.grants.map (fun record => record.advance (newBound fresh) word) ++
      Mandate.Challenge.Cross.newbornGrants (newBound fresh) word := rfl

theorem only_actual_new_challenges_are_added (saved : Inventory authority inventory fresh) (word : List Action) :
    (submit saved word).objections = saved.objections.map (fun record => record.advance (newBound fresh) word) ++
      Mandate.Challenge.Cross.newborn (newBound fresh) word := rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation
