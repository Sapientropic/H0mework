import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Finance.Runtime

/-! The joint after-cut inventory saves all old native states together with
the new scope's births. An append consumes exactly one actual source visit. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Continuation

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.BalanceConservation
noncomputable section
open Handoff.Continuation

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs) (original : List Action)

abbrev oldInputs := (Future.advance authority inventory .revision).inputs
abbrev oldInventory := Future.advance authority inventory .revision

structure Inventory where
  private mk ::
  inputs : List (List Action)
  paidPast : Registered.inputs authority inventory fresh original <+: inputs
  oldGrants : List (Sigma fun record : Mandate.Challenge.Cross.GrantResident (Pending.B authority) (oldInputs authority inventory) => Handoff.Continuation.Grant.Saved fresh record)
  oldChallenges : List (Sigma fun record : Mandate.Challenge.Cross.Resident (Pending.B authority) (oldInputs authority inventory) => Handoff.Continuation.Challenge.Saved fresh record)
  oldServices : (index : (Pending.B authority).source.Slot) →
    OutstandingSource.History.NativeService.Expired.Continuation (Pending.B authority).source ((oldInventory authority inventory).services index)
  grants : List (Mandate.Challenge.Cross.GrantResident (newBound fresh) inputs)
  objections : List (Mandate.Challenge.Cross.Resident (newBound fresh) inputs)
  services : (index : (source fresh).Slot) →
    OutstandingSource.History.NativeService.Thread (source fresh) (Registered.inputs authority inventory fresh original) index inputs
  finance : Pending.Joint.Finance.Account
  compatible : ∀ targetInputs, Compatible Pending.Joint.Finance.sources (Handoff.Continuation.inputAt fresh targetInputs) finance.current
  matrix : Financial.Family.ledgerClaims Pending.Joint.Finance.sources finance.current = (Handoff.Continuation.currentAt fresh inputs).claims

def initial : Inventory authority inventory fresh original :=
  ⟨Registered.inputs authority inventory fresh original,List.prefix_rfl,
    Registered.oldGrants authority inventory fresh original,Registered.oldChallenges authority inventory fresh original,
    Registered.oldService authority inventory fresh original,Registered.newGrants authority inventory fresh original,
    Registered.newChallenges authority inventory fresh original,Registered.newServices authority inventory fresh original,
    Registered.account authority inventory fresh original,(by
      intro targetInputs
      exact continueVisits_compatible _ (Registered.input authority inventory fresh original) 0 4 _
        (Registered.compatible authority inventory fresh original)),Registered.financial_matrix_is_the_same_actual_after authority inventory fresh original⟩

variable {authority inventory fresh original}

def receipts (saved : Inventory authority inventory fresh original) (word : List Action) :=
  Mandate.Challenge.ScopeBoundary.receiptsAt (Handoff.Continuation.boundarySource fresh (saved.inputs ++ [word])) (saved.inputs.length + 2)

def observations (saved : Inventory authority inventory fresh original) (word : List Action) :=
  (OutstandingSource.History.NativeService.ExpiredInput.read (Pending.B authority).source (source fresh)
    (saved.inputs ++ [word]) (saved.inputs.length + 1)).toList

def nextFinance (saved : Inventory authority inventory fresh original) (word : List Action) :=
  Financial.Family.consumeVisit Pending.Joint.Finance.sources (Handoff.Continuation.inputAt fresh (saved.inputs ++ [word])) (saved.inputs.length + 2) saved.finance

def submit (saved : Inventory authority inventory fresh original) (word : List Action) : Inventory authority inventory fresh original :=
  ⟨saved.inputs ++ [word],saved.paidPast.trans (List.prefix_append _ _),
    saved.oldGrants.map (fun entry => ⟨entry.1,entry.2.consume (Handoff.Continuation.boundarySource fresh (saved.inputs ++ [word])) (receipts saved word)⟩),
    saved.oldChallenges.map (fun entry => ⟨entry.1,entry.2.consume (Handoff.Continuation.boundarySource fresh (saved.inputs ++ [word]))
      (Handoff.Challenge.laterWindow fresh) (receipts saved word)⟩),
    fun index => (saved.oldServices index).consume (Pending.B authority).source (observations saved word),
    Mandate.Challenge.Cross.advanceGrants (newBound fresh) saved.grants word,
    Mandate.Challenge.Cross.advanceAll (newBound fresh) saved.objections word,
    fun index => (saved.services index).advance (source fresh) word,
    nextFinance saved word,(by
      intro targetInputs
      exact consumeVisit_compatible _ (Handoff.Continuation.inputAt fresh (saved.inputs ++ [word])) _ _ (saved.compatible _)),(by
      have matched : Financial.Family.ledgerClaims Pending.Joint.Finance.sources saved.finance.current =
          (OutstandingSource.History.currentAt (source fresh) (saved.inputs ++ [word]) (saved.inputs.length + 2)).claims := by
        have before : OutstandingSource.History.currentAt (source fresh) (saved.inputs ++ [word]) (saved.inputs.length + 2) =
            Handoff.Continuation.currentAt fresh saved.inputs := Mandate.Challenge.Cross.emitted_word_uses_actual_cut (newBound fresh) saved.inputs word
        rw [before]
        exact saved.matrix
      simpa only [nextFinance,Handoff.Continuation.currentAt,OutstandingSource.History.currentAt,Handoff.Continuation.inputAt,Pending.Joint.Finance.sources,id_eq,
        List.length_append,List.length_singleton,Nat.add_assoc,Nat.reduceAdd] using
        consumeVisit_claims_source_next Pending.Joint.Finance.sources (Handoff.Continuation.inputAt fresh (saved.inputs ++ [word]))
          (saved.inputs.length + 2) saved.finance (saved.compatible _) matched)⟩

def actual (saved : Inventory authority inventory fresh original) (word : List Action) :=
  OutstandingSource.History.actualExecution (source fresh) (submit saved word).inputs (saved.inputs.length + 1)

theorem actual_word_and_cut (saved : Inventory authority inventory fresh original) (word : List Action) :
    (actual saved word).submitted = word ∧ (actual saved word).before = Handoff.Continuation.currentAt fresh saved.inputs :=
  ⟨Mandate.Challenge.Cross.emitted_word_is_actual (newBound fresh) saved.inputs word,
    Mandate.Challenge.Cross.emitted_word_uses_actual_cut (newBound fresh) saved.inputs word⟩

def financialRun (saved : Inventory authority inventory fresh original) (word : List Action) :
    (Financial.Family.process Pending.Joint.Finance.sources).Run saved.finance.current (submit saved word).finance.current :=
  Financial.Family.visitRun _ _ _ _

def financialMigration (saved : Inventory authority inventory fresh original) (word : List Action)
    (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary Pending.Joint.Finance.sources))
    (present : saved.finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow _ (financialRun saved word) index slot present

theorem every_saved_grant_keeps_its_original_record_in_order (saved : Inventory authority inventory fresh original) (word : List Action) :
    (submit saved word).oldGrants.map Sigma.fst = saved.oldGrants.map Sigma.fst := by
  simp only [submit,List.map_map]
  rfl

theorem every_saved_challenge_keeps_its_original_record_in_order (saved : Inventory authority inventory fresh original) (word : List Action) :
    (submit saved word).oldChallenges.map Sigma.fst = saved.oldChallenges.map Sigma.fst := by
  simp only [submit,List.map_map]
  rfl

theorem only_actual_new_grants_are_added (saved : Inventory authority inventory fresh original) (word : List Action) :
    (submit saved word).grants = saved.grants.map (fun record => record.advance (newBound fresh) word) ++
      Mandate.Challenge.Cross.newbornGrants (newBound fresh) word := rfl

theorem only_actual_new_challenges_are_added (saved : Inventory authority inventory fresh original) (word : List Action) :
    (submit saved word).objections = saved.objections.map (fun record => record.advance (newBound fresh) word) ++
      Mandate.Challenge.Cross.newborn (newBound fresh) word := rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Continuation
