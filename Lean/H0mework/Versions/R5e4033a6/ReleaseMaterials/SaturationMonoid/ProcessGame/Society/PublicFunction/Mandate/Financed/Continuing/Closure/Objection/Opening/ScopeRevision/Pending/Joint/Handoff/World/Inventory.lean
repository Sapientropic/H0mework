import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Cohort

/-! Every epoch carries all past origins and its own current native births.
The common financial carrier is denominated in the actual base law's units. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.BalanceConservation
noncomputable section

abbrev sources := Pending.Joint.Finance.sources
abbrev Account := Pending.Joint.Finance.Account
abbrev I (epoch : Epoch) (inputs : List (List Action)) := OutstandingSource.History.input epoch.source inputs
abbrev current (epoch : Epoch) (inputs : List (List Action)) := OutstandingSource.History.currentAt epoch.source inputs (inputs.length + 2)
def boundarySource (epoch : Epoch) (inputs : List (List Action)) : Mandate.Challenge.ScopeBoundary.Source base :=
  ⟨epoch.scope,epoch.bound,inputs⟩

def Denominated (account : Account) : Prop :=
  ∀ claim ∈ account.current.slots.map (Financial.Family.slotClaim sources),
    base.settlementUnit claim.2.instrument = (sources claim.1).law.settlementUnit claim.2.instrument ∧
    base.settlementRate claim.2.instrument = (sources claim.1).law.settlementRate claim.2.instrument

structure Inventory (epoch : Epoch) where
  private mk ::
  inputs : List (List Action)
  originOpening : Handoff.Outcome epoch.fresh
  originOpening_exact : originOpening = Handoff.outcome epoch.fresh
  pastGrants : List GrantCohort
  pastChallenges : List (ChallengeCohort epoch.scope)
  pastServices : List (ServiceCohort epoch.source.seed.initial.clock)
  grants : List (Mandate.Challenge.Cross.GrantResident epoch.bound inputs)
  objections : List (Mandate.Challenge.Cross.Resident epoch.bound inputs)
  services : (index : epoch.source.Slot) → OutstandingSource.History.NativeService.Thread epoch.source (epochInputs epoch.fresh) index inputs
  finance : Account
  denominated : Denominated finance
  matrix : Financial.Family.ledgerClaims sources finance.current = (current epoch inputs).claims

variable {epoch : Epoch}

theorem Inventory.compatible (inventory : Inventory epoch) (target : Epoch) (inputs : List (List Action)) :
    Compatible sources (I target inputs) inventory.finance.current := inventory.denominated

def initial {fuel : ℚ} {old : Followup.Joint.Inventory fuel} {authority : ScopeRevision.Ready old}
    {originInputs : List (List Action)} {inventory : Pending.Joint.Inventory authority originInputs}
    {fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs}
    (saved : Continuation.Inventory authority inventory fresh) : Inventory (Epoch.ofFresh fresh) :=
  ⟨saved.inputs,Handoff.outcome fresh,rfl,
    saved.oldGrants.map (fun entry => ⟨⟨Epoch.ofFresh fresh,entry.1⟩,entry.2⟩),
    saved.oldChallenges.map (fun entry => ⟨⟨Epoch.ofFresh fresh,entry.1⟩,entry.2,Handoff.Challenge.laterWindow fresh⟩),
    (List.finRange (Pending.B authority).source.seed.task.slots.length).map (fun index =>
      ⟨⟨(Pending.B authority).source,originInputs,(Continuation.oldInventory authority inventory).inputs,index,
        (Continuation.oldInventory authority inventory).services index⟩,
        saved.oldServices index,fresh.actual_successor_is_after_the_expired_scope⟩),
    saved.grants,saved.objections,saved.services,saved.finance,saved.compatible [],saved.matrix⟩

def receipts (inventory : Inventory epoch) (word : List Action) :=
  Mandate.Challenge.ScopeBoundary.receiptsAt (boundarySource epoch (inventory.inputs ++ [word])) (inventory.inputs.length + 2)

def nextFinance (inventory : Inventory epoch) (word : List Action) :=
  Financial.Family.consumeVisit sources (I epoch (inventory.inputs ++ [word])) (inventory.inputs.length + 2) inventory.finance

def submit (inventory : Inventory epoch) (word : List Action) : Inventory epoch :=
  ⟨inventory.inputs ++ [word],inventory.originOpening,inventory.originOpening_exact,
    inventory.pastGrants.map (fun entry => entry.advance (boundarySource epoch (inventory.inputs ++ [word])) (receipts inventory word)),
    inventory.pastChallenges.map (fun entry => entry.advance (boundarySource epoch (inventory.inputs ++ [word])) (le_refl _) (receipts inventory word)),
    inventory.pastServices.map (fun entry => entry.advance (boundarySource epoch (inventory.inputs ++ [word])) (le_refl _) (inventory.inputs.length + 1) 1),
    Mandate.Challenge.Cross.advanceGrants epoch.bound inventory.grants word,
    Mandate.Challenge.Cross.advanceAll epoch.bound inventory.objections word,
    fun index => (inventory.services index).advance epoch.source word,
    nextFinance inventory word,
    consumeVisit_compatible sources (I epoch (inventory.inputs ++ [word])) _ _ (inventory.compatible epoch _),(by
      have before : OutstandingSource.History.currentAt epoch.source (inventory.inputs ++ [word]) (inventory.inputs.length + 2) = current epoch inventory.inputs :=
        Mandate.Challenge.Cross.emitted_word_uses_actual_cut epoch.bound inventory.inputs word
      have matched : Financial.Family.ledgerClaims sources inventory.finance.current =
          (OutstandingSource.History.currentAt epoch.source (inventory.inputs ++ [word]) (inventory.inputs.length + 2)).claims := by
        rw [before]; exact inventory.matrix
      simpa only [nextFinance,current,OutstandingSource.History.currentAt,I,sources,Pending.Joint.Finance.sources,id_eq,
        List.length_append,List.length_singleton,Nat.add_assoc,Nat.reduceAdd] using
        consumeVisit_claims_source_next sources (I epoch (inventory.inputs ++ [word])) (inventory.inputs.length + 2)
          inventory.finance (inventory.compatible epoch _) matched)⟩

def actual (inventory : Inventory epoch) (word : List Action) :=
  OutstandingSource.History.actualExecution epoch.source (submit inventory word).inputs (inventory.inputs.length + 1)

theorem actual_word_and_cut (inventory : Inventory epoch) (word : List Action) :
    (actual inventory word).submitted = word ∧ (actual inventory word).before = current epoch inventory.inputs :=
  ⟨Mandate.Challenge.Cross.emitted_word_is_actual epoch.bound inventory.inputs word,
    Mandate.Challenge.Cross.emitted_word_uses_actual_cut epoch.bound inventory.inputs word⟩

def financialRun (inventory : Inventory epoch) (word : List Action) :
    (Financial.Family.process sources).Run inventory.finance.current (submit inventory word).finance.current :=
  Financial.Family.visitRun _ _ _ _

def Inventory.actualOpening? (inventory : Inventory epoch) :=
  let actual := OutstandingSource.History.actualExecution epoch.source inventory.inputs 1
  if inventory.inputs.isEmpty then none else Handoff.decodePaidOpening epoch.fresh actual.before actual.submitted

theorem every_past_origin_keeps_order_and_multiplicity (inventory : Inventory epoch) (word : List Action) :
    (submit inventory word).pastGrants.map GrantCohort.origin = inventory.pastGrants.map GrantCohort.origin ∧
    (submit inventory word).pastChallenges.map ChallengeCohort.origin = inventory.pastChallenges.map ChallengeCohort.origin ∧
    (submit inventory word).pastServices.map ServiceCohort.origin = inventory.pastServices.map ServiceCohort.origin := by
  constructor
  · simp only [submit,List.map_map]; rfl
  constructor
  · change ((inventory.pastChallenges.map (fun entry => entry.advance (boundarySource epoch (inventory.inputs ++ [word])) (le_refl _) (receipts inventory word))).map ChallengeCohort.origin) = _
    rw [List.map_map]
    rfl
  · change ((inventory.pastServices.map (fun entry => entry.advance (boundarySource epoch (inventory.inputs ++ [word])) (le_refl _) (inventory.inputs.length + 1) 1)).map ServiceCohort.origin) = _
    rw [List.map_map]
    rfl

section Handoff
variable (inventory : Inventory epoch) (fresh : Handoff.Ready epoch.bound inventory.inputs)

abbrev nextEpoch := Epoch.ofFresh fresh
def nextReceipts := Mandate.Challenge.ScopeBoundary.receipts (Handoff.Challenge.occurrence fresh) 0 4
def nextAccount := Financial.Family.continueVisits sources (Handoff.I fresh) 0 4 inventory.finance

def currentGrant (record : Mandate.Challenge.Cross.GrantResident epoch.bound inventory.inputs) : GrantCohort :=
  ⟨⟨Epoch.ofFresh fresh,record⟩,Continuation.Grant.initial (Handoff.Grant.entry fresh record 4)⟩

def currentChallenge (record : Mandate.Challenge.Cross.Resident epoch.bound inventory.inputs) : ChallengeCohort fresh.scope :=
  ⟨⟨Epoch.ofFresh fresh,record⟩,Continuation.Challenge.initial (Handoff.Challenge.entry fresh record 4),Handoff.Challenge.laterWindow fresh⟩

def currentService (index : epoch.source.Slot) : ServiceCohort (Handoff.source fresh).seed.initial.clock :=
  ⟨⟨epoch.source,epochInputs epoch.fresh,inventory.inputs,index,inventory.services index⟩,
    Handoff.Service.continued fresh (inventory.services index) 3,fresh.actual_successor_is_after_the_expired_scope⟩

theorem window_follows : epoch.scope.task.earliest ≤ fresh.scope.task.earliest :=
  epoch.window.trans fresh.new_window_is_after_the_actual_expired_scope.le

theorem initial_clock_follows : epoch.source.seed.initial.clock ≤ (Handoff.source fresh).seed.initial.clock :=
  clock_after_initial epoch.source inventory.inputs (inventory.inputs.length + 2)

def handoff : Inventory (nextEpoch inventory fresh) :=
  ⟨epochInputs fresh,Handoff.outcome fresh,rfl,
    inventory.pastGrants.map (fun entry => entry.advance (Handoff.Challenge.occurrence fresh) (nextReceipts inventory fresh)) ++
      inventory.grants.map (currentGrant inventory fresh),
    (inventory.pastChallenges.map (fun entry => entry.advance (Handoff.Challenge.occurrence fresh)
      (window_follows inventory fresh) (nextReceipts inventory fresh)) : List (ChallengeCohort fresh.scope)) ++ inventory.objections.map (currentChallenge inventory fresh),
    (inventory.pastServices.map (fun entry => entry.advance (Handoff.Challenge.occurrence fresh)
      (initial_clock_follows inventory fresh) 0 3) : List (ServiceCohort (Handoff.source fresh).seed.initial.clock)) ++
      (List.finRange epoch.source.seed.task.slots.length).map (currentService inventory fresh),
    Handoff.grants fresh,Handoff.objections fresh,
    fun index => OutstandingSource.History.NativeService.Thread.initial (Handoff.source fresh) index,
    nextAccount inventory fresh,
    continueVisits_compatible sources (Handoff.I fresh) 0 4 inventory.finance (inventory.compatible (nextEpoch inventory fresh) _),(by
      have initial : Financial.Family.ledgerClaims sources inventory.finance.current = (Handoff.I fresh).initial.claims := inventory.matrix
      change Financial.Family.ledgerClaims sources (nextAccount inventory fresh).current =
        (OutstandingSource.History.currentAt (Handoff.source fresh) (epochInputs fresh) 4).claims
      exact continueVisits_claims_source sources (Handoff.I fresh) 0 4 inventory.finance
        (inventory.compatible (nextEpoch inventory fresh) _) initial)⟩

def handoffFinancialRun : (Financial.Family.process sources).Run inventory.finance.current (handoff inventory fresh).finance.current :=
  Financial.Family.continueVisits_run sources (Handoff.I fresh) 0 4 inventory.finance

def handoffFinancialMigration (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow sources (handoffFinancialRun inventory fresh) index slot present

theorem all_cohort_censuses_include_every_old_and_every_current_birth :
    (handoff inventory fresh).pastGrants.map GrantCohort.origin = inventory.pastGrants.map GrantCohort.origin ++
      inventory.grants.map (fun record => (⟨Epoch.ofFresh fresh,record⟩ : GrantOrigin)) ∧
    (handoff inventory fresh).pastChallenges.map ChallengeCohort.origin = inventory.pastChallenges.map ChallengeCohort.origin ++
      inventory.objections.map (fun record => (⟨Epoch.ofFresh fresh,record⟩ : ChallengeOrigin)) ∧
    (handoff inventory fresh).pastServices.map ServiceCohort.origin = inventory.pastServices.map ServiceCohort.origin ++
      (List.finRange epoch.source.seed.task.slots.length).map
        (fun index => (⟨epoch.source,epochInputs epoch.fresh,inventory.inputs,index,inventory.services index⟩ : ServiceOrigin)) := by
  constructor
  · simp only [handoff,List.map_append,List.map_map]; rfl
  constructor
  · change ((inventory.pastChallenges.map (fun entry => entry.advance (Handoff.Challenge.occurrence fresh)
      (window_follows inventory fresh) (nextReceipts inventory fresh)) : List (ChallengeCohort fresh.scope)) ++
        inventory.objections.map (currentChallenge inventory fresh)).map ChallengeCohort.origin = _
    dsimp only [Handoff.Challenge.occurrence,Handoff.newBound]
    rw [List.map_append,List.map_map,List.map_map]
    rfl
  · change ((inventory.pastServices.map (fun entry => entry.advance (Handoff.Challenge.occurrence fresh)
      (initial_clock_follows inventory fresh) 0 3) : List (ServiceCohort (Handoff.source fresh).seed.initial.clock)) ++
        (List.finRange epoch.source.seed.task.slots.length).map (currentService inventory fresh)).map ServiceCohort.origin = _
    dsimp only [Handoff.Challenge.occurrence,Handoff.newBound]
    rw [List.map_append,List.map_map,List.map_map]
    rfl

theorem original_task_homology_is_literal (index : epoch.source.Slot) :
    (Handoff.source fresh).seed.slot (Handoff.homologous fresh index) = epoch.source.seed.slot index :=
  Handoff.original_slot_content_is_preserved fresh index

section ActualOpening
variable (actualInputs : List (List Action))

def openingBoundary : Mandate.Challenge.ScopeBoundary.Source base :=
  ⟨fresh.scope,Handoff.newBound fresh,actualInputs⟩

def openingReceipts := Mandate.Challenge.ScopeBoundary.receipts (openingBoundary inventory fresh actualInputs) 0 (actualInputs.length+2)

def openingAccount := Financial.Family.continueVisits sources
  (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0 (actualInputs.length+2) inventory.finance

def openingCurrentGrant (record : Mandate.Challenge.Cross.GrantResident epoch.bound inventory.inputs) : GrantCohort :=
  ⟨⟨Epoch.ofFresh fresh,record⟩,
    (Continuation.Grant.beginAt (Handoff.Grant.entry fresh record 0)).consume
      (openingBoundary inventory fresh actualInputs) (openingReceipts inventory fresh actualInputs)⟩

def openingCurrentChallenge (record : Mandate.Challenge.Cross.Resident epoch.bound inventory.inputs) : ChallengeCohort fresh.scope :=
  ⟨⟨Epoch.ofFresh fresh,record⟩,
    (Continuation.Challenge.beginAt (Handoff.Challenge.entry fresh record 0)).consume
      (openingBoundary inventory fresh actualInputs) (Handoff.Challenge.laterWindow fresh)
      (openingReceipts inventory fresh actualInputs),Handoff.Challenge.laterWindow fresh⟩

def openingServiceObservations :=
  (List.range (actualInputs.length+1)).filterMap
    (OutstandingSource.History.NativeService.ExpiredInput.read epoch.source (Handoff.source fresh) actualInputs)

def openingCurrentService (index : epoch.source.Slot) : ServiceCohort (Handoff.source fresh).seed.initial.clock :=
  ⟨⟨epoch.source,epochInputs epoch.fresh,inventory.inputs,index,inventory.services index⟩,
    (OutstandingSource.History.NativeService.Expired.begin epoch.source (inventory.services index)).consume epoch.source
      (openingServiceObservations inventory fresh actualInputs),fresh.actual_successor_is_after_the_expired_scope⟩

/-- Every cohort and financial visit is generated from the supplied actual
history. The retained canonical outcome is a planning value; actual opening
evidence is decoded by Inventory.actualOpening? from these inputs. -/
def handoffAt : Inventory (nextEpoch inventory fresh) :=
  ⟨actualInputs,Handoff.outcome fresh,rfl,
    inventory.pastGrants.map (fun entry => entry.advance (openingBoundary inventory fresh actualInputs)
      (openingReceipts inventory fresh actualInputs)) ++ inventory.grants.map (openingCurrentGrant inventory fresh actualInputs),
    (inventory.pastChallenges.map (fun entry => entry.advance (openingBoundary inventory fresh actualInputs)
      (window_follows inventory fresh) (openingReceipts inventory fresh actualInputs)) : List (ChallengeCohort fresh.scope)) ++
      inventory.objections.map (openingCurrentChallenge inventory fresh actualInputs),
    (inventory.pastServices.map (fun entry => entry.advance (openingBoundary inventory fresh actualInputs)
      (initial_clock_follows inventory fresh) 0 (actualInputs.length+1)) : List (ServiceCohort (Handoff.source fresh).seed.initial.clock)) ++
      (List.finRange epoch.source.seed.task.slots.length).map (openingCurrentService inventory fresh actualInputs),
    Mandate.Challenge.Cross.grantsBefore (Handoff.newBound fresh) actualInputs,
    Mandate.Challenge.Cross.residentsAt (Handoff.newBound fresh) actualInputs,
    fun index => OutstandingSource.History.NativeService.Thread.fromInputs (Handoff.source fresh) index actualInputs,
    openingAccount inventory fresh actualInputs,
    continueVisits_compatible sources (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0 (actualInputs.length+2)
      inventory.finance (inventory.compatible (nextEpoch inventory fresh) _),(by
      have initial : Financial.Family.ledgerClaims sources inventory.finance.current =
          (OutstandingSource.History.input (Handoff.source fresh) actualInputs).initial.claims := inventory.matrix
      simpa only [openingAccount,current,nextEpoch,Epoch.source,Epoch.ofFresh,OutstandingSource.History.currentAt,sources,Pending.Joint.Finance.sources,id_eq,Nat.zero_add] using
        continueVisits_claims_source sources (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0
          (actualInputs.length+2) inventory.finance (inventory.compatible (nextEpoch inventory fresh) _) initial)⟩

def handoffAtFinancialRun : (Financial.Family.process sources).Run inventory.finance.current (handoffAt inventory fresh actualInputs).finance.current :=
  Financial.Family.continueVisits_run sources (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0
    (actualInputs.length+2) inventory.finance

theorem actual_handoff_keeps_all_old_and_current_origins :
    (handoffAt inventory fresh actualInputs).pastGrants.map GrantCohort.origin = inventory.pastGrants.map GrantCohort.origin ++
      inventory.grants.map (fun record => (⟨Epoch.ofFresh fresh,record⟩ : GrantOrigin)) ∧
    (handoffAt inventory fresh actualInputs).pastChallenges.map ChallengeCohort.origin = inventory.pastChallenges.map ChallengeCohort.origin ++
      inventory.objections.map (fun record => (⟨Epoch.ofFresh fresh,record⟩ : ChallengeOrigin)) ∧
    (handoffAt inventory fresh actualInputs).pastServices.map ServiceCohort.origin = inventory.pastServices.map ServiceCohort.origin ++
      (List.finRange epoch.source.seed.task.slots.length).map
        (fun index => (⟨epoch.source,epochInputs epoch.fresh,inventory.inputs,index,inventory.services index⟩ : ServiceOrigin)) := by
  constructor
  · simp only [handoffAt,List.map_append,List.map_map]; rfl
  constructor
  · change ((inventory.pastChallenges.map (fun entry => entry.advance (openingBoundary inventory fresh actualInputs)
      (window_follows inventory fresh) (openingReceipts inventory fresh actualInputs)) : List (ChallengeCohort fresh.scope)) ++
      inventory.objections.map (openingCurrentChallenge inventory fresh actualInputs)).map ChallengeCohort.origin = _
    dsimp only [openingBoundary]
    rw [List.map_append,List.map_map,List.map_map]
    rfl
  · change ((inventory.pastServices.map (fun entry => entry.advance (openingBoundary inventory fresh actualInputs)
      (initial_clock_follows inventory fresh) 0 (actualInputs.length+1)) : List (ServiceCohort (Handoff.source fresh).seed.initial.clock)) ++
      (List.finRange epoch.source.seed.task.slots.length).map (openingCurrentService inventory fresh actualInputs)).map ServiceCohort.origin = _
    exact List.map_append.trans
      (congrArg₂ List.append List.map_map List.map_map)

end ActualOpening

end Handoff

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
