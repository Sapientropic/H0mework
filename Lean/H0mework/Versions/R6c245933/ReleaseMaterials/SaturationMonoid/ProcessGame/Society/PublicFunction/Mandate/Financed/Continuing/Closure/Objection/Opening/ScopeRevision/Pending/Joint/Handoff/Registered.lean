import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Effects
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeService.Response

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.BalanceConservation
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (word : List Action)

abbrev legacy := Future.advance authority inventory .revision
def responseWord :=
  let after := (law fresh).next (start fresh) word
  Repayment.Portfolio.word (law fresh) (Handoff.debtPositions after) after
abbrev inputs := [word,responseWord authority inventory fresh word]
abbrev input := OutstandingSource.History.input (source fresh) (inputs authority inventory fresh word)
abbrev actual := OutstandingSource.History.actualExecution (source fresh) (inputs authority inventory fresh word) 1
abbrev final := OutstandingSource.History.currentAt (source fresh) (inputs authority inventory fresh word) 4
abbrev boundary : Mandate.Challenge.ScopeBoundary.Source base := ⟨fresh.scope,newBound fresh,inputs authority inventory fresh word⟩
def receipts := Mandate.Challenge.ScopeBoundary.receipts (boundary authority inventory fresh word) 0 4

theorem literal_input_and_original_in_window_cut :
    (actual authority inventory fresh word).submitted = word ∧ (actual authority inventory fresh word).before = start fresh := by
  refine ⟨OutstandingSource.History.scheduled_input_is_actual (source fresh) (inputs authority inventory fresh word) 0 (by simp),?_⟩
  change OutstandingSource.History.currentAt (source fresh) (inputs authority inventory fresh word) 2 = start fresh
  rw [(OutstandingSource.History.actual_frame _ _ _).1,
    OutstandingSource.History.finite_prefix_exact (source fresh) (inputs authority inventory fresh word) 0 (by simp)]
  rfl

theorem the_after_is_the_same_actual_source_successor : (actual authority inventory fresh word).after =
    OutstandingSource.History.currentAt (source fresh) (inputs authority inventory fresh word) 3 :=
  OutstandingSource.History.actual_next _ _ _

abbrev Legal := ∀ item ∈ (law fresh).rawItems (actual authority inventory fresh word).before (actual authority inventory fresh word).submitted,
  (law fresh).Valid item.before item.request
abbrev SlotPaid (index : (source fresh).Slot) :=
  (source fresh).SlotPaid (actual authority inventory fresh word).before (actual authority inventory fresh word).submitted index

inductive Assessment : Type where
  | private paid (legal : Legal authority inventory fresh word) (service : ∀ index, SlotPaid authority inventory fresh word index)
  | private invalid (reason : ∃ item ∈ (law fresh).rawItems (actual authority inventory fresh word).before (actual authority inventory fresh word).submitted,
      ¬ (law fresh).Valid item.before item.request)
  | private unpaid (legal : Legal authority inventory fresh word) (index : (source fresh).Slot) (missing : ¬ SlotPaid authority inventory fresh word index)
      (blocker : OutstandingSource.History.NativeService.Response.Blocker (source fresh)
        (actual authority inventory fresh word).before (actual authority inventory fresh word).submitted index)

def blocker (index : (source fresh).Slot) (unpaid : ¬ SlotPaid authority inventory fresh word index) :
    OutstandingSource.History.NativeService.Response.Blocker (source fresh)
      (actual authority inventory fresh word).before (actual authority inventory fresh word).submitted index := by
  by_cases early : (actual authority inventory fresh word).before.clock < (source fresh).seed.task.earliest
  · exact .early early
  by_cases late : (source fresh).seed.task.deadline <
      ((source fresh).seed.law.next (actual authority inventory fresh word).before (actual authority inventory fresh word).submitted).clock
  · exact .late late
  have absent : ¬ Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (source fresh).seed.law
      (actual authority inventory fresh word).before (actual authority inventory fresh word).submitted
      ((source fresh).seed.slot index).bearer ((source fresh).seed.slot index).goods ((source fresh).seed.slot index).purpose := by
    intro paid
    exact unpaid ⟨le_of_not_gt early,le_of_not_gt late,paid⟩
  refine .missingUse (fun empty => absent (Or.inl empty)) ?_
  intro item member matched accepted
  exact absent (Or.inr ⟨item,member,accepted,matched⟩)

def assess : Assessment authority inventory fresh word := by
  by_cases legal : Legal authority inventory fresh word
  · match failed : (List.finRange (source fresh).seed.task.slots.length).find? (fun index => decide (¬ SlotPaid authority inventory fresh word index)) with
    | some index =>
      have missing : ¬ SlotPaid authority inventory fresh word index := of_decide_eq_true
        (List.find?_some (p := fun i : (source fresh).Slot => decide (¬ SlotPaid authority inventory fresh word i)) failed)
      exact .unpaid legal index missing
        (blocker authority inventory fresh word index missing)
    | none =>
      apply Assessment.paid legal
      intro index
      have denied := List.find?_eq_none.mp failed index (List.mem_finRange _)
      by_contra missing
      rw [decide_eq_true missing] at denied
      exact denied rfl
  · apply Assessment.invalid
    classical
    by_contra absent
    apply legal
    intro item inside
    by_contra invalid
    exact absent ⟨item,inside,invalid⟩

def Assessment.isPaid : Assessment authority inventory fresh word → Bool
  | .paid .. => true
  | _ => false

theorem actual_paid_is_checked_not_supplied : (assess authority inventory fresh word).isPaid = true ↔
    Legal authority inventory fresh word ∧ ∀ index, SlotPaid authority inventory fresh word index := by
  constructor
  · intro checked
    cases selected : assess authority inventory fresh word
    next legal service => exact ⟨legal,service⟩
    next denied => simp only [selected,Assessment.isPaid,Bool.false_eq_true] at checked
    next legal index missing blocker => simp only [selected,Assessment.isPaid,Bool.false_eq_true] at checked
  · rintro ⟨legal,service⟩
    cases selected : assess authority inventory fresh word
    next valid paid => rfl
    next denied => obtain ⟨item,inside,invalid⟩ := denied; exact (invalid (legal item inside)).elim
    next valid index missing blocker => exact (missing (service index)).elim

def account := Financial.Family.continueVisits Pending.Joint.Finance.sources (input authority inventory fresh word) 0 4 (legacy authority inventory).finance

theorem compatible : Compatible Pending.Joint.Finance.sources (input authority inventory fresh word) (legacy authority inventory).finance.current := by
  intro claim inside
  exact (legacy authority inventory).financeGenerated.compatible authority [] claim inside

def financialRun : (Financial.Family.process Pending.Joint.Finance.sources).Run
    (legacy authority inventory).finance.current (account authority inventory fresh word).current :=
  Financial.Family.continueVisits_run _ _ _ _ _

theorem financial_matrix_is_the_same_actual_after :
    Financial.Family.ledgerClaims Pending.Joint.Finance.sources (account authority inventory fresh word).current =
      (final authority inventory fresh word).claims := by
  simpa only [account,final,OutstandingSource.History.currentAt,Nat.zero_add,id_eq,Pending.Joint.Finance.sources] using
    continueVisits_claims_source Pending.Joint.Finance.sources (input authority inventory fresh word) 0 4 (legacy authority inventory).finance
      (compatible authority inventory fresh word)
      (Pending.Joint.financial_matrix_at_every_actual_cut authority (legacy authority inventory))

def oldGrant (record : Mandate.Challenge.Cross.GrantResident (Pending.B authority) (legacy authority inventory).inputs) :=
  (Continuation.Grant.beginAt (Handoff.Grant.entry fresh record 0)).consume (boundary authority inventory fresh word) (receipts authority inventory fresh word)
def oldGrants : List (Sigma fun record : Mandate.Challenge.Cross.GrantResident (Pending.B authority) (legacy authority inventory).inputs => Continuation.Grant.Saved fresh record) :=
  (legacy authority inventory).grants.map fun record => ⟨record,oldGrant authority inventory fresh word record⟩

def oldChallenge (record : Mandate.Challenge.Cross.Resident (Pending.B authority) (legacy authority inventory).inputs) :=
  (Continuation.Challenge.beginAt (Handoff.Challenge.entry fresh record 0)).consume (boundary authority inventory fresh word)
    fresh.new_window_is_after_the_actual_expired_scope (receipts authority inventory fresh word)
def oldChallenges : List (Sigma fun record : Mandate.Challenge.Cross.Resident (Pending.B authority) (legacy authority inventory).inputs => Continuation.Challenge.Saved fresh record) :=
  (legacy authority inventory).objections.map fun record => ⟨record,oldChallenge authority inventory fresh word record⟩

def serviceObservations := (List.range 3).filterMap
  (OutstandingSource.History.NativeService.ExpiredInput.read (Pending.B authority).source (source fresh) (inputs authority inventory fresh word))
def oldService (index : (Pending.B authority).source.Slot) :=
  (OutstandingSource.History.NativeService.Expired.begin (Pending.B authority).source ((legacy authority inventory).services index)).consume
    (Pending.B authority).source (serviceObservations authority inventory fresh word)

private theorem clock_after_initial (ordinal : Nat) :
    (source fresh).seed.initial.clock ≤ (OutstandingSource.History.currentAt (source fresh) (inputs authority inventory fresh word) ordinal).clock := by
  induction ordinal with
  | zero => exact le_refl _
  | succ ordinal ih =>
    have step : (OutstandingSource.History.currentAt (source fresh) (inputs authority inventory fresh word) ordinal).clock ≤
        (OutstandingSource.History.currentAt (source fresh) (inputs authority inventory fresh word) (ordinal+1)).clock := by
      change (ProgrammeSource.rawCurrent (input authority inventory fresh word)
        (ProgrammeHistory.visitAt (input authority inventory fresh word) ordinal).current).clock ≤
        (ProgrammeSource.rawCurrent (input authority inventory fresh word)
          (ProgrammeSource.next (input authority inventory fresh word)
            (ProgrammeHistory.visitAt (input authority inventory fresh word) ordinal).current)).clock
      rw [ProgrammeSource.actual_raw_next]
      exact (input authority inventory fresh word).law.next_clock_nondecreasing _ _
    exact ih.trans step

theorem every_original_expired_service_sees_every_actual_visit_in_order :
    (serviceObservations authority inventory fresh word).map OutstandingSource.History.NativeService.ExpiredInput.depth = List.range 3 := by
  have expired (depth : Nat) : (Pending.B authority).source.seed.task.deadline <
      (OutstandingSource.History.currentAt (source fresh) (inputs authority inventory fresh word) (depth+1)).clock :=
    lt_of_lt_of_le fresh.actual_successor_is_after_the_expired_scope (clock_after_initial authority inventory fresh word (depth+1))
  unfold serviceObservations
  rw [List.map_filterMap]
  have select : (fun depth => Option.map OutstandingSource.History.NativeService.ExpiredInput.depth
      (OutstandingSource.History.NativeService.ExpiredInput.read (Pending.B authority).source
        (source fresh) (inputs authority inventory fresh word) depth)) = some := by
    funext depth
    simp only [OutstandingSource.History.NativeService.ExpiredInput.read,dif_pos (expired depth),Option.map_some]
  rw [select,List.filterMap_some]


theorem repayment_is_generated_from_this_actual_first_after :
    responseWord authority inventory fresh word = Repayment.Portfolio.word (law fresh)
      (Handoff.debtPositions (actual authority inventory fresh word).after) (actual authority inventory fresh word).after := by
  have after : (actual authority inventory fresh word).after = (law fresh).next (start fresh) word := by
    have generated := (actual authority inventory fresh word).after_exact
    rw [(literal_input_and_original_in_window_cut authority inventory fresh word).1,
      (literal_input_and_original_in_window_cut authority inventory fresh word).2] at generated
    exact generated
  unfold responseWord
  rw [after]


def newServices (index : (source fresh).Slot) :=
  OutstandingSource.History.NativeService.Thread.initial (source fresh) (originInputs := inputs authority inventory fresh word) index
def newGrants := Mandate.Challenge.Cross.grantsBefore (newBound fresh) (inputs authority inventory fresh word)
def newChallenges := Mandate.Challenge.Cross.residentsAt (newBound fresh) (inputs authority inventory fresh word)

theorem every_original_grant_and_challenge_keeps_order_and_multiplicity :
    (oldGrants authority inventory fresh word).map Sigma.fst = (legacy authority inventory).grants ∧
    (oldChallenges authority inventory fresh word).map Sigma.fst = (legacy authority inventory).objections := by
  simp only [oldGrants,oldChallenges,List.map_map]
  exact ⟨List.map_id _,List.map_id _⟩

theorem old_grant_history_is_original_then_the_same_actual_boundaries
    (record : Mandate.Challenge.Cross.GrantResident (Pending.B authority) (legacy authority inventory).inputs) :
    (oldGrant authority inventory fresh word record).state.history = record.history.state.history ++
      (receipts authority inventory fresh word).map (Continuation.Grant.image (boundary authority inventory fresh word) record.history.obligation) := by
  exact Continuation.Grant.Saved.consume_history _ _ _

theorem all_old_service_slots_still_have_their_original_identity (index : (Pending.B authority).source.Slot) :
    (oldService authority inventory fresh word index).state.current.slots =
      ((legacy authority inventory).services index).state.current.slots :=
  (oldService authority inventory fresh word index).slots

structure Receipt where
  private mk ::
  assessment : Assessment authority inventory fresh word
  grantStates : {states // states = oldGrants authority inventory fresh word}
  challengeStates : {states // states = oldChallenges authority inventory fresh word}
  serviceStates : {states // states = oldService authority inventory fresh word}
  bornGrants : {states // states = newGrants authority inventory fresh word}
  bornChallenges : {states // states = newChallenges authority inventory fresh word}
  bornServices : {states // states = newServices authority inventory fresh word}
  financialAccount : {states // states = account authority inventory fresh word}
  grants : (oldGrants authority inventory fresh word).map Sigma.fst = (legacy authority inventory).grants
  challenges : (oldChallenges authority inventory fresh word).map Sigma.fst = (legacy authority inventory).objections
  principal : (legacy authority inventory).finance.current.slots.map (Financial.Family.slotClaim Pending.Joint.Finance.sources) <+:
    (account authority inventory fresh word).current.slots.map (Financial.Family.slotClaim Pending.Joint.Finance.sources)
  matrix : Financial.Family.ledgerClaims Pending.Joint.Finance.sources (account authority inventory fresh word).current = (final authority inventory fresh word).claims

def produce : Receipt authority inventory fresh word :=
  ⟨assess authority inventory fresh word,⟨oldGrants authority inventory fresh word,rfl⟩,
    ⟨oldChallenges authority inventory fresh word,rfl⟩,⟨oldService authority inventory fresh word,rfl⟩,
    ⟨newGrants authority inventory fresh word,rfl⟩,⟨newChallenges authority inventory fresh word,rfl⟩,
    ⟨newServices authority inventory fresh word,rfl⟩,⟨account authority inventory fresh word,rfl⟩,(every_original_grant_and_challenge_keeps_order_and_multiplicity authority inventory fresh word).1,
    (every_original_grant_and_challenge_keeps_order_and_multiplicity authority inventory fresh word).2,
    Financial.Family.continueVisits_preserves_original_claims _ _ _ _ _,financial_matrix_is_the_same_actual_after authority inventory fresh word⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered
