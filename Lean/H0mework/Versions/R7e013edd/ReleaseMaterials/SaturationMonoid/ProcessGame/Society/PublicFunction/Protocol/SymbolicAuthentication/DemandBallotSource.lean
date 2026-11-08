import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandScheduleExecution

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandBallotSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open DemandScheduleExecution

-- Admission of the original supply operation is fixed by Code; actual Inputs decide refill at each cut.
def run (cursor : Cursor code) (rivals : Nat → Opponent code) (demands : List Bool) : Report :=
  DemandScheduleExecution.run cursor (fun _ => true) rivals demands

abbrev vocabulary := RenewedQuorumSource.vocabulary
abbrev Ballot := StageBudget.Ballot (code := code)
def ballots (report : Report) : List Ballot :=
  report.charges.filterMap fun charge => StageBudget.issued vocabulary charge.row 0

theorem every_generated_charge_retains_its_actual_payer
    (rivals : Nat → Opponent code) (n : Nat) (cursor : Cursor code)
    (before : Feedback.State code) (correct : before = EventStep.seed cursor) (demands : List Bool) :
    ∀ charge ∈ (steps (fun _ => true) rivals n cursor before correct demands).charges,
      DemandSchedulePolicy.payer charge.row = true := by
  induction n generalizing cursor before demands with
  | zero => simp [steps,empty]
  | succ n ih =>
    cases demands with
    | nil => simp [steps,empty]
    | cons second tail =>
      simp only [steps]
      split_ifs with stopped actual paid
      · simp [empty]
      · intro charge member
        rcases List.mem_cons.mp member with first | later
        · subst charge;exact actual
        · exact ih _ _ _ tail charge later
      · simp
      · exact ih _ _ _ (second :: tail)

theorem every_paid_original_fee_generates_an_actual_native_ballot
    (charge : Charge) (payer : DemandSchedulePolicy.payer charge.row = true) :
    ∃ site, StageTrace.activation charge.row = some site ∧
      StageBudget.issued vocabulary charge.row 0 =
        some ⟨charge.row.cursor.cut,0,site,1,RenewedQuorumSource.slot charge.second,true,1⟩ := by
  unfold DemandSchedulePolicy.payer at payer
  cases activated : StageTrace.activation charge.row with
  | none => simp only [activated] at payer;cases payer
  | some site =>
    refine ⟨site,rfl,?_⟩
    have labelled : vocabulary.decode (RenewedQuorumSource.fee charge.second).purpose =
        some (RenewedQuorumSource.slot charge.second,true) := by cases charge.second <;> rfl
    have epoch : (RenewedQuorumSource.slot charge.second).epoch = vocabulary.epoch charge.row.before.current := rfl
    have signer : (RenewedQuorumSource.fee charge.second).signer = code.siteParty site := rfl
    have debit : code.law.actualDebit charge.row.before.current (RenewedQuorumSource.fee charge.second) =
        [((1,Repayment.Recovery.Good.service),1)] := by
      rw [RawLaw.actualDebit,if_pos charge.paid]
      cases charge.second <;> rfl
    simp only [StageBudget.issued,StageBudget.outcome,activated,StageTrace.items,charge.submitted,
      RawLaw.rawItems,RawLaw.execute,List.getElem?_cons_zero]
    unfold OwnedAttestation.classify
    rw [labelled]
    simp only [epoch,signer,ne_eq,not_true_eq_false,if_false,charge.paid,debit]
    norm_num [flowAt,locate,amount]

theorem every_served_request_has_a_verified_ballot_in_the_same_actual_history
    (cursor : Cursor code) (rivals : Nat → Opponent code) (demands : List Bool)
    (charge : Charge) (member : charge ∈ (run cursor rivals demands).charges) :
    ∃ body ∈ ballots (run cursor rivals demands),
      StageBudget.verify vocabulary cursor (run cursor rivals demands).stages body = true ∧
      body.cut = charge.row.cursor.cut ∧ body.position = 0 ∧
      body.scope = RenewedQuorumSource.slot charge.second ∧ body.choice = true ∧ body.fee = 1 := by
  have payer := every_generated_charge_retains_its_actual_payer rivals _ cursor _ rfl demands charge member
  obtain ⟨site,_,issued⟩ := every_paid_original_fee_generates_an_actual_native_ballot charge payer
  let body : Ballot := ⟨charge.row.cursor.cut,0,site,1,RenewedQuorumSource.slot charge.second,true,1⟩
  have original := (generated_steps_are_actual_ordered_paid_occurrences (fun _ => true) rivals _ cursor _ rfl demands).2.2.1 charge member
  have ledger : body ∈ StageBudget.ledger vocabulary cursor (run cursor rivals demands).stages := by
    apply List.mem_flatMap.mpr
    refine ⟨charge.row,original,List.mem_filterMap.mpr ⟨0,?_,issued⟩⟩
    exact List.mem_range.mpr (by rw [charge.submitted];simp only [List.length_singleton];omega)
  exact ⟨body,List.mem_filterMap.mpr ⟨charge,member,issued⟩,decide_eq_true ledger,rfl,rfl,rfl,rfl,rfl⟩

theorem no_served_request_is_lost_at_the_authentication_boundary
    (cursor : Cursor code) (rivals : Nat → Opponent code) (demands : List Bool) :
    (ballots (run cursor rivals demands)).length = (run cursor rivals demands).served.length := by
  have paid := every_generated_charge_retains_its_actual_payer rivals (EventStep.seed cursor).remaining cursor _ rfl demands
  change ∀ charge ∈ (run cursor rivals demands).charges, DemandSchedulePolicy.payer charge.row = true at paid
  change ((run cursor rivals demands).charges.filterMap (fun charge => StageBudget.issued vocabulary charge.row 0)).length =
    ((run cursor rivals demands).charges.map Charge.second).length
  rw [List.length_map]
  generalize (run cursor rivals demands).charges = charges at paid ⊢
  induction charges with
  | nil => rfl
  | cons charge tail ih =>
    obtain ⟨site,_,issued⟩ := every_paid_original_fee_generates_an_actual_native_ballot charge (paid charge List.mem_cons_self)
    simp only [List.filterMap_cons,issued,List.length_cons]
    exact congrArg Nat.succ (ih (fun later member => paid later (List.mem_cons_of_mem charge member)))

theorem supply_activation_is_decided_by_the_actual_resource_gap
    (current : RecycledQuorumMaterial.Current) (second : Bool)
    (key : code.Key) (inside : key ∈ code.keys) (supplier : key.1 = 2) :
    ((DemandSchedulePolicy.compile current true second).events key inside).val =
      if DemandRenewalStep.refill current then some ⟨.activate key.1,
        by rw [supplier];simp [code,RenewedQuorumSource.code]⟩ else none := by
  simp only [DemandSchedulePolicy.compile,supplier,ite_true,Bool.true_and]
  split
  · simp only [RenewedQuorumSource.activation,supplier]
  · rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandBallotSource
