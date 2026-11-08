import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 48000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumControls
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open OwnedQuorumSource OwnedQuorumDomain OwnedQuorumConsumer

def never : Controller := fun _ _ => false
def always : Controller := fun _ _ => true
def signerHold : Controller := fun cut _ => decide (cut = 18 ∨ cut = 24)
def mixedHold : Controller := fun cut _ => decide (cut = 18 ∨ cut = 26)
def early (cut : Nat) : Opponent code := EventStep.fixed
  (if cut = 25 then some ⟨.deliver 2,by decide⟩ else if cut = 27 then some ⟨.deliver 3,by decide⟩ else none)
def latest (cut : Nat) : Opponent code := EventStep.fixed
  (if cut = 41 then some ⟨.deliver 3,by decide⟩ else if cut = 47 then some ⟨.deliver 2,by decide⟩ else none)
def signerNetwork (cut : Nat) : Opponent code := EventStep.fixed
  (if cut = 31 then some ⟨.deliver 2,by decide⟩ else if cut = 41 then some ⟨.deliver 3,by decide⟩ else none)
def mixedNetwork (cut : Nat) : Opponent code := EventStep.fixed
  (if cut = 35 then some ⟨.deliver 3,by decide⟩ else if cut = 41 then some ⟨.deliver 2,by decide⟩ else none)

def conforms (control : Controller) (external : Nat → Opponent code) : Bool :=
  (List.range window).all fun index => decide
    (intake (actual control external index) (external (actual control external index).cursor.cut) ∈
      choices (actual control external index))
theorem conforms_iff (control : Controller) (external : Nat → Opponent code) :
    conforms control external = true ↔ Within control external window := by
  simp only [conforms,Within,List.all_eq_true,List.mem_range,decide_eq_true_eq]

theorem independently_changing_all_three_sites_has_actual_admitted_networks :
    conforms never early = true ∧ conforms always latest = true ∧
      conforms signerHold signerNetwork = true ∧ conforms mixedHold mixedNetwork = true := by decide +kernel

theorem all_three_source_sites_leave_actual_withholding_history :
    (finished always latest).omissions = [(16,2),(22,2)] ∧
      (finished signerHold signerNetwork).omissions = [(18,0),(24,0)] ∧
      (finished mixedHold mixedNetwork).omissions = [(18,0),(26,1)] := by decide +kernel

theorem authentication_is_generated_after_the_actual_withheld_signing_slots :
    ((encoding (finished never early) 2).map (·.cut)) = some 18 ∧
      ((encoding (finished signerHold signerNetwork) 2).map (·.cut)) = some 30 ∧
      ((ballots initial).filter fun body => decide (body.scope = RenewedQuorumSource.slot true)) = [] := by decide +kernel

theorem a_successful_quorum_and_actual_signing_withholding_coexist :
    result (finished signerHold signerNetwork) = .decided true ∧
      (observed (finished signerHold signerNetwork)).receipts.length = 2 ∧
      (finished signerHold signerNetwork).omissions = [(18,0),(24,0)] := by
  have completed := all_owned_signing_supply_and_delivery_controls_generate_the_original_quorum signerHold signerNetwork
    ((conforms_iff signerHold signerNetwork).mp independently_changing_all_three_sites_has_actual_admitted_networks.2.2.1)
  exact ⟨completed.1,completed.2.1,all_three_source_sites_leave_actual_withholding_history.2.1⟩

def replay (cut : Nat) : Opponent code :=
  if cut = 39 then EventStep.fixed (some ⟨.deliver 0,by decide⟩) else early cut

def duplicate (cut : Nat) : Opponent code := EventStep.fixed
  (if cut = 25 ∨ cut = 27 then some ⟨.deliver 2,by decide⟩
    else if cut = 29 then some ⟨.deliver 3,by decide⟩ else none)

theorem actual_replay_evidence_survives_the_generated_authentication_and_decision :
    conforms never replay = false ∧ result (finished never replay) = .decided true ∧
      (observed (finished never replay)).receipts.length = 2 ∧
      ((finished never replay).rows.all fun row => (StageTrace.audit row).all Prod.snd) = false := by
  have valid := every_actual_cut_is_source_generated never replay window
  rw [← calculated_is_the_original_producer _ valid,← cached_is_the_actual_receiver _ valid]
  decide +kernel

theorem repeated_actual_delivery_is_rejected_and_cannot_supply_another_vote :
    conforms never duplicate = false ∧ result (finished never duplicate) = .blocked .missingQuorum ∧
      (observed (finished never duplicate)).receipts.length = 1 ∧
      ((observed (finished never duplicate)).audit.any fun item =>
        decide (item.1 = 27 ∧ item.2.2 = .rejected .duplicate)) = true := by
  have valid := every_actual_cut_is_source_generated never duplicate window
  rw [← calculated_is_the_original_producer _ valid,← cached_is_the_actual_receiver _ valid]
  decide +kernel

abbrev idle := DemandTransitConsumer.idle
abbrev quiet := DemandScheduleConsumer.quiet

def inspect (stages : List (EventHistory.Stage (code := code))) (enc : StageTransport.Encoding (code := code))
    (delay threshold : Nat) := InterfaceQuorum.produce start vocabulary enc (DemandTransitSource.reception delay)
      stages 2 (RenewedQuorumSource.slot true) threshold

def withoutOrigin := (finished always latest).stages.set 30 (idle,EventStep.fixed none)
def withoutSupply := (finished always latest).stages.set 34 (idle,EventStep.fixed none)
def withoutDelivery := (finished always latest).stages.set 47 (idle,EventStep.fixed none)
def forgedEncoding : StageTransport.Encoding (code := code) :=
  fun signal => (encoding (finished always latest) signal).map fun body => {body with actor := 0}
def indefiniteStages := front ++ List.replicate window (idle,EventStep.fixed none)

theorem original_authentication_delivery_supply_and_timing_cannot_be_erased :
    inspect withoutOrigin (encoding (finished always latest)) 11 2 = .blocked .missingQuorum ∧
      inspect withoutSupply (encoding (finished always latest)) 11 2 = .blocked .missingQuorum ∧
      inspect withoutDelivery (encoding (finished always latest)) 11 2 = .blocked .missingQuorum ∧
      inspect (finished always latest).stages forgedEncoding 11 2 = .blocked .missingQuorum ∧
      inspect (finished always latest).stages (encoding (finished always latest)) 10 2 = .blocked .missingQuorum ∧
      inspect (finished always latest).stages (encoding (finished always latest)) 11 3 = .blocked .missingQuorum ∧
      inspect indefiniteStages (encoding (finished always latest)) 11 2 = .blocked .missingQuorum ∧
      result (finished always quiet) = .blocked .missingQuorum := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumControls
