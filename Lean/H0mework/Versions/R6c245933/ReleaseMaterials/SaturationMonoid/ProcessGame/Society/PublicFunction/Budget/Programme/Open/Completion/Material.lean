import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Flows

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def creditless (request : Request Party Good Port Technology Instrument) : Bool := match request.operation with
  | .produce _ | .transfer _ _ _ | .settle _ _ _ _ => false
  | _ => true

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem creditless_is_the_original_credit
    (law : RawLaw Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (known : creditless request = true)
    (current : RawCurrent Party Good Technology Instrument) : law.credit current request = [] := by
  cases operation : request.operation <;> simp_all [creditless,RawLaw.credit]

def noSupply (code : Code Party Good Port Technology Instrument) : Bool :=
  code.actions.all creditless && code.eventAlphabet.all (fun event => match event with
    | .adversary request => creditless request | _ => true) &&
  (List.finRange code.sites).all (fun sender => (List.finRange code.sites).all fun recipient =>
    (code.sendCost sender recipient).all creditless) &&
  (List.finRange code.sites).all (fun recipient => (code.deliveryCost recipient).all creditless)

variable (code : Code Party Good Port Technology Instrument)

private theorem no_supply_action (checked : noSupply code = true) (policy : code.Policy)
    (supported : Normalization.Supported code policy) (site : Fin code.sites) (signal : Fin code.signals) :
    ∀ request ∈ code.action policy site signal, creditless request = true := by
  intro request inside
  have actions := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1).1
  have present : request ∈ code.actions := by
    unfold Code.action at inside
    split at inside
    · exact supported _ _ request inside
    · simp only [List.not_mem_nil] at inside
  exact (List.all_eq_true.mp actions) request present

private theorem no_supply_step (checked : noSupply code = true) (policy : code.Policy)
    (supported : Normalization.Supported code policy) (state : State code) (event : Choice code) :
    ∀ request ∈ (stepLocal code policy state event.val).word,creditless request = true := by
  obtain ⟨sender,delivery⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨earlier,sends⟩ := Bool.and_eq_true_iff.mp sender
  obtain ⟨actions,events⟩ := Bool.and_eq_true_iff.mp earlier
  rcases event with ⟨event,original⟩
  cases event with
  | adversary action =>
    intro request inside
    have same : request = action := List.mem_singleton.mp inside
    subst request
    exact (List.all_eq_true.mp events) _ original
  | send sender recipient =>
    exact List.all_eq_true.mp ((List.all_eq_true.mp ((List.all_eq_true.mp sends) sender (List.mem_finRange _))) recipient (List.mem_finRange _))
  | deliver address =>
    simp only [stepLocal,Code.step]
    cases packet : state.frame.sent[address]? with
    | none => simp
    | some message =>
      simp only []
      exact List.all_eq_true.mp ((List.all_eq_true.mp delivery) message.recipient (List.mem_finRange _))
  | activate site => exact no_supply_action code checked policy supported site _

theorem each_actual_word_has_no_material_supply (checked : noSupply code = true)
    (policy : Option code.Policy) (supported : ∀ raw,policy = some raw → Normalization.Supported code raw)
    (input : Input code) (state : State code) :
    ∀ request ∈ word code policy input state,creditless request = true := by
  cases policy with
  | none => simp [word]
  | some policy =>
    cases chosen : decision code input state with
    | none => simp [word,chosen]
    | some event => simpa only [word,chosen] using no_supply_step code checked policy (supported _ rfl) state event

theorem creditless_word_pays_no_credit (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (known : ∀ request ∈ word,creditless request = true) (party : Party) (good : Good) :
    law.totalCredit (law.rawItems current word) party good = 0 := by
  apply List.sum_eq_zero
  intro amount inside
  obtain ⟨item,present,rfl⟩ := List.mem_map.mp inside
  have requests := law.inventory_requests_exact current 0 word
  have request : item.request ∈ word := requests ▸ List.mem_map.mpr ⟨item,present,rfl⟩
  have absent := creditless_is_the_original_credit law item.request (known _ request) item.before
  unfold RawLaw.actualCredit
  split <;> simp only [absent,flowAt,amount,List.map_nil,List.sum_nil]

theorem a_creditless_actual_word_cannot_increase_stock
    (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (known : ∀ request ∈ word,creditless request = true) (party : Party) (good : Good) :
    (law.next current word).stock party good ≤ current.stock party good := by
  have balance := law.actual_next_material_balance current word party good
  rw [creditless_word_pays_no_credit law current word known party good,add_zero] at balance
  have nonnegative : 0 ≤ law.totalDebit (law.rawItems current word) party good :=
    Institutions.Capitalism.Universal.Source.Material.total_nonnegative _ _
    (fun item _ => Institutions.Capitalism.Universal.Source.Material.paid_nonnegative law item party good)
  linarith

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion
