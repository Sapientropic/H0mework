import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentryControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlControls
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ActualRoundNetworkSource (Network code window)
open DispatchControlSource DispatchControlConsumer

abbrev seed : State := ⟨NetworkReentryControls.first,[]⟩
def network (settings : ActualRoundNetworkSource.Settings := {})
    (admitted : (NetworkReentrySource.inspect seed.legacy true true settings).isSome) : Network :=
  (NetworkReentrySource.inspect seed.legacy true true settings).get admitted
def net := network {} (by decide +kernel)
def subject := (completion net).get (by decide +kernel)
abbrev follow : Controls := fun _ _ _ => false
abbrev pause : Controls := fun _ cut _ => decide (cut=2)
abbrev twice : Controls := fun _ cut _ => decide (cut=2 ∨ cut=4)
abbrev immediate := NetworkReentrySource.latest
abbrev delayed := ActualRoundNetworkControls.delayed
abbrev holdLast : NetworkReentrySource.Callbacks := fun net cut => if cut=5 then EventStep.fixed none else immediate net cut
abbrev ownTrace := actual net (pause net) (immediate net) (window net)
abbrev networkTrace := actual net (follow net) (delayed net) (window net)
abbrev excessive := actual net (twice net) (immediate net) (window net)
abbrev mixed := actual net (pause net) (holdLast net) (window net)
abbrev first := next seed true true {} pause immediate
abbrev blocked := next seed true true {} twice immediate

def conforms (net : Network) (control : Controller net) (callbacks : Nat → Opponent (code net)) : Bool :=
  (List.range (window net)).all fun n => let node := actual net control callbacks n
    decide (control node.cursor.cut node.state ∈ controls net node ∧ intake net node (callbacks node.cursor.cut) ∈ choices net node)
theorem conforms_iff (net : Network) (control : Controller net) (callbacks : Nat → Opponent (code net)) :
    conforms net control callbacks = true ↔ Within net control callbacks (window net) := by
  simp only [conforms,Within,List.all_eq_true,List.mem_range,decide_eq_true_eq]

theorem the_original_clock_generates_a_shared_control_capacity :
    window net = 6 ∧ limit net = 1 ∧ completion net = some subject := by
  exact ⟨by decide +kernel,by decide +kernel,(Option.some_get _).symm⟩

theorem either_local_dispatch_withholding_or_network_waiting_completes :
    Within net (pause net) (immediate net) (window net) ∧
      Within net (follow net) (delayed net) (window net) ∧
      result net ownTrace = .decided true subject ∧ result net networkTrace = .decided true subject ∧
      ownTrace.omissions = [2] ∧ networkTrace.omissions = [] ∧
      (ownTrace.rows[2]?).map (fun row => match row.call with
        | .own site none => decide (site=0) | _ => false) = some true := by
  have one := (conforms_iff net (pause net) (immediate net)).mp (by decide +kernel)
  have two := (conforms_iff net (follow net) (delayed net)).mp (by decide +kernel)
  refine ⟨one,two,computed_completion_covers_arbitrary_compliant_local_and_network_controls net subject
    the_original_clock_generates_a_shared_control_capacity.2.2 _ _ one,
    computed_completion_covers_arbitrary_compliant_local_and_network_controls net subject
    the_original_clock_generates_a_shared_control_capacity.2.2 _ _ two,?_,?_,?_⟩
  all_goals decide +kernel

theorem excessive_control_is_executed_and_records_real_blockage :
    excessive.omissions = [2,4] ∧ conforms net (twice net) (immediate net) = false ∧
      result net excessive = .blocked .missingQuorum ∧
      spent net mixed = 2 ∧ conforms net (pause net) (holdLast net) = false ∧
      result net mixed = .blocked .missingQuorum := by and_intros <;> decide +kernel

theorem controlled_reentry_keeps_the_old_evidence_and_actual_debt :
    first.legacy.evidence = seed.legacy.evidence ∧ first.evidence.length = 1 ∧
      (NetworkReentrySource.current first.legacy).claims () 1 2 = 5 ∧
      (NetworkReentrySource.current blocked.legacy).claims () 1 2 = 5 ∧
      blocked.evidence.length = 1 ∧ seed.legacy.evidence.length = 1 := by
  refine ⟨the_actual_next_keeps_all_legacy_attempts seed true true {} pause immediate,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel

def noTiming := network ⟨1,0,1⟩ (by decide +kernel)
def noQuorum := network ⟨1,3,2⟩ (by decide +kernel)
theorem missing_timing_or_quorum_is_not_completed : completion noTiming = none ∧ completion noQuorum = none := by
  and_intros <;> decide +kernel

abbrev arbitraryCompletion := computed_completion_covers_arbitrary_compliant_local_and_network_controls net subject
  the_original_clock_generates_a_shared_control_capacity.2.2
abbrev ownPayment := computed_completion_consumes_actual_payment_whole_ledger_and_next net subject
  the_original_clock_generates_a_shared_control_capacity.2.2 (pause net) (immediate net)
  either_local_dispatch_withholding_or_network_waiting_completes.1
abbrev arbitraryPayment := computed_completion_consumes_actual_payment_whole_ledger_and_next net subject
  the_original_clock_generates_a_shared_control_capacity.2.2
abbrev ownNative := actual_last_occurrence_consumes_its_own_native_ledger_and_next (execute net (pause net) (immediate net))
abbrev excessiveNative := actual_last_occurrence_consumes_its_own_native_ledger_and_next (execute net (twice net) (immediate net))
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlControls
