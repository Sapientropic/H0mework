import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenControlSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkDomain

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenControlDomain
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open FinancedNetworkSource (code start window)
open OpenControlSource

abbrev Related := ControlledPaymentDomain.Related

abbrev related_states := ControlledPaymentDomain.related_states
abbrev related_owners := ControlledPaymentDomain.related_owners
abbrev related_opportunities := ControlledPaymentDomain.related_opportunities
theorem related_protocols (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) (requested : Bool) :
    protocol left requested = protocol right requested := by
  simp only [protocol,withhold,related_opportunities left right one two same]
  rfl
theorem related_choices (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    choices left = choices right := by
  rw [choices_are_the_original_source_envelope left one,choices_are_the_original_source_envelope right two]
  have equal : allowance left = allowance right := by simp only [allowance,related_states left right one two same]
  rw [equal]
  exact EnvelopeObservation.choices_equal start _ _ same.1 (allowance right)

def normalized (node : Node) (requested : Bool) : Bool :=
  if opportunity node then requested else false

theorem normalized_is_generated (node : Node) (requested : Bool) : normalized node requested ∈ controls node := by
  unfold normalized controls
  split <;> cases requested <;> simp_all

theorem normalization_preserves_protocol (node : Node) (requested : Bool) : protocol node (normalized node requested) = protocol node requested := by
  have hold : withhold node (normalized node requested) = withhold node requested := by
    unfold normalized withhold
    split <;> simp_all
  simp only [protocol,hold]

def chosen (left right : Node) (rival : Opponent code) : Move code := FinancedNetworkDomain.chosen left.toNode right.toNode rival

theorem compact_step (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right)
    (requested : Bool) (rival : Opponent code) :
    Related (step left (normalized left requested) (EventStep.fixed (chosen left right rival))) (step right requested rival) := by
  have protocols := (normalization_preserves_protocol left requested).trans (related_protocols left right one two same requested)
  have hold : withhold left (normalized left requested) = withhold right requested := by
    have norm : withhold left (normalized left requested) = withhold left requested := by
      unfold withhold normalized
      split <;> simp_all
    rw [norm]
    simp only [withhold,related_opportunities left right one two same]
  refine ⟨?_,?_⟩
  · change EnvelopeObservation.Compatible start
      (left.stages ++ [(protocol left (normalized left requested),EventStep.fixed (chosen left right rival))])
      (right.stages ++ [(protocol right requested,rival)])
    rw [← protocols]
    exact EnvelopeObservation.compact_extension start _ _ same.1 _ rival
  · change (if withhold left (normalized left requested) then left.omissions ++ [(left.cursor.cut,(owner left).getD 0)] else left.omissions) =
      (if withhold right requested then right.omissions ++ [(right.cursor.cut,(owner right).getD 0)] else right.omissions)
    have cuts : left.cursor.cut = right.cursor.cut := by rw [one.1,two.1];exact same.1.1.cut
    have owners : owner left = owner right := related_owners left right one two same
    rw [hold,same.2,cuts,owners]

theorem every_actual_joint_controller_has_a_generated_source_branch
    (control : Controller) (rivals : Nat → Opponent code) (count : Nat) (within : Within control rivals count) :
    ∃ node ∈ generate count, Related node (actual control rivals count) := by
  induction count with
  | zero => exact ⟨initial,List.mem_singleton_self _,⟨EventStep.matches_self _,EnvelopeObservation.reflexive _⟩,rfl⟩
  | succ count ih =>
    obtain ⟨node,member,same⟩ := ih (fun index bounded => within index (by omega))
    have one := generated_valid count node member
    have two := actual_valid control rivals count
    let right := actual control rivals count
    let requested := control right.cursor.cut right.state
    let rival := rivals right.cursor.cut
    let move := chosen node right rival
    have allowed : move ∈ choices node := by
      change FinancedNetworkDomain.chosen node.toNode right.toNode rival ∈ choices node
      rw [related_choices node right one two same,
        FinancedNetworkDomain.chosen_is_actual node.toNode right.toNode two same.1]
      exact within count (by omega)
    exact ⟨step node (normalized node requested) (EventStep.fixed move),
      List.mem_flatMap.mpr ⟨node,member,List.mem_flatMap.mpr ⟨normalized node requested,normalized_is_generated node requested,
        List.mem_map.mpr ⟨move,allowed,rfl⟩⟩⟩,compact_step node right one two same requested rival⟩

abbrev related_rows := ControlledPaymentDomain.related_rows
abbrev related_results := ControlledPaymentDomain.related_results
abbrev related_original_subjects := ControlledPaymentDomain.related_original_subjects

theorem related_checks (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    ControlledPaymentConsumer.check left = ControlledPaymentConsumer.check right := by
  have states := related_states left right one two same
  have audits : (left.rows.all fun row => (StageTrace.audit row).all Prod.snd) =
      (right.rows.all fun row => (StageTrace.audit row).all Prod.snd) := by
    have rows := related_rows left right one two same
    generalize left.rows = a at rows ⊢
    generalize right.rows = b at rows ⊢
    induction rows with
    | nil => rfl
    | @cons a b _ _ head tail ih =>
      have audit : StageTrace.audit a = StageTrace.audit b := by simp only [StageTrace.audit,StageTrace.items,head.before,head.submitted]
      simp only [List.all_cons,audit,ih]
  unfold ControlledPaymentConsumer.check
  rw [ControlledPaymentDomain.related_original_subjects left right one two same,
    ControlledPaymentDomain.related_results left right one two same,audits,states]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenControlDomain
