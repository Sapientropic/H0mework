import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Rule
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Distributed.Recall.Information.Agency.Protocol.Continuation.Whole
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

def clock (point : Cursor code) (ordinal : Nat) :=
  Distributed.Recall.Information.Agency.ownerAt code point.ownerStart
    ((Residual.seed point.source point.entry point.cut).history.length+ordinal)

def owners (domain : List (Cursor code)) (ordinal : Nat) : List (Fin code.sites) :=
  domain.filterMap (fun point => clock point ordinal)

def projected (domain : List (Cursor code)) (original : Rule code) (programme : Program code fuel)
    (frozen ordinal : Nat) : Rule code :=
  if ordinal < frozen then programme.at original ordinal
  else focus code (owners domain ordinal) (programme.at original ordinal)

/-- The paid prefix stays literal; only future rows outside every source clock are erased. -/
def normalize (domain : List (Cursor code)) (original : Rule code) (programme : Program code fuel)
    (frozen : Nat) : Program code (Continuation.Whole.Complete.horizon domain) :=
  ⟨(List.range (Continuation.Whole.Complete.horizon domain)).map (projected domain original programme frozen),by simp⟩

theorem each_normalized_stage_is_source_generated (domain : List (Cursor code))
    (original : Rule code) (programme : Program code fuel) (frozen ordinal : Nat)
    (inside : ordinal < Continuation.Whole.Complete.horizon domain) :
    (normalize domain original programme frozen).at original ordinal = projected domain original programme frozen ordinal := by
  simp only [normalize,Program.at,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem run_history_length (schedule : Residual.Schedule code) (input : Input code)
    (seed : State code) (count : Nat) :
    (Residual.run code schedule input seed count).history.length = seed.history.length+count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Residual.run,history_keeps_every_actual_word]
      simp only [List.length_append,List.length_singleton,ih]
      omega

private theorem seed_history_length (point : Cursor code) :
    (Residual.seed point.source point.entry point.cut).history.length = point.history.length+1+point.cut := by
  have size (count : Nat) : (point.source.feedbackState point.entry count).history.length = point.history.length+1+count := by
    induction count with
    | zero => simp only [Machine.feedbackState,Machine.feedbackInitial,List.length_append,List.length_singleton,Nat.add_zero]
    | succ count ih =>
        change (Feedback.advance code _ _ _).history.length = _
        rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
        omega
  exact size point.cut

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem advance_reads_its_actual_decision (policy : Option code.Policy)
    (first second : Input code) (state : State code)
    (same : first.opponent state.history state.past state.frame = second.opponent state.history state.past state.frame) :
    Feedback.advance code policy first state = Feedback.advance code policy second state := by
  simp only [Feedback.advance,Feedback.word,Feedback.decision,same]

theorem the_source_generated_projection_keeps_every_actual_state
    (domain : List (Cursor code)) (point : Cursor code) (member : point ∈ domain)
    (original : Rule code) (programme : Program code fuel) (frozen : Nat)
    (rival : Opponent code) (count : Nat) :
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point original (normalize domain original programme frozen)).val)
      ⟨controller point original (normalize domain original programme frozen) rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) count =
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point original programme).val)
      ⟨controller point original programme rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [Residual.run] at ih ⊢
      rw [ih]
      let actual := Residual.run code (Residual.scheduleAt point.source point.cut (schedule point original programme).val)
        ⟨controller point original programme rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) count
      change Feedback.advance code _ _ actual = Feedback.advance code _ _ actual
      by_cases stopped : actual.remaining = 0
      · cases (Residual.scheduleAt point.source point.cut (schedule point original (normalize domain original programme frozen)).val count) <;>
          cases (Residual.scheduleAt point.source point.cut (schedule point original programme).val count) <;>
          simp only [Feedback.advance,Feedback.word,Feedback.decision,stopped,if_pos]
      · have remaining := Residual.remaining_is_the_seed_budget code
          (Residual.scheduleAt point.source point.cut (schedule point original programme).val)
          ⟨controller point original programme rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) count
        change actual.remaining = (Residual.seed point.source point.entry point.cut).remaining-count at remaining
        have inside : count < Cut.horizon point.source point.entry point.cut := by
          change count < (Residual.seed point.source point.entry point.cut).remaining
          omega
        have publicRoom : count < Continuation.Whole.Complete.horizon domain := inside.trans_le (Continuation.Whole.Complete.each_remaining_horizon_is_generated domain point member)
        have size : actual.history.length = point.history.length+1+point.cut+count := by
          exact (run_history_length _ _ _ count).trans (by rw [seed_history_length])
        have ordinal : actual.history.length-(point.history.length+1+point.cut) = count := by rw [size];omega
        have policy (program : Program code (Continuation.Whole.Complete.horizon domain)) :
            Residual.scheduleAt point.source point.cut (schedule point original program).val count = some (program.at original count).work.val := by
          simp only [Residual.scheduleAt,schedule,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]
        have oldPolicy : Residual.scheduleAt point.source point.cut (schedule point original programme).val count = some (programme.at original count).work.val := by
          simp only [Residual.scheduleAt,schedule,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]
        rw [policy,oldPolicy,each_normalized_stage_is_source_generated domain original programme frozen count publicRoom]
        have newInput : Feedback.advance code (some (projected domain original programme frozen count).work.val)
            ⟨controller point original (normalize domain original programme frozen) rival,point.entry.budget⟩ actual =
            Feedback.advance code (some (projected domain original programme frozen count).work.val)
              ⟨driver code point.ownerStart (projected domain original programme frozen count) rival,point.entry.budget⟩ actual := by
          apply advance_reads_its_actual_decision
          simp only [Continuation.Whole.controller,ordinal,each_normalized_stage_is_source_generated domain original programme frozen count publicRoom]
        have oldInput : Feedback.advance code (some (programme.at original count).work.val)
            ⟨controller point original programme rival,point.entry.budget⟩ actual =
            Feedback.advance code (some (programme.at original count).work.val)
              ⟨driver code point.ownerStart (programme.at original count) rival,point.entry.budget⟩ actual := by
          apply advance_reads_its_actual_decision
          simp only [Continuation.Whole.controller,ordinal]
        rw [newInput,oldInput]
        unfold projected
        split
        · rfl
        · apply the_focused_rule_generates_the_same_actual_next
          intro site owned
          apply List.mem_filterMap.mpr
          refine ⟨point,member,?_⟩
          unfold clock
          rw [seed_history_length]
          rw [size] at owned
          exact owned

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
