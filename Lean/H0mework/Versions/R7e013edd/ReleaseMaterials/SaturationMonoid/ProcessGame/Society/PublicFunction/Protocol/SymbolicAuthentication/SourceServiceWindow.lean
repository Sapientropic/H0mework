import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceRoster

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceServiceWindow

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := ForwardResponseClock.width model start

-- Local knowledge and funded, source-grounded pending offers persist until an actual slot.
-- A window already complete at its endpoint needs no further source offer.
def Persistent (blocks : Nat) (past : JointResponse.Stages model) : Prop :=
  ∀ block < blocks,
    ¬ JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law past ((block + 1) * width model start)) →
    ∃ worker : Fin model.source.code.sites, ∀ n < width model start,
      ¬ JointResponse.Clear model start vocabulary encoding law
        (atCut model start vocabulary encoding law past (block * width model start + n)) →
      UnifiedResponse.Clear model start vocabulary encoding law
        (atCut model start vocabulary encoding law past (block * width model start + n)) ∧
      JointResponse.queueClear model start
        (atCut model start vocabulary encoding law past (block * width model start + n)) = true ∧
      (NativeServiceStanding.offer model start
        (atCut model start vocabulary encoding law past (block * width model start + n)) worker).isSome = true

theorem the_original_roster_generates_completion_or_a_raw_service
    (past : JointResponse.Stages model) (worker : Fin model.source.code.sites)
    (full : (UnifiedRecoveryRun.run model start vocabulary encoding law (width model start) past).trace.length = width model start)
    (live : ∀ n < width model start, 0 < JointResponse.fuel model start (atCut model start vocabulary encoding law past n))
    (persistent : ∀ n < width model start,
      ¬ JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past n) →
      UnifiedResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past n) ∧
      JointResponse.queueClear model start (atCut model start vocabulary encoding law past n) = true ∧
      (NativeServiceStanding.offer model start (atCut model start vocabulary encoding law past n) worker).isSome = true) :
    JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (width model start)) ∨
    ∃ n < width model start,
      (RawNativeService.produce model start (atCut model start vocabulary encoding law past n) vocabulary encoding law).isSome = true := by
  by_cases complete : JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (width model start))
  · exact Or.inl complete
  · have unfinished : ∀ n < width model start,
        ¬ JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past n) := by
      intro n inside
      exact NativeServiceRoster.an_unclear_final_cut_has_no_clear_earlier_cut model start vocabulary encoding law
        (width model start) n past (Nat.le_of_lt inside) complete
    obtain ⟨n, inside, owned⟩ := NativeServiceRoster.clear_communication_generates_the_actual_receiver_slot
      model start vocabulary encoding law past worker (fun n hn => (persistent n hn (unfinished n hn)).1) full
    obtain ⟨communication, queue, present⟩ := persistent n inside (unfinished n inside)
    refine Or.inr ⟨n, inside, ?_⟩
    cases generated : NativeServiceStanding.offer model start (atCut model start vocabulary encoding law past n) worker with
    | none => rw [generated] at present; cases present
    | some offered =>
      exact NativeServiceStanding.an_actual_offer_at_its_generated_owner_slot_produces_raw_admission
        model start (atCut model start vocabulary encoding law past n) worker vocabulary encoding law
        offered (unfinished n inside) communication queue (live n inside) owned

theorem persistent_source_material_regenerates_every_unfinished_raw_window
    (blocks : Nat) (past : JointResponse.Stages model)
    (reserve : (blocks * width model start) * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (persistent : Persistent model start vocabulary encoding law blocks past)
    (full : (UnifiedRecoveryRun.run model start vocabulary encoding law (blocks * width model start) past).trace.length = blocks * width model start)
    (unfinished : ¬ JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law past (blocks * width model start))) :
    RawServiceWindow.Available model start vocabulary encoding law blocks (width model start) past := by
  intro block inside windowFull
  let first := block * width model start
  let begin := atCut model start vocabulary encoding law past first
  have endInside : (block + 1) * width model start ≤ blocks * width model start := Nat.mul_le_mul_right _ (by omega)
  have endOpen := NativeServiceRoster.an_unclear_final_cut_has_no_clear_earlier_cut model start vocabulary encoding law
    (blocks * width model start) ((block + 1) * width model start) past endInside unfinished
  obtain ⟨worker, supported⟩ := persistent block inside endOpen
  have same (n : Nat) : atCut model start vocabulary encoding law begin n =
      atCut model start vocabulary encoding law past (first + n) :=
    (UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law first n past).symm
  have initialFull := UnifiedRunPrefix.every_prefix_of_a_full_actual_trace_is_full model start vocabulary encoding law
    (blocks * width model start) first past (Nat.mul_le_mul_right _ (by omega)) full
  have lengths := UnifiedRunPrefix.actual_trace_lengths_compose model start vocabulary encoding law first (width model start) past
  have endEq : first + width model start = (block + 1) * width model start := by
    simp only [first, Nat.add_mul, Nat.one_mul]
  change (UnifiedRecoveryRun.run model start vocabulary encoding law ((block + 1) * width model start) past).trace.length =
    (block + 1) * width model start at windowFull
  rw [endEq, windowFull, initialFull] at lengths
  change (block + 1) * width model start = first +
    (UnifiedRecoveryRun.run model start vocabulary encoding law (width model start) begin).trace.length at lengths
  have generated := the_original_roster_generates_completion_or_a_raw_service model start vocabulary encoding law begin worker
    (by change _ = _ at lengths; omega)
    (by
      intro n hn
      rw [same]
      have index : first + n ≤ blocks * width model start := by dsimp only [first] at endEq ⊢; omega
      have bounded := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) index
      apply UnifiedRunCost.a_source_reserve_keeps_every_actual_prefix_live model start vocabulary encoding law
      omega)
    (by
      intro n hn currentOpen
      rw [same] at currentOpen ⊢
      exact supported n hn currentOpen)
  rcases generated with complete | raw
  · rw [same, endEq] at complete
    exact False.elim (endOpen complete)
  · obtain ⟨n, hn, admitted⟩ := raw
    refine ⟨n, hn, ?_⟩
    rw [same] at admitted
    exact admitted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceServiceWindow
