import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeThread

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService.Response
open ResponsibilityLifecycle Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (originInputs inputs : List (RawEvent Party Good Port Technology Instrument))

def actual (word : RawEvent Party Good Port Technology Instrument) :=
  OutstandingSource.History.actualExecution source (inputs ++ [word]) (inputs.length+1)

theorem actual_word_and_cut (word : RawEvent Party Good Port Technology Instrument) :
    (actual source inputs word).submitted = word ∧
    (actual source inputs word).before = OutstandingSource.History.currentAt source inputs (inputs.length+2) := by
  constructor
  · exact OutstandingSource.History.scheduled_input_is_actual source (inputs ++ [word]) inputs.length (by simp)
      |>.trans (by simp)
  · change OutstandingSource.History.currentAt source (inputs ++ [word]) (inputs.length+2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1,
      OutstandingSource.History.extending_inputs_preserves_its_executed_prefix source inputs [word] _ (le_refl _)]
    exact (OutstandingSource.History.actual_frame source inputs _).1.symm

def event (index : source.Slot) (word : RawEvent Party Good Port Technology Instrument) : Event source originInputs :=
  ⟨index,inputs.length+2,some (.periods (inputs ++ [word]))⟩

def visit (index : source.Slot) (word : RawEvent Party Good Port Technology Instrument) :
    VisitReceipt source originInputs (event source originInputs inputs index word) :=
  visitReceiptAt source originInputs index (inputs.length+1) (some (inputs ++ [word]))

def image (index : source.Slot) (word : RawEvent Party Good Port Technology Instrument) : LifecycleEvent (V source originInputs) :=
  if paid : ActualSlotPaid source (inputs ++ [word]) (inputs.length+2) index then
    .terminal 0 (obligation source originInputs index) (event source originInputs inputs index word)
      (.fulfilled ⟨rfl,rfl,visit source originInputs inputs index word,paid⟩)
  else .carried 0 (obligation source originInputs index) (event source originInputs inputs index word)
    (.maintained ⟨rfl,rfl,visit source originInputs inputs index word,paid⟩)

theorem appended_payment_is_the_same_actual_service (index : source.Slot)
    (word : RawEvent Party Good Port Technology Instrument) :
    ActualSlotPaid source (inputs ++ [word]) (inputs.length+2) index ↔
      source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index := Iff.rfl

inductive Blocker (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : source.Slot) : Type
  | early (before_window : before.clock < source.seed.task.earliest)
  | late (after_window : source.seed.task.deadline < (source.seed.law.next before word).clock)
  | missingUse (nonempty : (source.seed.slot index).goods ≠ [])
      (unpaid : ∀ item ∈ source.seed.law.rawItems before word,
        Necessity.UseMatches item.request.operation (source.seed.slot index).bearer
          (source.seed.slot index).goods (source.seed.slot index).purpose →
        ¬ source.seed.law.Valid item.before item.request)

def blocker (index : source.Slot) (word : RawEvent Party Good Port Technology Instrument)
    (unpaid : ¬ source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index) :
    Blocker source (actual source inputs word).before (actual source inputs word).submitted index := by
  by_cases early : (actual source inputs word).before.clock < source.seed.task.earliest
  · exact .early early
  by_cases late : source.seed.task.deadline <
      (source.seed.law.next (actual source inputs word).before (actual source inputs word).submitted).clock
  · exact .late late
  have absent : ¬ Necessity.BundlePaid source.seed.law (actual source inputs word).before
      (actual source inputs word).submitted (source.seed.slot index).bearer
      (source.seed.slot index).goods (source.seed.slot index).purpose := by
    intro paid
    exact unpaid ⟨le_of_not_gt early,le_of_not_gt late,paid⟩
  refine .missingUse (fun empty => absent (Or.inl empty)) ?_
  intro item member matched accepted
  exact absent (Or.inr ⟨item,member,accepted,matched⟩)

variable {originInputs inputs}
theorem advance_history {index : source.Slot} (thread : Thread source originInputs index inputs)
    (live : thread.state.current.LiveAt 0) (word : RawEvent Party Good Port Technology Instrument) :
    (thread.advance source word).state.current.history = thread.state.current.history ++
      [image source originInputs inputs index word] := by
  rcases thread with ⟨state,shape⟩
  cases shape with
  | live unpaid slots =>
    by_cases paid : ActualSlotPaid source (inputs ++ [word]) (inputs.length+2) index
    · simp only [Thread.advance,dif_pos paid,image]
      simp only [NativeResponsibilityProcess.GeneratedState.step,NativeResponsibilityProcess.Edge.target]
      congr 2
      unfold NativeResponsibilityProcess.Edge.lifecycleEvent
      dsimp only
      conv_lhs =>
        arg 3
        change (show BoundaryDisposition (V source originInputs) (obligation source originInputs index) (event source originInputs inputs index word) from if payment : ActualSlotPaid source (inputs ++ [word]) (inputs.length+2) index then
          BoundaryDisposition.terminal (.final (.fulfilled ⟨rfl,rfl,visit source originInputs inputs index word,payment⟩))
          else .carry (.maintained ⟨rfl,rfl,visit source originInputs inputs index word,payment⟩))
        rw [dif_pos paid]
      rfl
    · simp only [Thread.advance,dif_neg paid,image]
      simp only [NativeResponsibilityProcess.GeneratedState.step,NativeResponsibilityProcess.Edge.target]
      congr 2
      unfold NativeResponsibilityProcess.Edge.lifecycleEvent
      dsimp only
      conv_lhs =>
        arg 3
        change (show BoundaryDisposition (V source originInputs) (obligation source originInputs index) (event source originInputs inputs index word) from if payment : ActualSlotPaid source (inputs ++ [word]) (inputs.length+2) index then
          BoundaryDisposition.terminal (.final (.fulfilled ⟨rfl,rfl,visit source originInputs inputs index word,payment⟩))
          else .carry (.maintained ⟨rfl,rfl,visit source originInputs inputs index word,payment⟩))
        rw [dif_neg paid]
      rfl
  | terminal archive paid recorded original slots =>
    obtain ⟨obligation,present⟩ := live
    simp only [slots,List.getElem?_cons_zero] at present
    cases present


theorem live_is_in_the_original_pending_task {index : source.Slot}
    (thread : Thread source originInputs index inputs) (live : thread.state.current.LiveAt 0) :
    source.seed.slot index ∈ source.pendingSlots (frameAt source inputs (inputs.length+2)).payments :=
  source.pending_slot_has_original_identity _ index (thread.native_live_iff_unpaid source |>.mp live)

theorem payment_generates_native_terminal {index : source.Slot}
    (thread : Thread source originInputs index inputs) (live : thread.state.current.LiveAt 0)
    (word : RawEvent Party Good Port Technology Instrument)
    (paid : source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index) :
    (thread.advance source word).state.current.TerminalAt 0 := by
  apply (thread.advance source word).native_terminal_iff_recorded source |>.mpr
  have prior : (frameAt source (inputs ++ [word]) (inputs.length+2)).payments index = none := by
    have same := common_payments source (inputs := inputs) word
    dsimp only [appended] at same
    rw [same]
    exact thread.native_live_iff_unpaid source |>.mp live
  have next := next_paid source (inputs ++ [word]) index (inputs.length+2) prior
    ((appended_payment_is_the_same_actual_service source inputs index word).mpr paid)
  exact ⟨inputs.length+2,by simpa only [appended,List.length_append,List.length_singleton,Nat.add_assoc] using next⟩

theorem unpaid_preserves_native_live {index : source.Slot}
    (thread : Thread source originInputs index inputs) (live : thread.state.current.LiveAt 0)
    (word : RawEvent Party Good Port Technology Instrument)
    (unpaid : ¬ source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index) :
    (thread.advance source word).state.current.LiveAt 0 := by
  apply (thread.advance source word).native_live_iff_unpaid source |>.mpr
  have prior : (frameAt source (inputs ++ [word]) (inputs.length+2)).payments index = none := by
    have same := common_payments source (inputs := inputs) word
    dsimp only [appended] at same
    rw [same]
    exact thread.native_live_iff_unpaid source |>.mp live
  have next := next_unpaid source (inputs ++ [word]) index (inputs.length+2) prior
    (fun paid => unpaid ((appended_payment_is_the_same_actual_service source inputs index word).mp paid))
  simpa only [appended,List.length_append,List.length_singleton,Nat.add_assoc] using next

inductive Disposition {index : source.Slot} (thread : Thread source originInputs index inputs)
    (word : RawEvent Party Good Port Technology Instrument) : Type where
  | private archived (archive : TerminalArchive (V source originInputs))
      (original : thread.state.current.slots = [.terminal archive])
      (unchanged : (thread.advance source word).state = thread.state)
  | private fulfilled (pending : thread.state.current.LiveAt 0)
      (payment : source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index)
      (terminal : (thread.advance source word).state.current.TerminalAt 0)
      (history : (thread.advance source word).state.current.history = thread.state.current.history ++
        [image source originInputs inputs index word])
  | private retained (pending : thread.state.current.LiveAt 0)
      (unpaid : ¬ source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index)
      (reason : Blocker source (actual source inputs word).before (actual source inputs word).submitted index)
      (live : (thread.advance source word).state.current.LiveAt 0)
      (history : (thread.advance source word).state.current.history = thread.state.current.history ++
        [image source originInputs inputs index word])

def produce {index : source.Slot} (thread : Thread source originInputs index inputs)
    (word : RawEvent Party Good Port Technology Instrument) : Disposition source thread word := by
  cases thread.shape with
  | terminal archive paid recorded original slots =>
    exact .archived archive slots (thread.terminal_state_is_preserved source ⟨archive,by simp [slots]⟩ word)
  | live unpaid slots =>
    have live : thread.state.current.LiveAt 0 := ⟨obligation source originInputs index,by simp [slots]⟩
    if paid : source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index then
      exact .fulfilled live paid (payment_generates_native_terminal source thread live word paid)
        (advance_history source thread live word)
    else
      exact .retained live paid (blocker source inputs index word paid)
        (unpaid_preserves_native_live source thread live word paid) (advance_history source thread live word)

inductive Kind where
  | archived | fulfilled | retained
  deriving DecidableEq, Repr

def Disposition.kind {index : source.Slot} {thread : Thread source originInputs index inputs}
    {word : RawEvent Party Good Port Technology Instrument} : Disposition source thread word → Kind
  | .archived .. => .archived
  | .fulfilled .. => .fulfilled
  | .retained .. => .retained


theorem live_paid_or_typed_blocker {index : source.Slot}
    (thread : Thread source originInputs index inputs) (live : thread.state.current.LiveAt 0)
    (word : RawEvent Party Good Port Technology Instrument) :
    (source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index ∧
      (thread.advance source word).state.current.TerminalAt 0 ∧
      (image source originInputs inputs index word).kind = .obligationTerminal) ∨
    (¬ source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index ∧
      Nonempty (Blocker source (actual source inputs word).before (actual source inputs word).submitted index) ∧
      (thread.advance source word).state.current.LiveAt 0 ∧
      (image source originInputs inputs index word).kind = .maintained) := by
  by_cases paid : source.SlotPaid (actual source inputs word).before (actual source inputs word).submitted index
  · refine Or.inl ⟨paid,payment_generates_native_terminal source thread live word paid,?_⟩
    rw [image,dif_pos ((appended_payment_is_the_same_actual_service source inputs index word).mpr paid)]
    rfl
  · refine Or.inr ⟨paid,⟨blocker source inputs index word paid⟩,
      unpaid_preserves_native_live source thread live word paid,?_⟩
    rw [image,dif_neg (fun payment => paid ((appended_payment_is_the_same_actual_service source inputs index word).mp payment))]
    rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService.Response
