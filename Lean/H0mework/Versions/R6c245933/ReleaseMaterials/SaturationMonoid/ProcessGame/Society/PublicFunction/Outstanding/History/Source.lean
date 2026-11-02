import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.Reachable

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (inputs : List (RawEvent Party Good Port Technology Instrument))

/-- Finite primitive input, executed after the original request. No state,
payment, admission, successful response or future endpoint is supplied. -/
def report (ordinal : Nat) (frame : source.Frame) :
    ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument :=
  if ordinal = 1 then .original frame.raw source.seed.original
  else match inputs[ordinal - 2]? with
    | some word => .original frame.raw word
    | none => (source.decideAt frame.raw frame.payments).report

def word (ordinal : Nat) (frame : source.Frame) : RawEvent Party Good Port Technology Instrument :=
  if ordinal = 0 then [] else (report source inputs ordinal frame).word

def trailAt : Nat → ExecutionPrefix source
  | 0 => .start
  | ordinal + 1 => (trailAt ordinal).append (word source inputs ordinal (trailAt ordinal).frame)

theorem length_exact (ordinal : Nat) : (trailAt source inputs ordinal).length = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem round_exact (ordinal : Nat) :
    (trailAt source inputs ordinal).frame.raw.round = source.seed.initial.round + ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      change (trailAt source inputs ordinal).frame.raw.round + 1 = _
      rw [ih]
      rfl

/-- Cache the full raw/payment frame at every actual ordinal. No prefix is
replayed twice to read its raw state and payment archive. -/
def advanceFrame (ordinal : Nat) (before : source.Frame) : source.Frame :=
  let emitted := word source inputs ordinal before
  ⟨source.seed.law.next before.raw emitted,
    source.update before.payments before.raw emitted ordinal⟩

def foldedFrameAt (visit : Nat) : source.Frame :=
  (List.range visit).foldl (fun before ordinal => advanceFrame source inputs ordinal before)
    ⟨source.seed.initial,fun _ => none⟩

theorem foldedFrameAt_is_the_complete_original_frame (visit : Nat) :
    foldedFrameAt source inputs visit = (trailAt source inputs visit).frame := by
  induction visit with
  | zero => rfl
  | succ visit ih =>
      unfold foldedFrameAt at *
      rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
      change (⟨_,source.update _ _ _ visit⟩ : source.Frame) =
        (⟨_,source.update _ _ _ (trailAt source inputs visit).length⟩ : source.Frame)
      rw [length_exact]

def ordinal (current : RawCurrent Party Good Technology Instrument) : Nat :=
  current.round - source.seed.initial.round

@[reducible] private def originalPaymentsAt (visit : Nat) :=
  (trailAt source inputs visit).frame.payments

def computedPaymentsAt (visit : Nat) := (foldedFrameAt source inputs visit).payments

@[csimp] private theorem originalPaymentsAt_codegen : @originalPaymentsAt = @computedPaymentsAt := by
  funext Party Good Port Technology Instrument decParty decGood decInstrument source inputs visit
  exact (congrArg (fun frame => frame.payments)
    (foldedFrameAt_is_the_complete_original_frame source inputs visit)).symm

def reportAt (current : RawCurrent Party Good Technology Instrument) :=
  report source inputs (ordinal source current)
    ⟨current, originalPaymentsAt source inputs (ordinal source current)⟩

def input : ProgrammeSource.Input Party Good Port Technology Instrument where
  law := source.seed.law
  initial := source.seed.initial
  instructions := source.seed.original
  emission? := some (fun current => (reportAt source inputs current).word)
  localAttempts := source.seed.actionsAt
  observedEmission? := some {
    generate := reportAt source inputs
    word := ProgrammeSource.ProgrammeReport.word }

@[reducible] private def rootCurrentAt (visit : Nat) :=
  ProgrammeSource.rawCurrent (input source inputs) (ProgrammeHistory.visitAt (input source inputs) visit).current

private theorem root_ordinal_exact (visit : Nat) : ordinal source (rootCurrentAt source inputs visit) = visit := by
  unfold ordinal rootCurrentAt
  rw [ProgrammeHistory.visit_round]
  exact Nat.add_sub_cancel_left _ _

/-- Every supplied word is interpreted by this input's own original root;
the suffix is recomputed from this history's current and payment archive. -/
private theorem root_actual_frame (visit : Nat) :
    rootCurrentAt source inputs visit = (trailAt source inputs visit).frame.raw ∧
    ProgrammeSource.rawEvent (input source inputs)
      (ProgrammeHistory.visitAt (input source inputs) visit).current =
        word source inputs visit (trailAt source inputs visit).frame := by
  induction visit with
  | zero => exact ⟨rfl, rfl⟩
  | succ visit ih =>
      have raw : rootCurrentAt source inputs (visit + 1) = (trailAt source inputs (visit + 1)).frame.raw := by
        change ProgrammeSource.rawCurrent (input source inputs)
          (ProgrammeSource.next (input source inputs)
            (ProgrammeHistory.visitAt (input source inputs) visit).current) = _
        rw [ProgrammeSource.actual_raw_next]
        change source.seed.law.next (rootCurrentAt source inputs visit) _ = _
        rw [ih.1, ih.2]
        rfl
      refine ⟨raw, ?_⟩
      have emitted : ProgrammeSource.rawEvent (input source inputs)
          (ProgrammeHistory.visitAt (input source inputs) (visit + 1)).current =
          (reportAt source inputs (rootCurrentAt source inputs (visit + 1))).word := by
        change ProgrammeSource.rawEvent (input source inputs)
          (ProgrammeSource.next (input source inputs)
            (ProgrammeHistory.visitAt (input source inputs) visit).current) =
          (reportAt source inputs (ProgrammeSource.rawCurrent (input source inputs)
            (ProgrammeSource.next (input source inputs)
              (ProgrammeHistory.visitAt (input source inputs) visit).current))).word
        cases (ProgrammeHistory.visitAt (input source inputs) visit).current <;> rfl
      rw [emitted]
      unfold reportAt
      rw [root_ordinal_exact, raw]
      unfold word
      rw [if_neg (by omega : visit + 1 ≠ 0)]

def computedCurrentAt (visit : Nat) := (foldedFrameAt source inputs visit).raw

@[csimp] private theorem rootCurrentAt_codegen : @rootCurrentAt = @computedCurrentAt := by
  funext Party Good Port Technology Instrument decParty decGood decInstrument source inputs visit
  exact (root_actual_frame source inputs visit).1.trans
    (congrArg (fun frame => frame.raw) (foldedFrameAt_is_the_complete_original_frame source inputs visit)).symm

def currentAt (visit : Nat) := rootCurrentAt source inputs visit

theorem ordinal_exact (visit : Nat) : ordinal source (currentAt source inputs visit) = visit :=
  root_ordinal_exact source inputs visit

/-- The compiled fold is a readout of this same original root occurrence. -/
theorem actual_frame (visit : Nat) :
    currentAt source inputs visit = (trailAt source inputs visit).frame.raw ∧
    ProgrammeSource.rawEvent (input source inputs)
      (ProgrammeHistory.visitAt (input source inputs) visit).current =
        word source inputs visit (trailAt source inputs visit).frame :=
  root_actual_frame source inputs visit

def actualExecution (depth : Nat) :=
  (ProgrammeLiving.projectionLaw (input source inputs)).project .execution
    (ProgrammeSource.emitted (input source inputs)
      (ProgrammeHistory.visitAt (input source inputs) (depth + 1)).current) ()

theorem actual_word (depth : Nat) : (actualExecution source inputs depth).submitted =
    word source inputs (depth + 1) (trailAt source inputs (depth + 1)).frame :=
  (actual_frame source inputs (depth + 1)).2

theorem original_request_is_actual : (actualExecution source inputs 0).submitted = source.seed.original := by
  rw [actual_word]
  rfl

theorem scheduled_input_is_actual (index : Nat)
    (inside : index < inputs.length) :
    (actualExecution source inputs (index + 1)).submitted = inputs[index] := by
  rw [actual_word]
  unfold word report
  rw [if_neg (by omega), if_neg (by omega)]
  have address : index + 1 + 1 - 2 = index := by omega
  rw [address, List.getElem?_eq_getElem inside]
  rfl

/-- This is the actual original bootstrap/request prefix, followed by the
given primitive words. Legality is checked at their own intermediate states. -/
def replay := inputs.foldl ExecutionPrefix.append (source.canonicalPrefix 2)

theorem finite_prefix_exact (count : Nat) (inside : count ≤ inputs.length) :
    trailAt source inputs (count + 2) =
      (inputs.take count).foldl ExecutionPrefix.append (source.canonicalPrefix 2) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have prior := ih (by omega)
      have item : count < inputs.length := by omega
      change (trailAt source inputs (count + 2)).append
        (word source inputs (count + 2) (trailAt source inputs (count + 2)).frame) = _
      have emitted : word source inputs (count + 2) (trailAt source inputs (count + 2)).frame =
          inputs[count] := by
        unfold word report
        rw [if_neg (by omega), if_neg (by omega)]
        have address : count + 2 - 2 = count := by omega
        rw [address, List.getElem?_eq_getElem item]
        rfl
      rw [emitted, prior, List.take_succ_eq_append_getElem item,
        List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem all_finite_inputs_reach_their_own_actual_current :
    currentAt source inputs (inputs.length + 2) = (replay source inputs).frame.raw ∧
    (trailAt source inputs (inputs.length + 2)).frame.payments = (replay source inputs).frame.payments := by
  have same := finite_prefix_exact source inputs inputs.length (Nat.le_refl _)
  rw [List.take_length] at same
  exact ⟨(actual_frame source inputs _).1.trans (congrArg (fun past => past.frame.raw) same),
    congrArg (fun past => past.frame.payments) same⟩

/-- Reachability starts after the source's actual refused occurrence.
Later legal words have no length or planner-alphabet restriction. -/
inductive LegalReach (source : OutstandingSource Party Good Port Technology Instrument) :
    RawCurrent Party Good Technology Instrument → Prop
  | original : LegalReach source (source.canonicalPrefix 2).frame.raw
  | next {current} (prior : LegalReach source current) (word)
      (accepted : ∀ item ∈ source.seed.law.rawItems current word,
        source.seed.law.Valid item.before item.request) : LegalReach source (source.seed.law.next current word)

theorem every_legal_reachable_state_has_its_own_actual_source (current)
    (reached : LegalReach source current) :
    ∃ inputs : List (RawEvent Party Good Port Technology Instrument),
      currentAt source inputs (inputs.length + 2) = current := by
  have represented : ∃ inputs : List (RawEvent Party Good Port Technology Instrument),
      (replay source inputs).frame.raw = current := by
    induction reached with
    | original => exact ⟨[], rfl⟩
    | next prior word accepted ih =>
        obtain ⟨inputs, same⟩ := ih
        refine ⟨inputs ++ [word], ?_⟩
        change ((inputs ++ [word]).foldl ExecutionPrefix.append (source.canonicalPrefix 2)).frame.raw = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact congrArg (fun raw => source.seed.law.next raw word) same
  obtain ⟨inputs, same⟩ := represented
  exact ⟨inputs, (all_finite_inputs_reach_their_own_actual_current source inputs).1.trans same⟩

theorem extending_inputs_preserves_its_executed_prefix
    (later : List (RawEvent Party Good Port Technology Instrument))
    (visit : Nat) (inside : visit ≤ inputs.length + 2) :
    trailAt source (inputs ++ later) visit = trailAt source inputs visit := by
  induction visit with
  | zero => rfl
  | succ visit ih =>
      have prior := ih (by omega)
      change (trailAt source (inputs ++ later) visit).append
        (word source (inputs ++ later) visit (trailAt source (inputs ++ later) visit).frame) =
        (trailAt source inputs visit).append (word source inputs visit (trailAt source inputs visit).frame)
      rw [prior]
      congr 1
      unfold word report
      by_cases bootstrap : visit = 0
      · rw [if_pos bootstrap, if_pos bootstrap]
      · rw [if_neg bootstrap, if_neg bootstrap]
        by_cases original : visit = 1
        · rw [if_pos original, if_pos original]
        · rw [if_neg original, if_neg original,
            List.getElem?_append_left (by omega : visit - 2 < inputs.length)]

theorem residual_is_actually_emitted (depth : Nat) (afterInputs : inputs.length ≤ depth) :
    (actualExecution source inputs (depth + 1)).submitted =
      (source.decideAt (currentAt source inputs (depth + 2))
        (trailAt source inputs (depth + 2)).frame.payments).word := by
  rw [actual_word]
  unfold word report
  rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by omega)]
  rw [OutstandingSource.Decision.report_word, (actual_frame source inputs (depth + 2)).1]

theorem actual_next (depth : Nat) :
    (actualExecution source inputs depth).after = currentAt source inputs (depth + 2) :=
  (actualExecution source inputs depth).root_next_exact

theorem actual_payment_update (depth : Nat) :
    (trailAt source inputs (depth + 2)).frame.payments =
      source.update (trailAt source inputs (depth + 1)).frame.payments
        (actualExecution source inputs depth).before (actualExecution source inputs depth).submitted (depth + 1) := by
  rw [actual_word]
  change source.update _ _ _ (trailAt source inputs (depth + 1)).length = _
  rw [length_exact, ← (actual_frame source inputs (depth + 1)).1]
  rfl

theorem recorded_payment_is_own_actual (visit : Nat) (index : source.Slot) (paid : Nat)
    (recorded : (trailAt source inputs visit).frame.payments index = some paid) :
    0 < paid ∧ paid < visit ∧ source.SlotPaid (currentAt source inputs paid)
      (ProgrammeSource.rawEvent (input source inputs)
        (ProgrammeHistory.visitAt (input source inputs) paid).current) index := by
  induction visit with
  | zero => cases recorded
  | succ visit ih =>
      change source.update _ _ _ (trailAt source inputs visit).length index = some paid at recorded
      rw [length_exact] at recorded
      unfold OutstandingSource.update at recorded
      split at recorded
      next old previous =>
        obtain ⟨positive, before, actual⟩ := ih (previous.trans recorded)
        exact ⟨positive, Nat.lt_succ_of_lt before, actual⟩
      next =>
        split at recorded
        next actual =>
          have same : paid = visit := (Option.some.inj recorded).symm
          subst paid
          have positive : 0 < visit := by
            by_contra absent
            have zero : visit = 0 := by omega
            subst visit
            exact source.no_payment_from_empty_word _ index actual
          rw [← (actual_frame source inputs visit).1, ← (actual_frame source inputs visit).2] at actual
          exact ⟨positive, Nat.lt_succ_self _, actual⟩
        next => cases recorded

theorem archive_preserved (visit later : Nat) (index : source.Slot) (paid : Nat)
    (recorded : (trailAt source inputs visit).frame.payments index = some paid) :
    (trailAt source inputs (visit + later)).frame.payments index = some paid := by
  induction later with
  | zero => exact recorded
  | succ later ih => exact source.payment_preserved _ _ _ _ index paid ih

def runningCurrent (depth : Nat) : (ProgrammeSource.V (input source inputs)).Current :=
  .running (currentAt source inputs (depth + 1))
    (ProgrammeSource.pastAt (ProgrammeHistory.visitAt (input source inputs) (depth + 1)).current)

theorem runningCurrent_is_own_visit (depth : Nat) : runningCurrent source inputs depth =
    (ProgrammeHistory.visitAt (input source inputs) (depth + 1)).current := by
  unfold runningCurrent currentAt
  change ProgrammeSource.Current.running
    (ProgrammeSource.rawCurrent (input source inputs) (ProgrammeSource.next (input source inputs)
      (ProgrammeHistory.visitAt (input source inputs) depth).current))
    (ProgrammeSource.pastAt (ProgrammeSource.next (input source inputs)
      (ProgrammeHistory.visitAt (input source inputs) depth).current)) =
    ProgrammeSource.next (input source inputs) (ProgrammeHistory.visitAt (input source inputs) depth).current
  cases (ProgrammeHistory.visitAt (input source inputs) depth).current <;> rfl

def taskEntry (depth : Nat) := ProgrammeSource.sourceEntry (input source inputs)
  (runningCurrent source inputs depth) (.instruction ⟨0, by change 0 < 1; decide⟩)

def taskWrite (depth : Nat) :=
  (ProgrammeLedger.evolution (input source inputs) (runningCurrent source inputs depth)).destination
    (taskEntry source inputs depth)

def writtenReceipt (depth : Nat) := ProgrammeLedger.writtenTransferReceipt (input source inputs)
  (currentAt source inputs (depth + 1))
  (ProgrammeSource.pastAt (ProgrammeHistory.visitAt (input source inputs) (depth + 1)).current)
  (taskEntry source inputs depth)

theorem receipt_is_in_own_original_write (depth : Nat) :
    ProgrammeLedger.transferReceiptOf (input source inputs) (taskWrite source inputs depth).2 =
      some (writtenReceipt source inputs depth) := by
  exact (ProgrammeLedger.destination_transfer_receipt (input source inputs) _ _
    (taskEntry source inputs depth)).trans
    (congrArg some (ProgrammeLedger.writtenTransferReceipt_exact (input source inputs) _ _
      (taskEntry source inputs depth)).symm)

theorem own_next_consumes_actual_residual (depth : Nat) (afterInputs : inputs.length ≤ depth) :
    (writtenReceipt source inputs (depth + 1)).val =
      (source.decideAt (actualExecution source inputs depth).after
        (source.update (trailAt source inputs (depth + 1)).frame.payments
          (actualExecution source inputs depth).before
          (actualExecution source inputs depth).submitted (depth + 1))).report := by
  rw [(writtenReceipt source inputs (depth + 1)).property]
  change reportAt source inputs (currentAt source inputs (depth + 2)) = _
  unfold reportAt report
  rw [ordinal_exact, if_neg (by omega), List.getElem?_eq_none (by omega)]
  rw [actual_payment_update, actual_next]


open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

structure RootFrame (ordinal : Nat) where
  private mk ::
  frame : source.Frame
  visit : RootVisit (ProgrammeLiving.livingRoot (input source inputs)).toAuthoritativeRoot.toRoot
  frame_exact : frame = foldedFrameAt source inputs ordinal
  visit_exact : visit = ProgrammeHistory.visitAt (input source inputs) ordinal

namespace RootFrame

private theorem next_current (current : ProgrammeSource.Current
    (RawCurrent Party Good Technology Instrument)) :
    ProgrammeSource.next (input source inputs) current =
      .running
        (source.seed.law.next (ProgrammeSource.rawCurrent (input source inputs) current)
          (ProgrammeSource.rawEvent (input source inputs) current))
        (ProgrammeSource.pastAt current ++ [ProgrammeSource.rawCurrent (input source inputs) current]) := by
  cases current <;> rfl

private theorem next_visit_eq
    (visit : RootVisit (ProgrammeLiving.livingRoot (input source inputs)).toAuthoritativeRoot.toRoot)
    (next : ProgrammeSource.Current (RawCurrent Party Good Technology Instrument))
    (same : ProgrammeSource.next (input source inputs) visit.current = next) :
    visit.next (next := next) (by
      change some (ProgrammeSource.next (input source inputs) visit.current) = some next
      exact congrArg some same) =
      visit.next (next := ProgrammeSource.next (input source inputs) visit.current) rfl := by
  subst next
  rfl

def produce : (ordinal : Nat) → RootFrame source inputs ordinal
  | 0 => ⟨⟨source.seed.initial, fun _ => none⟩,
      (ProgrammeLiving.livingRoot (input source inputs)).toAuthoritativeRoot.toRoot.initialVisit,
      rfl, rfl⟩
  | ordinal + 1 =>
    let before := produce ordinal
    let after := advanceFrame source inputs ordinal before.frame
    let next := ProgrammeSource.Current.running after.raw
      (ProgrammeSource.pastAt before.visit.current ++ [before.frame.raw])
    have raw : ProgrammeSource.rawCurrent (input source inputs) before.visit.current = before.frame.raw := by
      rw [before.visit_exact, before.frame_exact, foldedFrameAt_is_the_complete_original_frame]
      exact (actual_frame source inputs ordinal).1
    have word : ProgrammeSource.rawEvent (input source inputs) before.visit.current =
        History.word source inputs ordinal before.frame := by
      rw [before.visit_exact, before.frame_exact, foldedFrameAt_is_the_complete_original_frame]
      exact (actual_frame source inputs ordinal).2
    have next_is_source : ProgrammeSource.next (input source inputs) before.visit.current = next := by
      rw [next_current, raw, word]
      rfl
    let visit := before.visit.next (next := next) (by
      change some (ProgrammeSource.next (input source inputs) before.visit.current) = some next
      exact congrArg some next_is_source)
    ⟨after, visit, by
      change advanceFrame source inputs ordinal before.frame = foldedFrameAt source inputs (ordinal + 1)
      rw [before.frame_exact]
      unfold foldedFrameAt
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil], by
      calc
        visit = before.visit.next
            (next := ProgrammeSource.next (input source inputs) before.visit.current) rfl :=
          next_visit_eq source inputs before.visit next next_is_source
        _ = ProgrammeHistory.visitAt (input source inputs) (ordinal + 1) := by
          rw [before.visit_exact]
          rfl⟩

end RootFrame

def foldedRootVisitAt (ordinal : Nat) := (RootFrame.produce source inputs ordinal).visit

theorem foldedRootVisitAt_is_the_original_visit (ordinal : Nat) :
    foldedRootVisitAt source inputs ordinal = ProgrammeHistory.visitAt (input source inputs) ordinal :=
  (RootFrame.produce source inputs ordinal).visit_exact

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History
