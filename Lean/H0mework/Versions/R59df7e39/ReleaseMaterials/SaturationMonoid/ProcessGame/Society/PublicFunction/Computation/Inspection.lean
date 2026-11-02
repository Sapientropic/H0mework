import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation

open Distributed Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument Row : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

/-- A source tariff for one row operation and its retained pending-row cells. These
are original material requests, not a hardware instruction-count claim. -/
structure Tariff (Row : Type) where
  compute : Row → RawEvent Party Good Port Technology Instrument
  retain : Nat → RawEvent Party Good Port Technology Instrument

def Tariff.word (tariff : Tariff (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) Row) (row : Row) (cells : Nat) :=
  tariff.compute row ++ tariff.retain cells

variable (holds : Row → Prop) [DecidablePred holds]
  (tariff : Tariff (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) Row)

/-- The constructors retain the actual payment boundary. A successful row
decision is inaccessible until its source requests have passed that boundary. -/
inductive InspectionTrace : RawCurrent Party Good Technology Instrument → List Row → Type where
  | empty (current) : InspectionTrace current []
  | unsupported (current row rest)
      (missing : tariff.word row (rest.length + 1) ∉ words code.actions code.actionLimit) :
      InspectionTrace current (row :: rest)
  | unpaid (current row rest)
      (supported : tariff.word row (rest.length + 1) ∈ words code.actions code.actionLimit)
      (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ code.law.rawItems current (tariff.word row (rest.length + 1)))
      (refused : ¬ code.law.Valid item.before item.request) : InspectionTrace current (row :: rest)
  | failed (current row rest)
      (supported : tariff.word row (rest.length + 1) ∈ words code.actions code.actionLimit)
      (paid : ∀ item ∈ code.law.rawItems current (tariff.word row (rest.length + 1)),
        code.law.Valid item.before item.request)
      (broken : ¬ holds row) : InspectionTrace current (row :: rest)
  | passed (current row rest)
      (supported : tariff.word row (rest.length + 1) ∈ words code.actions code.actionLimit)
      (paid : ∀ item ∈ code.law.rawItems current (tariff.word row (rest.length + 1)),
        code.law.Valid item.before item.request)
      (checked : holds row)
      (later : InspectionTrace (code.law.next current (tariff.word row (rest.length + 1))) rest) :
      InspectionTrace current (row :: rest)

/-- Neither an Inspection nor an accepted Candidate is an input. Row results
are computed only in the paid branch, before generating the next row. -/
def inspectPaid (current : RawCurrent Party Good Technology Instrument) :
    (rows : List Row) → InspectionTrace code holds tariff current rows
  | [] => .empty current
  | row :: rest =>
      if supported : tariff.word row (rest.length + 1) ∈ words code.actions code.actionLimit then
        match Distributed.inspect (fun item : ExecutionItem Party Good Port Technology Instrument =>
            code.law.Valid item.before item.request)
            (code.law.rawItems current (tariff.word row (rest.length + 1))) with
        | .rejected item original refused => .unpaid current row rest supported item original refused
        | .accepted paid =>
            if checked : holds row then .passed current row rest supported paid checked
              (inspectPaid (code.law.next current (tariff.word row (rest.length + 1))) rest)
            else .failed current row rest supported paid checked
      else .unsupported current row rest supported

namespace InspectionTrace

variable {code holds tariff} {current : RawCurrent Party Good Technology Instrument} {rows : List Row}

def submitted : {current : RawCurrent Party Good Technology Instrument} → {rows : List Row} →
    InspectionTrace code holds tariff current rows → List (RawEvent Party Good Port Technology Instrument)
  | _, _, .empty _ | _, _, .unsupported .. => []
  | _, _, .unpaid _ row rest .. | _, _, .failed _ row rest .. => [tariff.word row (rest.length + 1)]
  | _, _, .passed _ row rest _ _ _ later => tariff.word row (rest.length + 1) :: later.submitted

def final : {current : RawCurrent Party Good Technology Instrument} → {rows : List Row} →
    InspectionTrace code holds tariff current rows → RawCurrent Party Good Technology Instrument
  | _, _, .empty current | _, _, .unsupported current .. => current
  | _, _, .unpaid current row rest .. | _, _, .failed current row rest .. =>
      code.law.next current (tariff.word row (rest.length + 1))
  | _, _, .passed _ _ _ _ _ _ later => later.final

def result : {current : RawCurrent Party Good Technology Instrument} → {rows : List Row} →
    InspectionTrace code holds tariff current rows → Option (Distributed.Inspection holds rows)
  | _, _, .empty _ => some (.accepted (by simp))
  | _, _, .unsupported .. | _, _, .unpaid .. => none
  | _, _, .failed _ row _ _ _ broken => some (.rejected row List.mem_cons_self broken)
  | _, _, .passed _ row _ _ _ checked later =>
      match later.result with
      | none => none
      | some (.accepted all) => some (.accepted (by
          intro other inside
          rcases List.mem_cons.mp inside with same | tail
          · exact same ▸ checked
          · exact all other tail))
      | some (.rejected other inside broken) =>
          some (.rejected other (List.mem_cons_of_mem row inside) broken)

def allPaid : {current : RawCurrent Party Good Technology Instrument} → {rows : List Row} →
    InspectionTrace code holds tariff current rows → Prop
  | _, _, .empty _ | _, _, .unsupported .. => True
  | _, _, .unpaid .. => False
  | _, _, .failed .. => True
  | _, _, .passed _ _ _ _ _ _ later => later.allPaid

structure Blocker (current : RawCurrent Party Good Technology Instrument) (rows : List Row) where
  row : Row
  original : row ∈ rows
  position : Nat
  before : RawCurrent Party Good Technology Instrument
  fee : RawEvent Party Good Port Technology Instrument
  reason : fee ∉ words code.actions code.actionLimit ∨
    ∃ item ∈ code.law.rawItems before fee, ¬ code.law.Valid item.before item.request

def blocker : {current : RawCurrent Party Good Technology Instrument} → {rows : List Row} →
    InspectionTrace code holds tariff current rows → Option (Blocker (code := code) current rows)
  | _, _, .empty _ | _, _, .failed .. => none
  | _, _, .unsupported current row rest missing =>
      some ⟨row,List.mem_cons_self,0,current,tariff.word row (rest.length+1),.inl missing⟩
  | _, _, .unpaid current row rest _ item original refused =>
      some ⟨row,List.mem_cons_self,0,current,tariff.word row (rest.length+1),.inr ⟨item,original,refused⟩⟩
  | _, _, .passed _ row _ _ _ _ later => later.blocker.map fun stopped =>
      ⟨stopped.row,List.mem_cons_of_mem row stopped.original,stopped.position+1,
        stopped.before,stopped.fee,stopped.reason⟩

omit [DecidableEq Port] [DecidableEq Technology] [DecidablePred holds] in
theorem every_blocker_names_the_actual_fee_cut
    (trace : InspectionTrace code holds tariff current rows)
    (stopped : Blocker (code := code) current rows) (found : trace.blocker = some stopped) :
    stopped.position ≤ trace.submitted.length ∧
      stopped.before = (trace.submitted.take stopped.position).foldl code.law.next current := by
  induction trace with
  | empty | failed => simp only [blocker] at found; cases found
  | unsupported | unpaid =>
      cases Option.some.inj found
      exact ⟨Nat.zero_le _,rfl⟩
  | passed before row rest supported paid checked later ih =>
      simp only [blocker] at found
      cases present : later.blocker with
      | none => simp only [present,Option.map_none] at found; cases found
      | some previous =>
          simp only [present,Option.map_some] at found
          cases Option.some.inj found
          obtain ⟨bounded,exactBefore⟩ := ih previous present
          exact ⟨Nat.succ_le_succ bounded,by simpa only [submitted,List.take_succ_cons,List.foldl_cons] using exactBefore⟩

omit [DecidableEq Port] [DecidableEq Technology] [DecidablePred holds] in
theorem every_supported_blocked_fee_is_an_actual_submission
    (trace : InspectionTrace code holds tariff current rows)
    (stopped : Blocker (code := code) current rows) (found : trace.blocker = some stopped)
    (supported : stopped.fee ∈ words code.actions code.actionLimit) :
    ∃ inside : stopped.position < trace.submitted.length, trace.submitted[stopped.position] = stopped.fee := by
  induction trace with
  | empty | failed => simp only [blocker] at found; cases found
  | unsupported _ _ _ missing =>
      cases Option.some.inj found
      exact False.elim (missing supported)
  | unpaid => cases Option.some.inj found; exact ⟨by simp [submitted],rfl⟩
  | passed before row rest support paid checked later ih =>
      simp only [blocker] at found
      cases present : later.blocker with
      | none => simp only [present,Option.map_none] at found; cases found
      | some previous =>
          simp only [present,Option.map_some] at found
          cases Option.some.inj found
          obtain ⟨inside,same⟩ := ih previous present supported
          exact ⟨Nat.succ_lt_succ inside,by simpa only [submitted,List.getElem_cons_succ] using same⟩

omit [DecidableEq Port] [DecidableEq Technology] [DecidablePred holds] in
theorem every_trace_generates_a_decision_or_a_specific_resource_blocker
    (trace : InspectionTrace code holds tariff current rows) :
    (∃ inspection, trace.result = some inspection) ∨ (∃ stopped, trace.blocker = some stopped) := by
  induction trace with
  | empty | failed => exact .inl ⟨_,rfl⟩
  | unsupported | unpaid => exact .inr ⟨_,rfl⟩
  | passed before head tail support paid checked later ih =>
      rcases ih with ⟨inspection,finished⟩ | ⟨stopped,blocked⟩
      · cases inspection with
        | accepted all =>
            refine .inl ⟨.accepted ?_,?_⟩
            · intro row inside
              rcases List.mem_cons.mp inside with same | rest
              · exact same ▸ checked
              · exact all row rest
            · simp only [result,finished]
        | rejected row inside broken =>
            exact .inl ⟨.rejected row (List.mem_cons_of_mem head inside) broken,by simp only [result,finished]⟩
      · exact .inr ⟨⟨stopped.row,List.mem_cons_of_mem head stopped.original,stopped.position+1,
          stopped.before,stopped.fee,stopped.reason⟩,by simp only [blocker,blocked,Option.map_some]⟩

omit [DecidableEq Port] [DecidableEq Technology] [DecidablePred holds] in
theorem final_is_the_fold_of_the_actual_submissions
    (trace : InspectionTrace code holds tariff current rows) :
    trace.final = trace.submitted.foldl code.law.next current := by
  induction trace with
  | empty | unsupported | unpaid | failed => rfl
  | passed _ _ _ _ _ _ _ ih => exact ih

omit [DecidableEq Port] [DecidableEq Technology] [DecidablePred holds] in
theorem every_submitted_word_has_original_source_support
    (trace : InspectionTrace code holds tariff current rows) :
    ∀ word ∈ trace.submitted, word ∈ words code.actions code.actionLimit := by
  induction trace with
  | empty | unsupported => simp [submitted]
  | unpaid _ _ _ supported | failed _ _ _ supported => simpa [submitted] using supported
  | passed _ _ _ supported _ _ _ ih =>
      intro word inside
      rcases List.mem_cons.mp inside with same | tail
      · exact same ▸ supported
      · exact ih word tail

omit [DecidableEq Port] [DecidableEq Technology] [DecidablePred holds] in
theorem an_inspection_can_only_escape_a_fully_paid_trace
    (trace : InspectionTrace code holds tariff current rows)
    (inspection : Distributed.Inspection holds rows) (finished : trace.result = some inspection) : trace.allPaid := by
  induction trace with
  | empty | unsupported | unpaid | failed => simp_all [result,allPaid]
  | passed _ _ _ _ _ _ later ih =>
      simp only [result] at finished
      cases produced : later.result with
      | none => simp only [produced] at finished; cases finished
      | some inspection => exact ih inspection produced

end InspectionTrace

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation
