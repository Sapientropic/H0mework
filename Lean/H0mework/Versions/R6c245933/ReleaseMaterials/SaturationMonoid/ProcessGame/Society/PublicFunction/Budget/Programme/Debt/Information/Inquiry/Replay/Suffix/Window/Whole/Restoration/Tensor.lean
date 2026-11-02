import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (point : Cursor model.source.code)

structure Tensor where
  present : Evaluation model.source.code
  restoration : (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) →
    Option (Native.Future.Recovery.Assessment.Report (old model point) ×
      Option (Native.Future.Recovery.Funding.Failure (old model point) (depth point) word))

abbrev Tensor.future {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {point : Cursor model.source.code} (tensor : Tensor model point) (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :=
  (tensor.restoration word).map Prod.fst
abbrev Tensor.funding {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {point : Cursor model.source.code} (tensor : Tensor model point) (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :=
  (tensor.restoration word).bind Prod.snd

variable {fuel : Nat} (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (program : Continuation.Whole.Program model.source.code fuel)

def actualTensor (rival : Opponent model.source.code) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) : Tensor model point :=
  ⟨Window.Whole.actualEvaluation model point original program rival,
    outcome (tariff := tariff) model point (Continuation.Whole.controller point original program rival)
      (Continuation.Whole.schedule point original program)⟩

def tableTensor (table : Cut.Table point.source point.entry point.cut) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) : Tensor model point :=
  actualTensor (tariff := tariff) model point original program (Cut.opponent point.source point.entry point.cut table)

theorem one_common_external_table_generates_the_same_complete_restoration_tensor
    (rival : Opponent model.source.code) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) :
    tableTensor (tariff := tariff) model point original program (externalTable point rival) = actualTensor (tariff := tariff) model point original program rival := by
  simp only [tableTensor,actualTensor,Tensor.mk.injEq]
  constructor
  · exact Window.Whole.one_common_table_preserves_the_entire_actual_evaluation model point original program rival
  · funext word
    have same := Continuation.Whole.one_external_restriction_controls_the_entire_program model point original program rival
    change Future.jointOpponent point.source point.entry point.cut
        (Continuation.Whole.controller point original program (Cut.opponent point.source point.entry point.cut (externalTable point rival))) =
      Future.jointOpponent point.source point.entry point.cut (Continuation.Whole.controller point original program rival) at same
    calc
      _ = outcome (tariff := tariff) model point (Future.jointOpponent point.source point.entry point.cut
          (Continuation.Whole.controller point original program (Cut.opponent point.source point.entry point.cut (externalTable point rival))))
          (Continuation.Whole.schedule point original program) word :=
        (joint_outcome_is_the_same_actual_source (tariff := tariff) model point _ _ word).symm
      _ = outcome (tariff := tariff) model point (Future.jointOpponent point.source point.entry point.cut
          (Continuation.Whole.controller point original program rival)) (Continuation.Whole.schedule point original program) word := by rw [same]
      _ = _ := joint_outcome_is_the_same_actual_source (tariff := tariff) model point _ _ word

theorem finite_relation_iff_every_same_full_adaptive_opponent
    (relation : Tensor model point → Tensor model point → Prop)
    (new previous : Continuation.Whole.Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) :
    (∀ table ∈ Cut.tables point.source point.entry point.cut,
      relation (tableTensor (tariff := tariff) model point original new table) (tableTensor (tariff := tariff) model point original previous table)) ↔
      ∀ rival : Opponent model.source.code,
        relation (actualTensor (tariff := tariff) model point original new rival) (actualTensor (tariff := tariff) model point original previous rival) := by
  constructor
  · intro finite rival
    have checked := finite (externalTable point rival) (Residual.restriction_is_generated _ _ _ rival)
    rw [one_common_external_table_generates_the_same_complete_restoration_tensor (tariff := tariff),
      one_common_external_table_generates_the_same_complete_restoration_tensor (tariff := tariff)] at checked
    exact checked
  · intro all table _
    exact all _

def futureNoWorse (new previous : Option (Native.Future.Recovery.Assessment.Report (old model point))) : Prop :=
  Family.ReportsNoWorse (Native.Future.Recovery.Assessment.NoWorse (old model point) (depth point)) new previous

instance (new previous : Option (Native.Future.Recovery.Assessment.Report (old model point))) :
    Decidable (futureNoWorse model point new previous) := by
  cases new <;> cases previous <;> unfold futureNoWorse Family.ReportsNoWorse <;> infer_instance

/-- New raw requests enter this same source cut's comparison before a programme is selected. -/
def required (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :=
  match requested with
  | [] => Native.Future.Recovery.capabilities (old model point) (depth point)
  | _ :: _ => Native.Future.Recovery.capabilities (old model point) (depth point) ++
      requested.filter (fun word => decide (Mandate.Replay.Legal (base := model.base) model.scope
        (Native.Authority.currentAt (old model point) (depth point)) word))

theorem every_required_word_is_legal (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (inside : word ∈ required model point requested) :
    Mandate.Replay.Legal (base := model.base) model.scope
      (Native.Authority.currentAt (old model point) (depth point)) word := by
  cases requested with
  | nil => exact (Native.Future.Recovery.capability_is_registered_and_legal word inside).2
  | cons head tail =>
      rcases List.mem_append.mp inside with registered | supplied
      · exact (Native.Future.Recovery.capability_is_registered_and_legal word registered).2
      · exact of_decide_eq_true (List.mem_filter.mp supplied).2

theorem every_old_capability_is_required (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (inside : word ∈ Native.Future.Recovery.capabilities (old model point) (depth point)) :
    word ∈ required model point requested := by
  cases requested with
  | nil => exact inside
  | cons head tail => exact List.mem_append_left _ inside

theorem every_legal_request_is_required (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (supplied : word ∈ requested)
    (legal : Mandate.Replay.Legal (base := model.base) model.scope
      (Native.Authority.currentAt (old model point) (depth point)) word) :
    word ∈ required model point requested := by
  cases requested with
  | nil => cases supplied
  | cons head tail => exact List.mem_append_right _ (List.mem_filter.mpr ⟨supplied,decide_eq_true legal⟩)

theorem every_required_report_is_generated
    (opponent : Opponent model.source.code) (term : Cut.Term point.source point.entry point.cut)
    (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (inside : word ∈ required model point requested)
    (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) :
    ∃ actual,report (tariff := tariff) model point opponent term word = some actual := by
  have legal := every_required_word_is_legal model point requested word inside
  simp only [report,outcome,Native.Future.produce,dif_pos legal,Option.map_some]
  exact ⟨_,rfl⟩

def Tensor.family {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {point : Cursor model.source.code}
    (tensor : Tensor model point) :
    Family.Tensor (Evaluation model.source.code)
      (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
      (fun _ _ => Native.Future.Recovery.Assessment.Report (old model point))
      (fun _ word => Native.Future.Recovery.Funding.Failure (old model point) (depth point) word) :=
  ⟨tensor.present,tensor.restoration⟩

def accepts (new previous : Tensor model point) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Prop :=
  Family.Accepts (Synthesis.accepts model.source.code (economicAxes point.source point.cut))
    (fun _ _ _ => Native.Future.Recovery.Assessment.NoWorse (old model point) (depth point))
    (required model point requested) new.family previous.family

instance (new previous : Tensor model point) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)) : Decidable (accepts (requested := requested) model point new previous) := by
  unfold accepts Family.Accepts
  infer_instance

theorem futureNoWorse_trans
    {first middle last : Option (Native.Future.Recovery.Assessment.Report (old model point))}
    (left : futureNoWorse model point first middle) (right : futureNoWorse model point middle last) :
    futureNoWorse model point first last := by
  cases first <;> cases middle <;> cases last <;> simp only [futureNoWorse,Family.ReportsNoWorse] at *
  all_goals first | contradiction | exact Native.Future.Recovery.Assessment.noWorse_trans _ _ left right

theorem accepts_trans {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} {first middle last : Tensor model point}
    (left : accepts (requested := requested) model point first middle) (right : accepts (requested := requested) model point middle last) : accepts (requested := requested) model point first last :=
  ⟨Synthesis.accepts_trans _ _ _ _ _ left.1 right.1,
    (fun word inside => futureNoWorse_trans model point
      (first := first.future word) (middle := middle.future word) (last := last.future word)
      (left.2.1 word inside) (right.2.1 word inside)),
    fun word inside funded => left.2.2 word inside (right.2.2 word inside funded)⟩

theorem the_same_opponent_compares_present_and_every_registered_future
    {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)}
    (new previous : Continuation.Whole.Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) :
    (∀ table ∈ Cut.tables point.source point.entry point.cut,
      accepts (requested := requested) model point (tableTensor (tariff := tariff) model point original new table) (tableTensor (tariff := tariff) model point original previous table)) ↔
      ∀ rival : Opponent model.source.code,
        accepts (requested := requested) model point (actualTensor (tariff := tariff) model point original new rival) (actualTensor (tariff := tariff) model point original previous rival) :=
  finite_relation_iff_every_same_full_adaptive_opponent (tariff := tariff) model point original (accepts (requested := requested) model point) new previous


theorem accepted_is_self_acceptable {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} {new previous : Tensor model point}
    (accepted : accepts (requested := requested) model point new previous) : accepts (requested := requested) model point new new := by
  refine ⟨⟨accepted.1.1,accepted.1.2.1,rfl,?_,fun _ _ => le_refl _⟩,?_,fun _ _ yes => yes⟩
  · exact Authority.Trace.Lawful.refl _
  · intro word inside
    have present := accepted.2.1 word inside
    change futureNoWorse model point (new.future word) (previous.future word) at present
    change futureNoWorse model point (new.future word) (new.future word)
    cases left : new.future word <;> cases right : previous.future word <;>
      simp only [futureNoWorse,Family.ReportsNoWorse,left,right] at present ⊢
    all_goals first | contradiction | exact Native.Future.Recovery.Assessment.noWorse_refl _ _ _


/-- Adding a request cannot remove any previously registered capability. -/
theorem requested_acceptance_retains_every_registered_obligation
    {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)}
    {new previous : Tensor model point}
    (accepted : accepts (requested := requested) model point new previous) :
    accepts model point new previous :=
  ⟨accepted.1,
    fun word inside => accepted.2.1 word (every_old_capability_is_required model point requested word inside),
    fun word inside => accepted.2.2 word (every_old_capability_is_required model point requested word inside)⟩

inductive Failure (new previous : Tensor model point)
    (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)) where
  | present (broken : ¬ Synthesis.accepts model.source.code (economicAxes point.source point.cut)
      new.present previous.present)
  | future (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
      (required : word ∈ Restoration.required model point requested)
      (broken : ¬ futureNoWorse model point (new.future word) (previous.future word))
  | funding (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
      (required : word ∈ Restoration.required model point requested)
      (previousPaid : (previous.funding word).isNone = true)
      (nowRefused : (new.funding word).isNone ≠ true)

/-- Failure records the exact checked word and the two actual tensor projections. -/
def explain (new previous : Tensor model point)
    (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (denied : ¬ accepts (requested := requested) model point new previous) :
    Failure model point new previous requested :=
  if present : Synthesis.accepts model.source.code (economicAxes point.source point.cut)
      new.present previous.present then
    match Distributed.inspect (fun word => futureNoWorse model point (new.future word) (previous.future word))
        (required model point requested) with
    | .rejected word inside broken => .future word inside broken
    | .accepted futures =>
      match Distributed.inspect (fun word => (previous.funding word).isNone = true →
          (new.funding word).isNone = true) (required model point requested) with
      | .rejected word inside broken =>
        have previousPaid : (previous.funding word).isNone = true := by
          by_contra no
          exact broken (fun yes => (no yes).elim)
        .funding word inside previousPaid (fun yes => broken (fun _ => yes))
      | .accepted funding => False.elim (denied ⟨present,(fun query member => futures query member),funding⟩)
  else .present present

theorem quiet_tensor (quiet : PublicDomain.quiet (code := model.source.code) = true)
    (rival : Opponent model.source.code) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) :
    actualTensor (tariff := tariff) model point original program rival = actualTensor (tariff := tariff) model point original program PublicDomain.silent := by
  have same := Window.Whole.quiet_controllers model point original program quiet rival
  simp only [actualTensor,Tensor.mk.injEq]
  constructor
  · exact Window.Whole.quiet_evaluation model point original program quiet rival
  · exact congrArg (fun driver => outcome (tariff := tariff) model point driver (Continuation.Whole.schedule point original program)) same

theorem stages_generate_the_same_complete_tensor {otherFuel : Nat}
    (second : Continuation.Whole.Program model.source.code otherFuel)
    (stages : ∀ ordinal < Cut.horizon point.source point.entry point.cut,
      program.at original ordinal = second.at original ordinal) (rival : Opponent model.source.code) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) :
    actualTensor (tariff := tariff) model point original program rival = actualTensor (tariff := tariff) model point original second rival := by
  have terms : (schedule point original program).val = (schedule point original second).val := by
    apply List.map_congr_left
    intro ordinal inside
    rw [stages ordinal (List.mem_range.mp inside)]
  have tables : Continuation.Whole.tableController model point original program (externalTable point rival) =
      Continuation.Whole.tableController model point original second (externalTable point rival) := by
    funext history past frame
    change (if member : (history,past,frame) ∈ Residual.keys model.source.code
        (Residual.seed point.source point.entry point.cut) (Residual.schedules point.source point.entry point.cut)
      then controller point original program (finiteRival point rival) history past frame else none) = _
    by_cases member : (history,past,frame) ∈ Residual.keys model.source.code
        (Residual.seed point.source point.entry point.cut) (Residual.schedules point.source point.entry point.cut)
    · simp only [Continuation.Whole.tableController,Future.jointOpponent,Residual.respond,Residual.restrict,dif_pos member,controller,
        Continuation.Whole.controller,stages _ (Continuation.Whole.Complete.every_registered_decision_has_a_consumed_stage point _ member)]
    · simp only [Continuation.Whole.tableController,Future.jointOpponent,Residual.respond,dif_neg member]
  have drivers := (Continuation.Whole.one_external_restriction_controls_the_entire_program model point original program rival).symm.trans
    (tables.trans (Continuation.Whole.one_external_restriction_controls_the_entire_program model point original second rival))
  simp only [actualTensor,Tensor.mk.injEq]
  constructor
  · exact Window.Whole.stages_generate_the_same_complete_evaluation model point original program second stages rival
  · funext word
    calc
      _ = outcome (tariff := tariff) model point (Future.jointOpponent point.source point.entry point.cut
          (Continuation.Whole.controller point original program rival)) (Continuation.Whole.schedule point original program) word :=
        (joint_outcome_is_the_same_actual_source (tariff := tariff) model point _ _ word).symm
      _ = outcome (tariff := tariff) model point (Future.jointOpponent point.source point.entry point.cut
          (Continuation.Whole.controller point original second rival)) (Continuation.Whole.schedule point original second) word := by
        rw [drivers,show Continuation.Whole.schedule point original program = Continuation.Whole.schedule point original second from Subtype.ext terms]
      _ = _ := joint_outcome_is_the_same_actual_source (tariff := tariff) model point _ _ word

theorem clipping_preserves_the_complete_actual_tensor (bound : Nat)
    (enough : Cut.horizon point.source point.entry point.cut ≤ bound) (rival : Opponent model.source.code) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) :
    actualTensor (tariff := tariff) model point original (Continuation.Whole.Complete.clip bound program) rival =
      actualTensor (tariff := tariff) model point original program rival := by
  apply stages_generate_the_same_complete_tensor (tariff := tariff)
  intro ordinal inside
  exact Continuation.Whole.Complete.clipping_keeps_each_consumed_stage bound program original ordinal (inside.trans_le enough)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration
