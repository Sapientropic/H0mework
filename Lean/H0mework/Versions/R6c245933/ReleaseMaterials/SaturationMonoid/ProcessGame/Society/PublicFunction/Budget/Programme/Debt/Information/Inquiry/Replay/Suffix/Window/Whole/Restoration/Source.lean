import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future.Reification
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

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
    (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code)

abbrev old := Replanning.native model point
abbrev count := point.cut+Cut.horizon point.source point.entry point.cut
abbrev target (opponent : Opponent model.source.code) (term : Cut.Term point.source point.entry point.cut) :
    Native.Authority.Sources (old model point).base (old model point).scope :=
  ⟨Future.target point.source point.entry point.cut opponent term.val,model.law_exact,model.task_exact⟩

variable (opponent : Opponent model.source.code) (term : Cut.Term point.source point.entry point.cut)
  (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)

theorem the_joint_target_has_the_same_actual_arrival :
    Native.Future.atTarget (old model point)
        (target model point (Future.jointOpponent point.source point.entry point.cut opponent) term) (count model point) =
      Native.Future.atTarget (old model point) (target model point opponent term) (count model point) := by
  exact Future.joint_current point.source point.entry point.cut opponent term.val rfl rfl term.property _ (by
    dsimp only [Native.Future.targetDepth,Machine.Continuation.depth,count,Cut.horizon,target]
    omega)

theorem joint_compiled_output :
    (Native.Future.plan (old model point)
      (target model point (Future.jointOpponent point.source point.entry point.cut opponent) term) (count model point) word).output =
      (Native.Future.plan (old model point) (target model point opponent term) (count model point) word).output :=
  congrArg (fun current => (Mandate.Replay.compile model.base model.scope current word).output)
    (the_joint_target_has_the_same_actual_arrival model point opponent term)

theorem joint_installed_source :
    Native.Authority.sourceIndex (Native.Future.installed (old model point)
        (target model point (Future.jointOpponent point.source point.entry point.cut opponent) term) (count model point) word) =
      Native.Authority.sourceIndex (Native.Future.installed (old model point)
        (target model point opponent term) (count model point) word) := by
  apply Subtype.ext
  change Machine.Continuation.extend _ _ _ = Machine.Continuation.extend _ _ _
  rw [joint_compiled_output model point opponent term word]
  exact Future.reified_joint_successor_is_the_same_actual_source point.source point.entry point.cut opponent term.val
    rfl rfl term.property (count model point) (Nat.le_refl _) _

theorem joint_recovery_beginning
    (left : Native.Future.Receipt (old model point) (depth point)
      (target model point (Future.jointOpponent point.source point.entry point.cut opponent) term) (count model point) word)
    (right : Native.Future.Receipt (old model point) (depth point) (target model point opponent term) (count model point) word) :
    Native.Future.Recovery.begin left = Native.Future.Recovery.begin right := by
  have arrival := the_joint_target_has_the_same_actual_arrival model point opponent term
  have consumed := congrArg (fun current => (Mandate.Replay.compile model.base model.scope current word).consumed) arrival
  have residual := congrArg (fun current => (Mandate.Replay.compile model.base model.scope current word).residual) arrival
  unfold Native.Future.Recovery.begin
  congr 1
  · exact joint_installed_source model point opponent term word

abbrev Tariff := Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)

def recover
    (receipt : Native.Future.Receipt (old model point) (depth point)
      (target model point opponent term) (count model point) word)
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :=
  Native.Future.Recovery.produceWith tariff receipt

private def readBeginning
    (cursor : {cursor : Native.Future.Recovery.Cursor (old model point) (depth point) word //
      cursor.source.val.code = model.source.code})
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :
    Native.Future.Recovery.Assessment.Report (old model point) ×
      Option (Native.Future.Recovery.Funding.Failure (old model point) (depth point) word) :=
  let made := tariff.execute cursor.val
  (⟨made.finish.consumed.length,
    (made.source_code_is_retained.trans cursor.property) ▸
      Native.Window.evaluate made.finish.model (depth point) (made.finish.depth-depth point)⟩,
    Native.Future.Recovery.Funding.ofWalk made)

def outcome (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :
    Option (Native.Future.Recovery.Assessment.Report (old model point) ×
      Option (Native.Future.Recovery.Funding.Failure (old model point) (depth point) word)) :=
  match Native.Future.produce (old model point) (depth point) (target model point opponent term) (count model point) word with
  | .inl _ => none
  | .inr receipt => some (readBeginning model point word ⟨Native.Future.Recovery.begin receipt,rfl⟩ tariff)

def report (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :=
  (outcome model point opponent term word tariff).map Prod.fst

def funding (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :=
  (outcome model point opponent term word tariff).bind Prod.snd

private theorem joint_data_from_receipts
    (left : Native.Future.Receipt (old model point) (depth point)
      (target model point (Future.jointOpponent point.source point.entry point.cut opponent) term) (count model point) word)
    (right : Native.Future.Receipt (old model point) (depth point) (target model point opponent term) (count model point) word)
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    readBeginning model point word ⟨Native.Future.Recovery.begin left,rfl⟩ tariff =
      readBeginning model point word ⟨Native.Future.Recovery.begin right,rfl⟩ tariff :=
  congrArg (fun cursor => readBeginning model point word cursor tariff)
    (Subtype.ext (joint_recovery_beginning model point opponent term word left right))

theorem joint_report_from_generated_receipts
    (left : Native.Future.Receipt (old model point) (depth point)
      (target model point (Future.jointOpponent point.source point.entry point.cut opponent) term) (count model point) word)
    (right : Native.Future.Receipt (old model point) (depth point) (target model point opponent term) (count model point) word) :
    Native.Future.Recovery.Assessment.reportFrom (Native.Future.Recovery.produce left) (depth point) rfl =
      Native.Future.Recovery.Assessment.reportFrom (Native.Future.Recovery.produce right) (depth point) rfl := by
  change (readBeginning model point word ⟨Native.Future.Recovery.begin left,rfl⟩ .unpriced).1 =
    (readBeginning model point word ⟨Native.Future.Recovery.begin right,rfl⟩ .unpriced).1
  exact congrArg Prod.fst (joint_data_from_receipts model point opponent term word left right .unpriced)

theorem joint_recovered_actual_cursor
    (left : Native.Future.Receipt (old model point) (depth point)
      (target model point (Future.jointOpponent point.source point.entry point.cut opponent) term) (count model point) word)
    (right : Native.Future.Receipt (old model point) (depth point) (target model point opponent term) (count model point) word) :
    (Native.Future.Recovery.produce left).walk.finish = (Native.Future.Recovery.produce right).walk.finish :=
  congrArg (fun beginning => (Native.Future.Recovery.execute beginning).finish)
    (joint_recovery_beginning model point opponent term word left right)

theorem joint_outcome_is_the_same_actual_source
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :
    outcome model point (Future.jointOpponent point.source point.entry point.cut opponent) term word tariff =
      outcome model point opponent term word tariff := by
  by_cases legal : Mandate.Replay.Legal (base := model.base) model.scope
      (Native.Authority.currentAt (old model point) (depth point)) word
  · simp only [outcome,Native.Future.produce,dif_pos legal]
    apply congrArg some
    exact joint_data_from_receipts model point opponent term word _ _ tariff
  · simp only [outcome,Native.Future.produce,dif_neg legal]

theorem joint_report_is_the_same_complete_actual_evaluation
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :
    report model point (Future.jointOpponent point.source point.entry point.cut opponent) term word tariff =
      report model point opponent term word tariff :=
  congrArg (Option.map Prod.fst) (joint_outcome_is_the_same_actual_source model point opponent term word tariff)

theorem joint_funding_is_the_same_actual_obstruction
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :
    funding model point (Future.jointOpponent point.source point.entry point.cut opponent) term word tariff =
      funding model point opponent term word tariff :=
  congrArg (fun result => result.bind Prod.snd) (joint_outcome_is_the_same_actual_source model point opponent term word tariff)

theorem report_is_the_actual_paid_output
    (receipt : Native.Future.Receipt (old model point) (depth point)
      (target model point opponent term) (count model point) word)
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :
    report model point opponent term word tariff = some
      (Native.Future.Recovery.Assessment.reportFrom (recover model point opponent term word receipt tariff) (depth point) rfl) := by
  simp only [report,outcome,Native.Future.produce,dif_pos receipt.origin,Option.map_some]
  cases tariff <;> rfl

theorem funding_is_the_actual_paid_output
    (receipt : Native.Future.Receipt (old model point) (depth point)
      (target model point opponent term) (count model point) word)
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :
    funding model point opponent term word tariff =
      Native.Future.Recovery.Funding.ofWalk (recover model point opponent term word receipt tariff).walk := by
  simp only [funding,outcome,Native.Future.produce,dif_pos receipt.origin,Option.bind_some]
  cases tariff <;> rfl

theorem every_registered_report_is_generated
    (inside : word ∈ Native.Future.Recovery.capabilities (old model point) (depth point))
    (tariff : Tariff (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := .unpriced) :
    ∃ actual,report model point opponent term word tariff = some actual := by
  have legal := (Native.Future.Recovery.capability_is_registered_and_legal word inside).2
  simp only [report,outcome,Native.Future.produce,dif_pos legal,Option.map_some]
  exact ⟨_,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration
