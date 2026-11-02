import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.CrossCap

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code) (party : Party) (good : Good)
  (floor : Gross.Floor model.source.code.law party good model.source.code.actions)

abbrev pool : List (Program model.source.code) :=
  reference :: Bounds.catalogue model domain fallback reference party good floor
abbrev canonical (program : Program model.source.code) :=
  Bounds.representative model domain fallback reference party good floor program
abbrev Supported (program : Program model.source.code) : Prop :=
  ∀ n < Whole.Complete.horizon domain, (stage model.source.code fallback program n).supported
abbrev Accepted (old new : Program model.source.code) := Bounds.Accepted model domain fallback old new
abbrev axes := Selection.axes model domain fallback (pool model domain fallback reference party good floor)
abbrev benefit := Selection.benefit model domain fallback (pool model domain fallback reference party good floor)
abbrev Improves := Distributed.Improves (axes model domain fallback reference party good floor)
  (benefit model domain fallback reference party good floor)
abbrev Outcome := Selection.Outcome model domain fallback (pool model domain fallback reference party good floor) reference
def compile : Outcome model domain fallback reference party good floor :=
  Selection.compile model domain fallback (pool model domain fallback reference party good floor) reference

theorem reference_is_generated : reference ∈ pool model domain fallback reference party good floor := List.mem_cons_self

theorem canonical_is_generated (program : Program model.source.code)
    (supported : Supported model domain fallback program) :
    canonical model domain fallback reference party good floor program ∈ pool model domain fallback reference party good floor :=
  List.mem_cons_of_mem _ (Bounds.every_supported_representative_is_in_the_generated_catalogue
    model domain fallback reference party good floor program supported)

variable (raw : Program model.source.code) (supported : Supported model domain fallback raw)
  (accepted : Accepted model domain fallback reference raw)

include supported accepted in
theorem canonical_keeps_every_complete_evaluation (world : Replanning.Point model domain)
    (rival : Opponent model.source.code) :
    Finite.actualEvaluation model world.val fallback (canonical model domain fallback reference party good floor raw) rival =
      Finite.actualEvaluation model world.val fallback raw rival :=
  Bounds.every_accepted_raw_program_has_a_complete_representative model domain fallback reference party good floor raw supported accepted world rival

include supported accepted in
theorem canonical_keeps_every_benefit :
    benefit model domain fallback reference party good floor (canonical model domain fallback reference party good floor raw) =
      benefit model domain fallback reference party good floor raw := by
  funext axis
  cases axis with
  | economic world table axis =>
    exact congrArg (fun evaluation => evaluation.value axis.val)
      (canonical_keeps_every_complete_evaluation model domain fallback reference party good floor raw supported accepted world
        (Finite.opponent world.val fallback (pool model domain fallback reference party good floor) table.val))
  | native world table anchor =>
    exact congrArg (fun evaluation : Evaluation model.source.code =>
      if (Authority.Trace.Lawful.inventory evaluation.native).due.Subperm
        (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback
          (pool model domain fallback reference party good floor) world anchor table).native).due then (0 : ℚ) else 1)
      (canonical_keeps_every_complete_evaluation model domain fallback reference party good floor raw supported accepted world
        (Finite.opponent world.val fallback (pool model domain fallback reference party good floor) table.val))

include supported accepted in
theorem canonical_is_accepted :
    Selection.acceptable model domain fallback (pool model domain fallback reference party good floor) reference
      (canonical model domain fallback reference party good floor raw) := by
  apply (Selection.acceptable_iff_every_common_external_opponent model domain fallback
    (pool model domain fallback reference party good floor) reference _
    (reference_is_generated model domain fallback reference party good floor)
    (canonical_is_generated model domain fallback reference party good floor raw supported)).mpr
  intro world rival
  rw [canonical_keeps_every_complete_evaluation model domain fallback reference party good floor raw supported accepted world rival]
  exact accepted world rival

variable (protocol : Program model.source.code)
  (generated : protocol ∈ pool model domain fallback reference party good floor)
  (checked : Selection.verify model domain fallback (pool model domain fallback reference party good floor) reference protocol = true)

include generated checked in
theorem verified_program_protects_every_actual_responsibility : Accepted model domain fallback reference protocol :=
  Selection.every_verified_protocol_protects_its_own_actual_full_responsibility model domain fallback
    (pool model domain fallback reference party good floor) reference protocol
    (reference_is_generated model domain fallback reference party good floor) generated checked

include generated checked in
theorem independent_review_excludes_every_supported_raw_dominator
    (other : Program model.source.code) (supportedOther : Supported model domain fallback other)
    (acceptedOther : Accepted model domain fallback protocol other) :
    ¬ Improves model domain fallback reference party good floor protocol other := by
  have own := verified_program_protects_every_actual_responsibility model domain fallback reference party good floor protocol generated checked
  have original : Accepted model domain fallback reference other := fun world rival =>
    Synthesis.accepts_trans _ _ _ _ _ (acceptedOther world rival) (own world rival)
  have newGenerated := canonical_is_generated model domain fallback reference party good floor other supportedOther
  have newAccepted : Selection.acceptable model domain fallback (pool model domain fallback reference party good floor) reference
      (canonical model domain fallback reference party good floor other) :=
    canonical_is_accepted model domain fallback reference party good floor other supportedOther original
  have maximal := ((Selection.verify_iff model domain fallback (pool model domain fallback reference party good floor) reference protocol).mp checked).2
    (canonical model domain fallback reference party good floor other) newGenerated newAccepted
  intro better
  apply maximal
  have values := canonical_keeps_every_benefit model domain fallback reference party good floor other supportedOther original
  dsimp only [benefit] at values
  simpa only [Improves,Distributed.Improves,Distributed.NoWorse,benefit,axes,values] using better

variable (choice : Selection.Choice model domain fallback (pool model domain fallback reference party good floor) reference)

include choice in
theorem selected_has_no_supported_raw_dominator (other : Program model.source.code)
    (supportedOther : Supported model domain fallback other) (acceptedOther : Accepted model domain fallback choice.policy.protocol other) :
    ¬ Improves model domain fallback reference party good floor choice.policy.protocol other :=
  independent_review_excludes_every_supported_raw_dominator model domain fallback reference party good floor choice.policy.protocol
    choice.policy.generated
    (Selection.independently_replayed_choice_is_accepted model domain fallback (pool model domain fallback reference party good floor) reference choice)
    other supportedOther acceptedOther

include choice in
theorem every_supported_raw_improvement_is_actually_selected
    (available : ∃ other : Program model.source.code, Supported model domain fallback other ∧ Accepted model domain fallback reference other ∧
      Improves model domain fallback reference party good floor reference other) :
    Improves model domain fallback reference party good floor reference choice.policy.protocol := by
  obtain ⟨other,supportedOther,acceptedOther,better⟩ := available
  apply Selection.every_full_responsibility_improvement_is_realized model domain fallback
    (pool model domain fallback reference party good floor) reference choice
  refine ⟨canonical model domain fallback reference party good floor other,
    canonical_is_generated model domain fallback reference party good floor other supportedOther,
    canonical_is_accepted model domain fallback reference party good floor other supportedOther acceptedOther,?_⟩
  have values := canonical_keeps_every_benefit model domain fallback reference party good floor other supportedOther acceptedOther
  dsimp only [benefit] at values
  simpa only [Improves,Distributed.Improves,Distributed.NoWorse,benefit,axes,values] using better

theorem a_blocked_outcome_excludes_every_supported_raw_program
    (rejected : ∀ program, program ∈ pool model domain fallback reference party good floor →
      Selection.Rejection model domain fallback (pool model domain fallback reference party good floor) reference program)
    (other : Program model.source.code) (supportedOther : Supported model domain fallback other) :
    ¬ Accepted model domain fallback reference other := by
  intro acceptedOther
  have generated := canonical_is_generated model domain fallback reference party good floor other supportedOther
  have passes := canonical_is_accepted model domain fallback reference party good floor other supportedOther acceptedOther
  exact (rejected _ generated).broken (passes _ (rejected _ generated).generated)


/-- A rejected raw programme is checked on its own raw reachable domain. -/
abbrev RawRejection (program : Program model.source.code) :=
  Selection.Rejection model domain fallback [reference,program] reference program

def rawRejection
    (rejected : ∀ program, program ∈ pool model domain fallback reference party good floor →
      Selection.Rejection model domain fallback (pool model domain fallback reference party good floor) reference program)
    (program : Program model.source.code) (programSupported : Supported model domain fallback program) :
    RawRejection model domain fallback reference program :=
  match inspect (Selection.holds model domain fallback [reference,program] reference program)
      (Selection.rows model domain fallback [reference,program]) with
  | .rejected row inside broken => ⟨row,inside,broken⟩
  | .accepted all => False.elim (by
      have actual := (Selection.acceptable_iff_every_common_external_opponent model domain fallback
        [reference,program] reference program (by simp) (by simp)).mp all
      exact a_blocked_outcome_excludes_every_supported_raw_program model domain fallback reference party good floor rejected program programSupported actual)

def verifyRawRejection (program : Program model.source.code)
    (row : Selection.Row model domain fallback [reference,program]) : Bool :=
  !decide (Selection.holds model domain fallback [reference,program] reference program row)

theorem each_raw_failure_is_independently_replayed (program : Program model.source.code)
    (failure : RawRejection model domain fallback reference program) :
    verifyRawRejection model domain fallback reference program failure.row = true := by
  simp only [verifyRawRejection,Bool.not_eq_true',decide_eq_false_iff_not]
  exact failure.broken

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.CrossCap
