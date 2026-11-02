import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Joint
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection.Indexed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

private def sourceAxes (code : Code Party Good Port (Mandate.State Party Technology) Instrument) : List (Party × Good) :=
  code.parties.flatMap fun party => code.goods.map fun good => (party,good)

/-- Both constructors carry primitive material readings; neither carries a cap or a normalizer. -/
inductive Basis (code : Code Party Good Port (Mandate.State Party Technology) Instrument) where
  | single (party : Party) (good : Good) (floor : Gross.Floor code.law party good code.actions)
  | joint (readings : Gross.Joint.Coverage code.law (sourceAxes code) code.actions)

namespace Span

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code) (basis : Basis model.source.code)

def cap : Nat := match basis with
  | .single party good floor => floor.cap (Programme.Bounds.upper model domain fallback reference (party,good))
  | .joint readings => Gross.Joint.cap model.source.code.law (sourceAxes model.source.code) readings.tickets
      (Programme.Bounds.upper model domain fallback reference)

abbrev representative (program : Program model.source.code) :=
  normalized (cap model domain fallback reference basis) (Whole.Complete.horizon domain) fallback program
abbrev catalogue : List (Program model.source.code) :=
  programs model.source.code (cap model domain fallback reference basis) (Whole.Complete.horizon domain)
abbrev Accepted := Programme.Bounds.Accepted model domain fallback

variable (program : Program model.source.code)
  (supported : ∀ n < Whole.Complete.horizon domain, (stage model.source.code fallback program n).supported)
  (accepted : Accepted model domain fallback reference program)

include supported accepted in
theorem every_accepted_raw_program_has_a_complete_representative
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    Finite.actualEvaluation model world.val fallback (representative model domain fallback reference basis program) rival =
      Finite.actualEvaluation model world.val fallback program rival := by
  cases basis with
  | single party good floor =>
    exact Programme.Bounds.every_accepted_raw_program_has_a_complete_representative model domain fallback reference
      party good floor program supported accepted world rival
  | joint readings =>
    exact Programme.Joint.every_accepted_raw_program_has_a_joint_complete_representative model domain fallback reference
      readings program supported accepted world rival

include supported in
theorem every_supported_representative_is_in_the_generated_catalogue :
    representative model domain fallback reference basis program ∈ catalogue model domain fallback reference basis :=
  every_supported_normalization_is_generated model.source.code fallback program
    (cap model domain fallback reference basis) (Whole.Complete.horizon domain) supported

end Span

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code) (basis : Basis model.source.code)

abbrev pool : List (Program model.source.code) :=
  reference :: Span.catalogue model domain fallback reference basis
abbrev canonical (program : Program model.source.code) :=
  Span.representative model domain fallback reference basis program
abbrev Supported (program : Program model.source.code) : Prop :=
  ∀ n < Whole.Complete.horizon domain, (stage model.source.code fallback program n).supported
abbrev Accepted (old new : Program model.source.code) := Span.Accepted model domain fallback old new
abbrev axes := Selection.axes model domain fallback (pool model domain fallback reference basis)
abbrev benefit := Selection.benefit model domain fallback (pool model domain fallback reference basis)
abbrev Improves := Distributed.Improves (axes model domain fallback reference basis)
  (benefit model domain fallback reference basis)
abbrev Outcome := Selection.Outcome model domain fallback (pool model domain fallback reference basis) reference
def compile : Outcome model domain fallback reference basis :=
  Selection.Indexed.compile model domain fallback reference (Span.catalogue model domain fallback reference basis)

theorem reference_is_generated : reference ∈ pool model domain fallback reference basis := List.mem_cons_self

theorem canonical_is_generated (program : Program model.source.code)
    (supported : Supported model domain fallback program) :
    canonical model domain fallback reference basis program ∈ pool model domain fallback reference basis :=
  List.mem_cons_of_mem _ (Span.every_supported_representative_is_in_the_generated_catalogue
    model domain fallback reference basis program supported)

variable (raw : Program model.source.code) (supported : Supported model domain fallback raw)
  (accepted : Accepted model domain fallback reference raw)

include supported accepted in
theorem canonical_keeps_every_complete_evaluation (world : Replanning.Point model domain)
    (rival : Opponent model.source.code) :
    Finite.actualEvaluation model world.val fallback (canonical model domain fallback reference basis raw) rival =
      Finite.actualEvaluation model world.val fallback raw rival :=
  Span.every_accepted_raw_program_has_a_complete_representative model domain fallback reference basis raw supported accepted world rival

include supported accepted in
theorem canonical_keeps_every_benefit :
    benefit model domain fallback reference basis (canonical model domain fallback reference basis raw) =
      benefit model domain fallback reference basis raw := by
  funext axis
  cases axis with
  | economic world table axis =>
    exact congrArg (fun evaluation => evaluation.value axis.val)
      (canonical_keeps_every_complete_evaluation model domain fallback reference basis raw supported accepted world
        (Finite.opponent world.val fallback (pool model domain fallback reference basis) table.val))
  | native world table anchor =>
    exact congrArg (fun evaluation : Evaluation model.source.code =>
      if (Authority.Trace.Lawful.inventory evaluation.native).due.Subperm
        (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback
          (pool model domain fallback reference basis) world anchor table).native).due then (0 : ℚ) else 1)
      (canonical_keeps_every_complete_evaluation model domain fallback reference basis raw supported accepted world
        (Finite.opponent world.val fallback (pool model domain fallback reference basis) table.val))

include supported accepted in
theorem canonical_is_accepted :
    Selection.acceptable model domain fallback (pool model domain fallback reference basis) reference
      (canonical model domain fallback reference basis raw) := by
  apply (Selection.acceptable_iff_every_common_external_opponent model domain fallback
    (pool model domain fallback reference basis) reference _
    (reference_is_generated model domain fallback reference basis)
    (canonical_is_generated model domain fallback reference basis raw supported)).mpr
  intro world rival
  rw [canonical_keeps_every_complete_evaluation model domain fallback reference basis raw supported accepted world rival]
  exact accepted world rival

variable (protocol : Program model.source.code)
  (generated : protocol ∈ pool model domain fallback reference basis)
  (checked : Selection.verify model domain fallback (pool model domain fallback reference basis) reference protocol = true)

include generated checked in
theorem verified_program_protects_every_actual_responsibility : Accepted model domain fallback reference protocol :=
  Selection.every_verified_protocol_protects_its_own_actual_full_responsibility model domain fallback
    (pool model domain fallback reference basis) reference protocol
    (reference_is_generated model domain fallback reference basis) generated checked

include generated checked in
theorem independent_review_excludes_every_supported_raw_dominator
    (other : Program model.source.code) (supportedOther : Supported model domain fallback other)
    (acceptedOther : Accepted model domain fallback protocol other) :
    ¬ Improves model domain fallback reference basis protocol other := by
  have own := verified_program_protects_every_actual_responsibility model domain fallback reference basis protocol generated checked
  have original : Accepted model domain fallback reference other := fun world rival =>
    Synthesis.accepts_trans _ _ _ _ _ (acceptedOther world rival) (own world rival)
  have newGenerated := canonical_is_generated model domain fallback reference basis other supportedOther
  have newAccepted : Selection.acceptable model domain fallback (pool model domain fallback reference basis) reference
      (canonical model domain fallback reference basis other) :=
    canonical_is_accepted model domain fallback reference basis other supportedOther original
  have maximal := ((Selection.verify_iff model domain fallback (pool model domain fallback reference basis) reference protocol).mp checked).2
    (canonical model domain fallback reference basis other) newGenerated newAccepted
  intro better
  apply maximal
  have values := canonical_keeps_every_benefit model domain fallback reference basis other supportedOther original
  dsimp only [benefit] at values
  simpa only [Improves,Distributed.Improves,Distributed.NoWorse,benefit,axes,values] using better

variable (choice : Selection.Choice model domain fallback (pool model domain fallback reference basis) reference)

include choice in
theorem selected_has_no_supported_raw_dominator (other : Program model.source.code)
    (supportedOther : Supported model domain fallback other) (acceptedOther : Accepted model domain fallback choice.policy.protocol other) :
    ¬ Improves model domain fallback reference basis choice.policy.protocol other :=
  independent_review_excludes_every_supported_raw_dominator model domain fallback reference basis choice.policy.protocol
    choice.policy.generated
    (Selection.independently_replayed_choice_is_accepted model domain fallback (pool model domain fallback reference basis) reference choice)
    other supportedOther acceptedOther

include choice in
theorem every_supported_raw_improvement_is_actually_selected
    (available : ∃ other : Program model.source.code, Supported model domain fallback other ∧ Accepted model domain fallback reference other ∧
      Improves model domain fallback reference basis reference other) :
    Improves model domain fallback reference basis reference choice.policy.protocol := by
  obtain ⟨other,supportedOther,acceptedOther,better⟩ := available
  apply Selection.every_full_responsibility_improvement_is_realized model domain fallback
    (pool model domain fallback reference basis) reference choice
  refine ⟨canonical model domain fallback reference basis other,
    canonical_is_generated model domain fallback reference basis other supportedOther,
    canonical_is_accepted model domain fallback reference basis other supportedOther acceptedOther,?_⟩
  have values := canonical_keeps_every_benefit model domain fallback reference basis other supportedOther acceptedOther
  dsimp only [benefit] at values
  simpa only [Improves,Distributed.Improves,Distributed.NoWorse,benefit,axes,values] using better

theorem a_blocked_outcome_excludes_every_supported_raw_program
    (rejected : ∀ program, program ∈ pool model domain fallback reference basis →
      Selection.Rejection model domain fallback (pool model domain fallback reference basis) reference program)
    (other : Program model.source.code) (supportedOther : Supported model domain fallback other) :
    ¬ Accepted model domain fallback reference other := by
  intro acceptedOther
  have generated := canonical_is_generated model domain fallback reference basis other supportedOther
  have passes := canonical_is_accepted model domain fallback reference basis other supportedOther acceptedOther
  exact (rejected _ generated).broken (passes _ (rejected _ generated).generated)


/-- A rejected raw programme is checked on its own raw reachable domain. -/
abbrev RawRejection (program : Program model.source.code) :=
  Selection.Rejection model domain fallback [reference,program] reference program

def rawRejection
    (rejected : ∀ program, program ∈ pool model domain fallback reference basis →
      Selection.Rejection model domain fallback (pool model domain fallback reference basis) reference program)
    (program : Program model.source.code) (programSupported : Supported model domain fallback program) :
    RawRejection model domain fallback reference program :=
  match inspect (Selection.holds model domain fallback [reference,program] reference program)
      (Selection.rows model domain fallback [reference,program]) with
  | .rejected row inside broken => ⟨row,inside,broken⟩
  | .accepted all => False.elim (by
      have actual := (Selection.acceptable_iff_every_common_external_opponent model domain fallback
        [reference,program] reference program (by simp) (by simp)).mp all
      exact a_blocked_outcome_excludes_every_supported_raw_program model domain fallback reference basis rejected program programSupported actual)

def verifyRawRejection (program : Program model.source.code)
    (row : Selection.Row model domain fallback [reference,program]) : Bool :=
  !decide (Selection.holds model domain fallback [reference,program] reference program row)

theorem each_raw_failure_is_independently_replayed (program : Program model.source.code)
    (failure : RawRejection model domain fallback reference program) :
    verifyRawRejection model domain fallback reference program failure.row = true := by
  simp only [verifyRawRejection,Bool.not_eq_true',decide_eq_false_iff_not]
  exact failure.broken

namespace Contracts

def Contract : Counted.Outcome model domain fallback reference basis → Prop
  | .selected choice =>
      (∀ other : Program model.source.code, Counted.Supported model domain fallback other →
        Counted.Accepted model domain fallback choice.policy.protocol other →
          ¬ Counted.Improves model domain fallback reference basis choice.policy.protocol other) ∧
      ((∃ other : Program model.source.code, Counted.Supported model domain fallback other ∧
        Counted.Accepted model domain fallback reference other ∧
        Counted.Improves model domain fallback reference basis reference other) →
          Counted.Improves model domain fallback reference basis reference choice.policy.protocol)
  | .blocked _ => ∀ other : Program model.source.code, Counted.Supported model domain fallback other →
      ¬ Counted.Accepted model domain fallback reference other

theorem every_outcome_contract (outcome : Counted.Outcome model domain fallback reference basis) :
    Contract model domain fallback reference basis outcome := by
  cases outcome with
  | selected choice => exact ⟨Counted.selected_has_no_supported_raw_dominator model domain fallback reference basis choice,
      Counted.every_supported_raw_improvement_is_actually_selected model domain fallback reference basis choice⟩
  | blocked rejected => exact Counted.a_blocked_outcome_excludes_every_supported_raw_program model domain fallback reference basis rejected

def Failures : Counted.Outcome model domain fallback reference basis → Type
  | .selected _ => Unit
  | .blocked _ => ∀ program : Program model.source.code, Counted.Supported model domain fallback program →
      Counted.RawRejection model domain fallback reference program

def failures (outcome : Counted.Outcome model domain fallback reference basis) :
    Failures model domain fallback reference basis outcome := by
  cases outcome with
  | selected => exact ()
  | blocked rejected => exact Counted.rawRejection model domain fallback reference basis rejected

end Contracts

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted
