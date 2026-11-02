import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work.Acquisition
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {input : Input seed} (prepared : Prepared input)

def Covered {point : NativePoint input} : Stage input point → Prop
  | .stopped _ | .blocked _ => False
  | .ready scope => input.span ≤ (initial input point).state.remaining ∧
      input.future ≤ (comparisonPoint scope).state.remaining
instance {point : NativePoint input} (stage : Stage input point) : Decidable (Covered stage) := by
  cases stage <;> unfold Covered <;> infer_instance

inductive Coverage where
  | accepted (all : ∀ index : Index prepared, Covered prepared.saved[index].stage)
  | blocked (index : Index prepared) (broken : ¬ Covered prepared.saved[index].stage)

def auditCoverage : Coverage prepared :=
  match Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) (keys prepared) with
  | .accepted all => .accepted (fun index => all index (List.mem_finRange _))
  | .rejected index _ broken => .blocked index broken

def checked : Outcome prepared (baseline prepared) → Bool :=
  Work.Outcome.checked prepared (baseline prepared)

structure Protocol where
  private mk ::
  compilation : Work.Compilation prepared (baseline prepared)
  compilation_exact : compilation = Work.compile prepared (baseline prepared)
  outcome : Outcome prepared (baseline prepared)
  generated : outcome = compilation.result.outcome prepared
  receipt : Work.Receipt prepared compilation
  coverage : Coverage prepared
  coverage_exact : coverage = auditCoverage prepared
  verified : Bool
  verified_exact : verified = checked prepared outcome
  release_exact : verified = receipt.authorized

def invoke : Protocol prepared :=
  let made := Work.compile prepared (baseline prepared)
  let review := Work.certify prepared made
  ⟨made,rfl,made.result.outcome prepared,rfl,review,auditCoverage prepared,rfl,review.authorized,
    review.authorized_matches_the_original_independent_verifier,rfl⟩

variable {prepared}
namespace Protocol
variable (record : Protocol prepared)
/-- Cached public comparison and independent replay, including each native local operation. -/
def work : List (Work.Operation prepared) := record.receipt.work

theorem verified_is_the_cached_native_release : record.verified = record.receipt.authorized := record.release_exact

theorem whole_cached_public_work_fits_its_source_budget :
    Work.controlSteps prepared record.work ≤ Work.workBudget prepared := by
  rcases record with ⟨compilation,compiled,outcome,generated,receipt,coverage,coverage_exact,verified,verified_exact,release_exact⟩
  subst compilation
  exact Work.receipt_release_fits_the_generated_budget prepared (baseline prepared) (sections prepared) (List.Perm.refl _) receipt

def authorized : Bool := match record.coverage with
  | .accepted _ => record.verified
  | .blocked .. => false

def retained {point : NativePoint input} : Stage input point → Cursor (point.world.native seed input.budget) (point.world.input seed input.budget)
  | .stopped header => header.endpoint
  | .blocked failure => comparisonPoint failure.retained
  | .ready scope => comparisonPoint scope

def executeLocal {point : NativePoint input} : (stage : Stage input point) → Local stage → Cursor (point.world.native seed input.budget) (point.world.input seed input.budget)
  | .stopped header,_ => header.endpoint
  | .blocked failure,_ => comparisonPoint failure.retained
  | .ready scope,term => Whole.execute scope input.span term

def endpoint (actual : Index prepared) :=
  if record.authorized then match record.outcome with
    | .selected choice => executeLocal prepared.saved[actual].stage (readTerm prepared choice.policy.term actual)
    | .blocked _ => retained prepared.saved[actual].stage
  else retained prepared.saved[actual].stage

theorem failed_review_retains_the_actual_preparation (actual : Index prepared) (failed : record.authorized = false) :
    record.endpoint actual = retained prepared.saved[actual].stage := by simp only [endpoint,failed,Bool.false_eq_true,ite_false]

theorem accepted_selection_executes_its_original_native_intent (actual : Index prepared)
    (choice : Choice prepared (baseline prepared)) (selected : record.outcome = .selected choice)
    (allowed : record.authorized = true) :
    record.endpoint actual = executeLocal prepared.saved[actual].stage (readTerm prepared choice.policy.term actual) := by
  simp only [endpoint,allowed,ite_true,selected]

theorem authorized_coverage (allowed : record.authorized = true) :
    ∀ index : Index prepared, Covered prepared.saved[index].stage := by
  unfold authorized at allowed
  cases same : record.coverage with
  | accepted all => exact all
  | blocked index broken => simp only [same] at allowed;cases allowed
end Protocol

/-- Original fee, quote generation, public scanning, and independent review remain separately addressable. -/
inductive Obligation (prepared : Prepared input) where
  | publicPreparation
  | invoiceQuotation (index : Index prepared)
  | publicComparison
  | independentVerification
  | nativePreparation (index : Index prepared)
  | rootReadout

def obligations (prepared : Prepared input) : List (Obligation prepared) :=
  [.publicPreparation,.publicComparison,.independentVerification,.rootReadout] ++
    (keys prepared).flatMap (fun index => [.invoiceQuotation index,.nativePreparation index])

theorem ready_stageFor_preserves_the_open_family (recipe : Recipe) (point : NativePoint input)
    (scope : Scope (initial input point) input.pricing input.future (reference input point) input.actor input.position)
    (same : stageFor input recipe point = .ready scope) : scope.ownFamily = true := by
  cases recipe with
  | initial =>
    unfold stageFor prepareStage at same
    split at same
    · cases same
    · cases same;rfl
  | reserved prior units =>
    dsimp only [stageFor] at same
    unfold reserveStage at same
    split at same
    · cases same
    · cases same
    · split at same
      · cases same
      · split at same
        · cases same;rfl
        · cases same

theorem ready_generated_cells_preserve_the_open_original_family
    (cell : Cell input) (scope : Scope (initial input cell.point) input.pricing input.future
      (reference input cell.point) input.actor input.position) (same : cell.stage = .ready scope) :
    scope.ownFamily = true :=
  ready_stageFor_preserves_the_open_family cell.recipe cell.point scope (cell.generated.symm.trans same)

def allOpponentNoWorse {point : NativePoint input} (stage : Stage input point) : Local stage → Local stage → Prop :=
  match stage with
  | .stopped _ | .blocked _ => fun _ _ => False
  | .ready scope => fun new previous => Deployable scope new ∧
      ∀ rival : Opponent (initial input point).source.val.code,
        accepts (initial input point) (tensor scope input.span new rival) (tensor scope input.span previous rival)

theorem local_comparison_covers_every_adaptive_opponent {point : NativePoint input}
    (stage : Stage input point) (new previous : Local stage) (covered : Covered stage)
    (accepted : localNoWorse stage new previous) : allOpponentNoWorse stage new previous := by
  cases stage with
  | stopped _ => exact covered.elim
  | blocked _ => exact covered.elim
  | ready scope => exact ⟨accepted.1,
      (finite_relation_iff_every_same_adaptive_opponent scope input.span (accepts (initial input point))
        new previous covered.1 covered.2).mp accepted.2⟩

theorem public_selection_retains_all_adaptive_opponents
    (record : Protocol prepared) (allowed : record.authorized = true)
    (choice : Choice prepared (baseline prepared)) :
    ∀ index : Index prepared, allOpponentNoWorse prepared.saved[index].stage
      (readTerm prepared choice.policy.term index) (readTerm prepared (baseline prepared) index) :=
  fun index => local_comparison_covers_every_adaptive_opponent _ _ _
    (record.authorized_coverage allowed index) (choice.policy.accepted.2.2 index)

variable (record : Protocol prepared) (actual : Index prepared)
namespace Runtime
abbrev point := record.endpoint actual
structure Snapshot where
  private mk ::
  execution : Protocol prepared
  execution_exact : execution = record
  work : List (Work.Operation prepared)
  work_exact : work = record.work
  pending : List (Work.Obligation prepared)
  pending_exact : pending = Work.pending prepared work
  outstanding : List (Obligation prepared)
  outstanding_exact : outstanding = obligations prepared
  learning : Cursor (prepared.saved[actual].point.world.native seed input.budget) (prepared.saved[actual].point.world.input seed input.budget)
  learning_exact : learning = point record actual
  whole : Evaluation (point record actual).source.val.code
  whole_exact : whole = Window.evaluate (point record actual).model (initial input prepared.saved[actual].point).depth ((point record actual).depth-(initial input prepared.saved[actual].point).depth)
  native : Authority.FullDisposition (point record actual).model ((point record actual).depth-1)
  native_exact : native = Authority.fullGenerate _ _

def generate : Snapshot record actual :=
  ⟨record,rfl,record.work,rfl,Work.pending prepared record.work,rfl,obligations prepared,rfl,point record actual,rfl,
    Window.evaluate (point record actual).model (initial input prepared.saved[actual].point).depth ((point record actual).depth-(initial input prepared.saved[actual].point).depth),rfl,
    Authority.fullGenerate _ _,rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (point record actual).source.val.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (point record actual).source.val.input (point record actual).depth).current → Snapshot record actual
  project := fun _ {_} _ _ _own => generate record actual

def root := (Online.Runtime.root (point record actual)).withProjectionCoface (projectionLaw record actual)

theorem original_programme_root_is_preserved : (root record actual).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (point record actual).source.val.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (point record actual).source.val.input) :=
  ⟨ProgrammeSource.V _,root record actual,ProgrammeHistory.temporalVisit _ ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (point record actual).source.val.input) where
  State := Nat
  stateAt := stateAt record actual
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (point record actual).source.val.input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (point record actual).source.val.input first).current =
        (ProgrammeHistory.visitAt (point record actual).source.val.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Online.Runtime.Face)
  | computation

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (point record actual).source.val.input) where
  process := process record actual
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Online.Runtime.facade (point record actual)).componentAt (Online.Runtime.facade (point record actual)).seed previous
    | .computation => projectionLaw record actual
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Online.Runtime.facade (point record actual)).installationAt (Online.Runtime.facade (point record actual)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Online.Runtime.root (point record actual)).toAuthoritativeRoot.source (projectionLaw record actual))
    | computation =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Online.Runtime.root (point record actual)).toAuthoritativeRoot.source (projectionLaw record actual)
  projectionAt := fun _ face => match face with
    | .previous previous => (Online.Runtime.facade (point record actual)).projectionAt (Online.Runtime.facade (point record actual)).seed previous
    | .computation => ()

abbrev activated := (facade record actual).seed.advance (point record actual).depth

theorem activated_state : (activated record actual).state = (point record actual).depth := by
  have all (n : Nat) : ((facade record actual).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Snapshot record actual :=
  match (facade record actual).readoutAt (activated record actual) .computation with
  | .inl output => output.2 (by
      change (ProgrammeHistory.visitAt (point record actual).source.val.input (activated record actual).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_the_public_choice_actual_preparation_whole_responsibility_and_next :
    let active := activated record actual
    (read record actual).execution = record ∧
    (read record actual).outstanding = obligations prepared ∧
    (read record actual).learning = record.endpoint actual ∧
    (read record actual).whole = Window.evaluate (point record actual).model (initial input prepared.saved[actual].point).depth ((point record actual).depth-(initial input prepared.saved[actual].point).depth) ∧
    (read record actual).native = Authority.fullGenerate (point record actual).model ((point record actual).depth-1) ∧
    HEq ((facade record actual).readoutAt active .computation) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process record actual).stateAt ((process record actual).successor active.state) := by
  have rooted := (facade record actual).readoutAt_factorizes (activated record actual) .computation
  exact ⟨rfl,rfl,rfl,rfl,rfl,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
/-- The same installed root preserves every comparison/review operation and its exact unresolved calls. -/
theorem the_original_root_retains_the_native_public_work_and_every_typed_debt :
    (read record actual).work = record.work ∧
    (read record actual).pending = Work.pending prepared record.work ∧
    (read record actual).work.length = Work.controlSteps prepared (read record actual).work +
      (read record actual).pending.length := by
  exact ⟨rfl,rfl,Work.every_operation_is_an_expanded_step_or_a_retained_obligation prepared record.work⟩

end Runtime
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
namespace CoverageAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

abbrev Check (prepared : Prepared input) (remaining : List (Index prepared)) := Distributed.Inspection (fun index : Index prepared => Covered prepared.saved[index].stage) remaining
private def liftCheck (head : Index prepared) {tail : List (Index prepared)} (checked : Covered prepared.saved[head].stage) : Check prepared tail → Check prepared (head::tail)
  | .accepted all => .accepted (by
      intro index inside;rcases List.mem_cons.mp inside with same | later
      · subst index;exact checked
      · exact all index later)
  | .rejected index listed broken => .rejected index (List.mem_cons_of_mem _ listed) broken
private theorem liftCheck_exact (head : Index prepared) (tail : List (Index prepared)) (checked : Covered prepared.saved[head].stage) :
    liftCheck head checked (Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) tail) =
      Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) (head::tail) := by
  simp only [Distributed.inspect,checked,↓reduceDIte]
  cases Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) tail <;> rfl
private def fromCheck : Check prepared (keys prepared) → Coverage prepared
  | .accepted all => .accepted (fun index => all index (List.mem_finRange _))
  | .rejected index _ broken => .blocked index broken
private theorem fromCheck_exact (checked : Check prepared (keys prepared))
    (actual : checked = Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) (keys prepared)) :
    fromCheck checked = auditCoverage prepared := by
  cases actual;dsimp only [auditCoverage];cases Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) (keys prepared) <;> rfl
inductive State (prepared : Prepared input) where
  | checking (remaining : List (Index prepared)) (embed : Check prepared remaining → Check prepared (keys prepared))
      (coherent : embed (Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) remaining) = Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) (keys prepared))
  | finished (coverage : Coverage prepared) (generated : coverage = auditCoverage prepared)
def initial (prepared : Prepared input) : State prepared := .checking (keys prepared) id rfl
inductive Event (prepared : Prepared input) where
  | checked (index : Index prepared) (value : Bool) (actual : value = decide (Covered prepared.saved[index].stage))
  | completed (coverage : Coverage prepared) (generated : coverage = auditCoverage prepared)
def move : State prepared → Option (State prepared × Event prepared)
  | .checking [] embed coherent =>
      let coverage := fromCheck (embed (.accepted (by simp)))
      let exact := fromCheck_exact _ coherent
      some (.finished coverage exact,.completed coverage exact)
  | .checking (head::tail) embed coherent =>
      if checked : Covered prepared.saved[head].stage then
        some (.checking tail (fun later => embed (liftCheck head checked later)) (by rw [liftCheck_exact];exact coherent),.checked head true (by exact (decide_eq_true checked).symm))
      else
        let actual : embed (.rejected head List.mem_cons_self checked) = Distributed.inspect (fun index : Index prepared => Covered prepared.saved[index].stage) (keys prepared) := by
          rw [←coherent];congr 1;rw [Distributed.inspect,dif_neg checked]
        some (.finished (fromCheck _) (fromCheck_exact _ actual),.checked head false (by exact (decide_eq_false checked).symm))
  | .finished .. => none
def State.rank : State prepared → Nat | .checking remaining .. => remaining.length+1 | .finished .. => 0
def State.done : State prepared → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared} {event : Event prepared} (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | checking remaining embed coherent =>
      cases remaining with
      | nil => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,List.length_nil];omega
      | cons head tail =>
          dsimp only [move] at actual;split at actual
          all_goals cases Option.some.inj actual;simp only [State.rank,List.length_cons];omega
  | finished => cases actual
theorem no_move_iff_done (before : State prepared) : move before = none ↔ before.done = true := by
  cases before with
  | checking remaining => cases remaining <;> dsimp only [move,State.done] <;> first | (split <;> simp) | simp
  | finished => simp [move,State.done]
end CoverageAcquisition
namespace ProtocolAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

private def pack (compilation : Work.Compilation prepared (baseline prepared)) (compiled : compilation = Work.compile prepared (baseline prepared))
    (receipt : Work.Receipt prepared compilation) (_reviewed : receipt = Work.certify prepared compilation)
    (coverage : Coverage prepared) (covered : coverage = auditCoverage prepared) : Protocol prepared :=
  ⟨compilation,compiled,compilation.result.outcome prepared,rfl,receipt,coverage,covered,receipt.authorized,
    receipt.authorized_matches_the_original_independent_verifier,rfl⟩
private theorem pack_exact (compilation : Work.Compilation prepared (baseline prepared)) (compiled : compilation = Work.compile prepared (baseline prepared))
    (receipt : Work.Receipt prepared compilation) (reviewed : receipt = Work.certify prepared compilation)
    (coverage : Coverage prepared) (covered : coverage = auditCoverage prepared) : pack compilation compiled receipt reviewed coverage covered = invoke prepared := by
  cases compiled;cases reviewed;cases covered;rfl
inductive State (prepared : Prepared input) where
  | opening
  | compiling (cursor : Work.CompilationAcquisition.State prepared (baseline prepared))
  | reviewing (compilation : Work.Compilation prepared (baseline prepared)) (compiled : compilation = Work.compile prepared (baseline prepared))
      (cursor : Work.ReceiptAcquisition.State compilation)
  | coverage (compilation : Work.Compilation prepared (baseline prepared)) (compiled : compilation = Work.compile prepared (baseline prepared))
      (receipt : Work.Receipt prepared compilation) (reviewed : receipt = Work.certify prepared compilation)
      (cursor : CoverageAcquisition.State prepared)
  | authorizing (compilation : Work.Compilation prepared (baseline prepared)) (compiled : compilation = Work.compile prepared (baseline prepared))
      (receipt : Work.Receipt prepared compilation) (reviewed : receipt = Work.certify prepared compilation)
      (coverage : Coverage prepared) (covered : coverage = auditCoverage prepared)
  | finished (protocol : Protocol prepared) (generated : protocol = invoke prepared)
def initial (prepared : Prepared input) : State prepared := .opening
inductive Event (prepared : Prepared input) where
  | opened
  | compilation (event : Work.CompilationAcquisition.Event prepared (baseline prepared))
  | compiled (compilation : Work.Compilation prepared (baseline prepared)) (generated : compilation = Work.compile prepared (baseline prepared))
  | review (compilation : Work.Compilation prepared (baseline prepared)) (event : Work.ReceiptAcquisition.Event compilation)
  | reviewed (compilation : Work.Compilation prepared (baseline prepared)) (receipt : Work.Receipt prepared compilation)
      (generated : receipt = Work.certify prepared compilation)
  | coverage (event : CoverageAcquisition.Event prepared)
  | covered (coverage : Coverage prepared) (generated : coverage = auditCoverage prepared)
  | completed (protocol : Protocol prepared) (generated : protocol = invoke prepared)
def move : State prepared → Option (State prepared × Event prepared)
  | .opening => some (.compiling (Work.CompilationAcquisition.initial prepared (baseline prepared)),.opened)
  | .compiling (.finished compilation generated) =>
      some (.reviewing compilation generated (Work.ReceiptAcquisition.initialKnown compilation generated),.compiled compilation generated)
  | .compiling cursor@(.collection ..) | .compiling cursor@(.scanning ..) =>
      match _step : Work.CompilationAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.compiling after,.compilation event)
  | .reviewing compilation compiled (.finished receipt generated) =>
      some (.coverage compilation compiled receipt generated (CoverageAcquisition.initial prepared),.reviewed compilation receipt generated)
  | .reviewing compilation compiled cursor@(.opening) | .reviewing compilation compiled cursor@(.openingKnown ..) | .reviewing compilation compiled cursor@(.rejectingKnown ..) | .reviewing compilation compiled cursor@(.rejection ..) | .reviewing compilation compiled cursor@(.verifying ..) | .reviewing compilation compiled cursor@(.rejecting ..) | .reviewing compilation compiled cursor@(.reviewing ..) =>
      match _step : Work.ReceiptAcquisition.move compilation cursor with
      | none => none
      | some (after,event) => some (.reviewing compilation compiled after,.review compilation event)
  | .coverage compilation compiled receipt reviewed (.finished coverage generated) =>
      some (.authorizing compilation compiled receipt reviewed coverage generated,.covered coverage generated)
  | .coverage compilation compiled receipt reviewed cursor@(.checking ..) =>
      match _step : CoverageAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.coverage compilation compiled receipt reviewed after,.coverage event)
  | .authorizing compilation compiled receipt reviewed coverage covered =>
      let protocol := pack compilation compiled receipt reviewed coverage covered
      let exact := pack_exact compilation compiled receipt reviewed coverage covered
      some (.finished protocol exact,.completed protocol exact)
  | .finished .. => none
def State.rank : State prepared → Nat
  | .opening => (Work.CompilationAcquisition.initial prepared (baseline prepared)).rank+Work.ReceiptAcquisition.openingRank prepared+(keys prepared).length+9
  | .compiling cursor => cursor.rank+Work.ReceiptAcquisition.openingRank prepared+(keys prepared).length+7
  | .reviewing compilation _ cursor => cursor.rank compilation+(keys prepared).length+5
  | .coverage _ _ _ _ cursor => cursor.rank+2
  | .authorizing .. => 1
  | .finished .. => 0
def State.done : State prepared → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared} {event : Event prepared} (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | opening => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | compiling cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Work.CompilationAcquisition.State.rank,Work.ReceiptAcquisition.initialKnown,Work.ReceiptAcquisition.State.rank];omega
      | collection | scanning =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := Work.CompilationAcquisition.progress step;simp only [State.rank];omega)
  | reviewing compilation compiled cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Work.ReceiptAcquisition.State.rank,CoverageAcquisition.initial,CoverageAcquisition.State.rank];omega
      | opening | openingKnown | rejectingKnown | rejection | verifying | rejecting | reviewing =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := Work.ReceiptAcquisition.progress compilation step;simp only [State.rank];omega)
  | coverage compilation compiled receipt reviewed cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,CoverageAcquisition.State.rank];omega
      | checking =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := CoverageAcquisition.progress step;simp only [State.rank];omega
  | authorizing => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done (before : State prepared) : move before = none ↔ before.done = true := by
  cases before with
  | opening | authorizing | finished => simp [move,State.done]
  | compiling cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | collection | scanning =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Work.CompilationAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | reviewing compilation compiled cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | opening | openingKnown | rejectingKnown | rejection | verifying | rejecting | reviewing =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Work.ReceiptAcquisition.no_move_iff_done compilation _).mp stopped;cases done)
            | simp
  | coverage compilation compiled receipt reviewed cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | checking =>
          dsimp only [move,State.done];split
          · rename_i stopped;have done := (CoverageAcquisition.no_move_iff_done _).mp stopped;cases done
          · simp
end ProtocolAcquisition

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
