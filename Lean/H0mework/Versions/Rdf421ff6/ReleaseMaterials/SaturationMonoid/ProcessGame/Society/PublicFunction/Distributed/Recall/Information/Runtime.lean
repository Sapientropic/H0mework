import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Synthesis

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (budget : Nat)


namespace Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable (world : World bound budget) (site : Fin bound.source.code.sites)

abbrev view (phase : Fin (budget + 1)) : World bound budget := {world with phase := phase}

def Realization (reference : Program bound budget) :
    Synthesis.Outcome bound budget reference → Type
  | .selected choice => (rival : Opponent bound.source.code) →
      Future.Execution (world.source bound budget) (world.input bound budget) world.phase.val rival
        (term bound budget world choice.policy.programme).val
  | .blocked _ => Unit

def LocalityOf (reference : Program bound budget) : Synthesis.Outcome bound budget reference → Prop
  | .selected choice => Synthesis.Locality bound budget choice.policy.rule world
  | .blocked _ => True

structure Disposition (reference : Program bound budget) where
  source_in_cell : world ∈ cell bound budget site (world.observation bound budget site)
  native : Authority.Disposition (world.native bound budget) (world.input bound budget) world.phase.val rfl rfl
  native_exact : native = Authority.generate (world.native bound budget) (world.input bound budget) world.phase.val rfl rfl
  outcome : Synthesis.Outcome bound budget reference
  generated : outcome = Synthesis.compile bound budget reference
  realization : Realization bound budget world reference outcome
  locality : LocalityOf bound budget world reference outcome
  verified_realization : (programme : Synthesis.Rule bound) →
    Synthesis.verify bound budget reference programme = true →
      (rival : Opponent bound.source.code) →
        Future.Execution (world.source bound budget) (world.input bound budget) world.phase.val rival
          (term bound budget world (Synthesis.plan bound budget programme)).val

def generate (reference : Program bound budget) : Disposition bound budget world site reference where
  source_in_cell := (in_cell_iff bound budget site _ world).mpr rfl
  native := Authority.generate (world.native bound budget) (world.input bound budget) world.phase.val rfl rfl
  native_exact := rfl
  outcome := Synthesis.compile bound budget reference
  generated := rfl
  realization := match Synthesis.compile bound budget reference with
    | .selected choice => fun rival => Future.execute (world.source bound budget) (world.input bound budget)
        world.phase.val rival (term bound budget world choice.policy.programme).val rfl rfl
    | .blocked _ => ()
  locality := match Synthesis.compile bound budget reference with
    | .selected choice => Synthesis.actual_emitted_activation_reads_only_that_workers_record bound budget choice.policy.rule world
    | .blocked _ => True.intro
  verified_realization := fun programme _ rival => Future.execute (world.source bound budget) (world.input bound budget)
    world.phase.val rival (term bound budget world (Synthesis.plan bound budget programme)).val rfl rfl

variable (reference : Program bound budget)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (world.source bound budget).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (phase : Fin (budget + 1)) →
    current = (ProgrammeHistory.visitAt (world.source bound budget).input
      ((world.source bound budget).history.length + 2 + phase.val)).current →
        Disposition bound budget (view bound budget world phase) site reference
  project := fun _ {_} _ _ phase _ => generate bound budget (view bound budget world phase) site reference

def root := (Authority.Runtime.root (world.native bound budget) (world.input bound budget) rfl rfl).withProjectionCoface
  (projectionLaw bound budget world site reference)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (world.source bound budget).input) :=
  ⟨ProgrammeSource.V (world.source bound budget).input, root bound budget world site reference,
    ProgrammeHistory.temporalVisit (world.source bound budget).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (world.source bound budget).input) where
  State := Nat
  stateAt := stateAt bound budget world site reference
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (world.source bound budget).input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (world.source bound budget).input first).current =
        (ProgrammeHistory.visitAt (world.source bound budget).input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Authority.Runtime.Face)
  | information

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (world.source bound budget).input) where
  process := process bound budget world site reference
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Authority.Runtime.facade (world.native bound budget) (world.input bound budget) rfl rfl).componentAt
        (Authority.Runtime.facade (world.native bound budget) (world.input bound budget) rfl rfl).seed previous
    | .information => projectionLaw bound budget world site reference
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Authority.Runtime.facade (world.native bound budget) (world.input bound budget) rfl rfl).installationAt
        (Authority.Runtime.facade (world.native bound budget) (world.input bound budget) rfl rfl).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Authority.Runtime.root (world.native bound budget) (world.input bound budget) rfl rfl).toAuthoritativeRoot.source
            (projectionLaw bound budget world site reference))
    | information =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Authority.Runtime.root (world.native bound budget) (world.input bound budget) rfl rfl).toAuthoritativeRoot.source
        (projectionLaw bound budget world site reference)
  projectionAt := fun _ face => match face with
    | .previous previous => (Authority.Runtime.facade (world.native bound budget) (world.input bound budget) rfl rfl).projectionAt
        (Authority.Runtime.facade (world.native bound budget) (world.input bound budget) rfl rfl).seed previous
    | .information => ()

def activated (ordinal : Nat) : LivingRuntimeState (process bound budget world site reference) :=
  (facade bound budget world site reference).seed.advance ordinal

theorem activated_state_is_ordinal (ordinal : Nat) : (activated bound budget world site reference ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated bound budget world site reference ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

def atCut (phase : Fin (budget+1)) :
    Disposition bound budget (view bound budget world phase) site reference :=
  match (facade bound budget world site reference).readoutAt
    (activated bound budget world site reference ((world.source bound budget).history.length+2+phase.val)) .information with
  | .inl actual => actual.2 phase (by
      change (ProgrammeHistory.visitAt (world.source bound budget).input
        (activated bound budget world site reference ((world.source bound budget).history.length+2+phase.val)).state).current = _
      exact congrArg (fun ordinal => (ProgrammeHistory.visitAt (world.source bound budget).input ordinal).current)
        (activated_state_is_ordinal bound budget world site reference _))
  | .inr impossible => nomatch impossible

theorem same_actual_cut_consumes_observation_selection_native_liability_ledger_and_next
    (phase : Fin (budget+1)) :
    let actual := activated bound budget world site reference ((world.source bound budget).history.length+2+phase.val)
    (atCut bound budget world site reference phase).outcome =
        Synthesis.compile bound budget reference ∧
      (atCut bound budget world site reference phase).native.current =
        Native.Authority.fullGenerate (world.native bound budget) ((world.source bound budget).history.length+1+phase.val) ∧
      HEq ((facade bound budget world site reference).readoutAt actual .information)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade bound budget world site reference).process.stateAt
        ((facade bound budget world site reference).process.successor actual.state) := by
  have consumed := (facade bound budget world site reference).readoutAt_factorizes
    (activated bound budget world site reference ((world.source bound budget).history.length+2+phase.val)) .information
  exact ⟨(atCut bound budget world site reference phase).generated,
    (atCut bound budget world site reference phase).native.current_exact,
    consumed.2.2.2.1, consumed.2.2.1, consumed.2.2.2.2⟩

def verifiedTarget (programme : Synthesis.Rule bound)
    (_verified : Synthesis.verify bound budget reference programme = true)
    (rival : Opponent bound.source.code) : Native.Authority.Bound
      (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  {bound with source := Future.target (world.source bound budget) (world.input bound budget) world.phase.val rival (term bound budget world (Synthesis.plan bound budget programme)).val}

def verifiedNext (programme : Synthesis.Rule bound)
    (verified : Synthesis.verify bound budget reference programme = true)
    (rival : Opponent bound.source.code) :=
  Authority.Selection.atCut (verifiedTarget bound budget world reference programme verified rival)
    (Future.takeover (world.source bound budget) (world.input bound budget) world.phase.val rival) rfl rfl (world.phase.val+1)

theorem every_independently_verified_information_planner_owns_its_actual_next
    (programme : Synthesis.Rule bound)
    (verified : Synthesis.verify bound budget reference programme = true)
    (rival : Opponent bound.source.code) :
    let target := verifiedTarget bound budget world reference programme verified rival
    let targetInput := Future.takeover (world.source bound budget) (world.input bound budget) world.phase.val rival
    let actual := Authority.Runtime.activated target targetInput rfl rfl (target.source.history.length+2+(world.phase.val+1))
    (verifiedNext bound budget world reference programme verified rival).feedback.state =
        Residual.run bound.source.code (Residual.scheduleAt (world.source bound budget) world.phase.val
          (term bound budget world (Synthesis.plan bound budget programme)).val) ⟨rival,budget⟩ (world.state bound budget) 1 ∧
      (verifiedNext bound budget world reference programme verified rival).current =
        Native.Authority.fullGenerate target (target.source.history.length+1+(world.phase.val+1)) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (Authority.Runtime.facade target targetInput rfl rfl).process.stateAt
        ((Authority.Runtime.facade target targetInput rfl rfl).process.successor actual.state) := by
  let target := verifiedTarget bound budget world reference programme verified rival
  let targetInput := Future.takeover (world.source bound budget) (world.input bound budget) world.phase.val rival
  have rooted := (Authority.Runtime.facade target targetInput rfl rfl).readoutAt_factorizes
    (Authority.Runtime.activated target targetInput rfl rfl (target.source.history.length+2+(world.phase.val+1))) .responsibilities
  have actual := Future.execute (world.source bound budget) (world.input bound budget) world.phase.val rival
    (term bound budget world (Synthesis.plan bound budget programme)).val rfl rfl
  exact ⟨(verifiedNext bound budget world reference programme verified rival).feedback.state_exact.trans
      (actual.complete_states 1), (verifiedNext bound budget world reference programme verified rival).current_exact,
    rooted.2.2.1,rooted.2.2.2.2⟩


end Runtime


end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information
