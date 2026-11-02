import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionCounter

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation
open CompletionState

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (allowance : Nat) (rival : Opponent model.source.code) (scope : Scope) (threshold : Nat)

abbrev tree := CompletionTree.produce model start vocabulary encoding law allowance past
-- Avoid expanding the independent executor while elaborating deep original-root fibres.
@[irreducible] def actual := CompletionExecution.produce model start vocabulary encoding law allowance past rival
abbrev full := BatchReentryRuntime.full model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law
def actualBound := BatchReentryRuntime.actualBound model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law
def ordinal := BatchReentryRuntime.ordinal model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law

structure Census where
  private mk ::
  guaranteed : Bool
  guaranteed_exact : guaranteed = CompletionTree.winning model start vocabulary encoding law allowance (tree model start past vocabulary encoding law allowance)
  deadline : Nat
  deadline_exact : deadline = CompletionTree.height model start vocabulary encoding law allowance (tree model start past vocabulary encoding law allowance)
  counterexample : Option (CompletionExecution.Result model)
  counterexample_exact : counterexample = CompletionCounter.firstFailure model start vocabulary encoding law allowance (tree model start past vocabulary encoding law allowance)
  execution : CompletionExecution.Result model
  execution_exact : execution = actual model start past vocabulary encoding law allowance rival
  parent : BatchReentryRuntime.Census model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law

def generate : Census model start past vocabulary encoding law allowance rival :=
  ⟨CompletionTree.winning model start vocabulary encoding law allowance (tree model start past vocabulary encoding law allowance), rfl,
    CompletionTree.height model start vocabulary encoding law allowance (tree model start past vocabulary encoding law allowance), rfl,
    CompletionCounter.firstFailure model start vocabulary encoding law allowance (tree model start past vocabulary encoding law allowance), rfl,
    actual model start past vocabulary encoding law allowance rival, rfl,
    BatchReentryRuntime.generate model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound model start past vocabulary encoding law allowance rival).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law allowance rival).source.input
      (ordinal model start past vocabulary encoding law allowance rival)).current → Census model start past vocabulary encoding law allowance rival
  project := fun _ {_} _ _ _own => generate model start past vocabulary encoding law allowance rival

def parentRoot := BatchReentryRuntime.root model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law scope threshold
def root := (parentRoot model start past vocabulary encoding law allowance rival scope threshold).withProjectionCoface
  (projectionLaw model start past vocabulary encoding law allowance rival)

theorem original_emitter_root_is_preserved :
    (root model start past vocabulary encoding law allowance rival scope threshold).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (actualBound model start past vocabulary encoding law allowance rival).source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (actualBound model start past vocabulary encoding law allowance rival).source.input) :=
  ⟨ProgrammeSource.V (actualBound model start past vocabulary encoding law allowance rival).source.input,
    root model start past vocabulary encoding law allowance rival scope threshold,
    ProgrammeHistory.temporalVisit (actualBound model start past vocabulary encoding law allowance rival).source.input index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound model start past vocabulary encoding law allowance rival).source.input) where
  State := Nat
  stateAt := stateAt model start past vocabulary encoding law allowance rival scope threshold
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt
        (ProgrammeSource.N (actualBound model start past vocabulary encoding law allowance rival).source.input) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law allowance rival).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law allowance rival).source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun index => ⟨index + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : BatchReentryRuntime.Face)
  | completion

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound model start past vocabulary encoding law allowance rival).source.input) where
  process := process model start past vocabulary encoding law allowance rival scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (BatchReentryRuntime.facade model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law scope threshold).componentAt
        (BatchReentryRuntime.facade model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law scope threshold).seed previous
    | .completion => projectionLaw model start past vocabulary encoding law allowance rival
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((BatchReentryRuntime.facade model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law scope threshold).installationAt
        (BatchReentryRuntime.facade model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law scope threshold).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (parentRoot model start past vocabulary encoding law allowance rival scope threshold).toAuthoritativeRoot.source
          (projectionLaw model start past vocabulary encoding law allowance rival))
    | completion =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (parentRoot model start past vocabulary encoding law allowance rival scope threshold).toAuthoritativeRoot.source
        (projectionLaw model start past vocabulary encoding law allowance rival)
  projectionAt := fun _ face => match face with
    | .previous previous =>
      (BatchReentryRuntime.facade model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law scope threshold).projectionAt
        (BatchReentryRuntime.facade model start (actual model start past vocabulary encoding law allowance rival).state.past vocabulary encoding law scope threshold).seed previous
    | .completion => ()

def activated (index : Nat) : LivingRuntimeState (process model start past vocabulary encoding law allowance rival scope threshold) :=
  (facade model start past vocabulary encoding law allowance rival scope threshold).seed.advance index

theorem activated_state_is_the_generated_ordinal (index : Nat) :
    (activated model start past vocabulary encoding law allowance rival scope threshold index).state = index := by
  induction index with
  | zero => rfl
  | succ index ih =>
    change Nat.succ (activated model start past vocabulary encoding law allowance rival scope threshold index).state = Nat.succ index
    exact congrArg Nat.succ ih

abbrev runtime := activated model start past vocabulary encoding law allowance rival scope threshold (ordinal model start past vocabulary encoding law allowance rival)

def rooted : Census model start past vocabulary encoding law allowance rival :=
  match (facade model start past vocabulary encoding law allowance rival scope threshold).readoutAt
      (runtime model start past vocabulary encoding law allowance rival scope threshold) .completion with
  | .inl value => value.2 (congrArg
      (fun index => (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law allowance rival).source.input index).current)
      (activated_state_is_the_generated_ordinal model start past vocabulary encoding law allowance rival scope threshold
        (ordinal model start past vocabulary encoding law allowance rival)))
  | .inr impossible => nomatch impossible

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionRuntime
