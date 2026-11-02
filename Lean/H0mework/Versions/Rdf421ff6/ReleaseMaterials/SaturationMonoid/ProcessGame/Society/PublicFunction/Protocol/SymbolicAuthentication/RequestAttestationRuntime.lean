import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalJointRuntime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestAttestation

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestAttestationRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code) (scope : Scope) (threshold : Nat)

abbrev result := LocalJointRun.produce model start vocabulary encoding law past
abbrev full := (result model start past vocabulary encoding law).stages
abbrev final := EventHistory.execute start (full model start past vocabulary encoding law)
abbrev actualBound := LocalJointRuntime.actualBound model start past vocabulary encoding law
abbrev ordinal := LocalJointRuntime.ordinal model start past vocabulary encoding law

def generate := RequestAttestation.ledger vocabulary start (full model start past vocabulary encoding law)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound model start past vocabulary encoding law).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
      (ordinal model start past vocabulary encoding law)).current → List (RequestAttestation.Statement (code := model.source.code))
  project := fun _ {_} _ _ _own => generate model start past vocabulary encoding law

-- The new projection extends the same completed source; the prior faces remain installed.
def parentRoot := LocalJointRuntime.root model start past vocabulary encoding law scope threshold

def root := (parentRoot model start past vocabulary encoding law scope threshold).withProjectionCoface
  (projectionLaw model start past vocabulary encoding law)

theorem original_emitter_root_is_preserved :
    (root model start past vocabulary encoding law scope threshold).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (actualBound model start past vocabulary encoding law).source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) :=
  ⟨ProgrammeSource.V (actualBound model start past vocabulary encoding law).source.input,
    root model start past vocabulary encoding law scope threshold,
    ProgrammeHistory.temporalVisit (actualBound model start past vocabulary encoding law).source.input index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) where
  State := Nat
  stateAt := stateAt model start past vocabulary encoding law scope threshold
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt
        (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun index => ⟨index + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : LocalJointRuntime.Face)
  | requests

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) where
  process := process model start past vocabulary encoding law scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (LocalJointRuntime.facade model start past vocabulary encoding law scope threshold).componentAt
        (LocalJointRuntime.facade model start past vocabulary encoding law scope threshold).seed previous
    | .requests => projectionLaw model start past vocabulary encoding law
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((LocalJointRuntime.facade model start past vocabulary encoding law scope threshold).installationAt
        (LocalJointRuntime.facade model start past vocabulary encoding law scope threshold).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (parentRoot model start past vocabulary encoding law scope threshold).toAuthoritativeRoot.source
          (projectionLaw model start past vocabulary encoding law))
    | requests =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (parentRoot model start past vocabulary encoding law scope threshold).toAuthoritativeRoot.source
        (projectionLaw model start past vocabulary encoding law)
  projectionAt := fun _ face => match face with
    | .previous previous => (LocalJointRuntime.facade model start past vocabulary encoding law scope threshold).projectionAt
        (LocalJointRuntime.facade model start past vocabulary encoding law scope threshold).seed previous
    | .requests => ()

def activated (index : Nat) : LivingRuntimeState (process model start past vocabulary encoding law scope threshold) :=
  (facade model start past vocabulary encoding law scope threshold).seed.advance index

theorem activated_state_is_the_generated_ordinal (index : Nat) :
    (activated model start past vocabulary encoding law scope threshold index).state = index := by
  induction index with
  | zero => rfl
  | succ index ih =>
    change Nat.succ (activated model start past vocabulary encoding law scope threshold index).state = Nat.succ index
    exact congrArg Nat.succ ih

abbrev runtime := activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)

def rooted : List (RequestAttestation.Statement (code := model.source.code)) :=
  match (facade model start past vocabulary encoding law scope threshold).readoutAt
      (runtime model start past vocabulary encoding law scope threshold) .requests with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
        (activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

def authority : Feedback.Authority.Disposition (actualBound model start past vocabulary encoding law)
    (final model start past vocabulary encoding law).entry (final model start past vocabulary encoding law).cut rfl rfl :=
  match (facade model start past vocabulary encoding law scope threshold).readoutAt
      (runtime model start past vocabulary encoding law scope threshold) (.previous (.previous .responsibilities)) with
  | .inl value => value.2 (final model start past vocabulary encoding law).cut (by
      change (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
        (activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

def inheritedJoint : LocalJointRuntime.Census model start past vocabulary encoding law scope threshold :=
  match (facade model start past vocabulary encoding law scope threshold).readoutAt
      (runtime model start past vocabulary encoding law scope threshold) (.previous .joint) with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
        (activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem the_original_joint_response_is_inherited_without_reinterpretation :
    inheritedJoint model start past vocabulary encoding law scope threshold =
      LocalJointRuntime.rooted model start past vocabulary encoding law scope threshold := rfl

theorem the_same_root_consumes_complete_requests_original_financial_items_ledger_and_next
    (body : RequestAttestation.Statement (code := model.source.code))
    (inside : body ∈ rooted model start past vocabulary encoding law scope threshold) :
    (∃ row ∈ StageTrace.records start (full model start past vocabulary encoding law), ∃ (position : Nat), ∃ site item,
      StageTrace.activation row = some site ∧ (StageTrace.items row)[position]? = some item ∧
      item ∈ (Financial.inventoryAt (final model start past vocabulary encoding law).source.input
        (ProgrammeHistory.visitAt (final model start past vocabulary encoding law).source.input
          (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? (final model start past vocabulary encoding law).source.input) ∧
      item.request = body.request ∧ RequestAttestation.protocolSyntax item.request = true ∧
      model.source.code.law.Valid item.before item.request ∧ item.request.signer = model.source.code.siteParty site ∧
      body.ballot.fee = flowAt (model.source.code.law.actualDebit item.before item.request)
        (model.source.code.siteParty site) vocabulary.feeUnit ∧ 0 < body.ballot.fee) ∧
    (authority model start past vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate
      (actualBound model start past vocabulary encoding law)
      ((final model start past vocabulary encoding law).source.history.length + 1 + (final model start past vocabulary encoding law).cut) ∧
    HEq ((facade model start past vocabulary encoding law scope threshold).readoutAt
      (runtime model start past vocabulary encoding law scope threshold) .requests)
      ((runtime model start past vocabulary encoding law scope threshold).tick.generated.projectionOutcome (.component ())) ∧
    HEq (runtime model start past vocabulary encoding law scope threshold).tick.generated.wholeLedgerWriteBack
      ((runtime model start past vocabulary encoding law scope threshold).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtime model start past vocabulary encoding law scope threshold).current.visit.current) ∧
    (runtime model start past vocabulary encoding law scope threshold).tick.nextCurrent =
      (facade model start past vocabulary encoding law scope threshold).process.stateAt
        ((facade model start past vocabulary encoding law scope threshold).process.successor
          (runtime model start past vocabulary encoding law scope threshold).state) := by
  have same : rooted model start past vocabulary encoding law scope threshold = generate model start past vocabulary encoding law := rfl
  rw [same] at inside
  obtain ⟨row, present, position, site, item, owned, actual, request, wellFormed, valid, signer, _, _, _, _, _, fee, paid⟩ :=
    RequestAttestation.every_statement_retains_owned_valid_paid_source_and_complete_request vocabulary start
      (full model start past vocabulary encoding law) body inside
  have inventory := StageTrace.final_financial_inventory_is_the_original_record_items start
    (full model start past vocabulary encoding law) row present
  have factor := (facade model start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past vocabulary encoding law scope threshold) .requests
  refine ⟨⟨row, present, position, site, item, owned, actual, ?_, request, wellFormed, valid, signer, fee, paid⟩,
    (authority model start past vocabulary encoding law scope threshold).current_exact,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩
  rw [inventory]
  exact List.mem_of_getElem? actual

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestAttestationRuntime
