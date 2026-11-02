import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Finance
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Runtime

open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code)
  (active : source.feedback? = some input) (empty : source.continuation = [])

abbrev target (cut : Nat) (position : Repayment.Position Party Instrument)
    (site : Fin source.code.sites) (owner : source.code.siteParty site = position.debtor) :=
  planned source input cut position site owner

variable (cut : Nat) (position : Repayment.Position Party Instrument)
  (site : Fin source.code.sites) (owner : source.code.siteParty site = position.debtor)

structure Disposition where
  proposal : Repayment.Quota.Outcome source.code.law position (source.feedbackState input cut).current
    (support source cut position)
  proposal_exact : proposal = Quota.proposal source input cut position
  bound : amount source input cut position ≤ support source cut position
  prior_state : (target source input cut position site owner).feedbackState input cut = source.feedbackState input cut
  prior_actual : ∀ ordinal, ordinal < source.history.length + 2 + cut →
      (ProgrammeHistory.visitAt (target source input cut position site owner).input ordinal).current =
          (ProgrammeHistory.visitAt source.input ordinal).current ∧
        ProgrammeSource.rawEvent (target source input cut position site owner).input
          (ProgrammeHistory.visitAt (target source input cut position site owner).input ordinal).current =
        ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current
  prior_issue_sources : ∀ ordinal, ordinal ≤ source.history.length + 2 + cut →
      ((Financial.accountAt (target source input cut position site owner).input ordinal).current.slots.map
          (Financial.slotClaim (target source input cut position site owner).input)).map
          (Identity.claimImage source.code (target source input cut position site owner).input) =
        ((Financial.accountAt source.input ordinal).current.slots.map (Financial.slotClaim source.input)).map
          (Identity.claimImage source.code source.input)
  finance_transport : Finance.Outcome source input cut position site owner
  finance_transport_exact : finance_transport = Finance.generate source input cut position site owner
  finance_transport_accepted : finance_transport.accepted = true
  planned_bound : amount source input cut position ≤ support (target source input cut position site owner) cut position
  native : Native.Disposition (target source input cut position site owner) (source.history.length + 1 + cut)
  native_exact : native = Native.generate (target source input cut position site owner) (source.history.length + 1 + cut)

def generate : Disposition source input cut position site owner :=
  ⟨Quota.proposal source input cut position, rfl, amount_is_native_supported source input cut position,
    plan_keeps_the_complete_current_cut source input cut position site owner,
    fun ordinal bounded =>
      source.scheduled_policy_keeps_every_prior_occurrence cut _ ordinal bounded,
    Native.Coupling.Causality.every_prior_original_claim_keeps_its_actual_source source cut _,
    Finance.generate source input cut position site owner, rfl,
    Finance.every_generated_transport_is_supported source input cut position site owner,
    (Finance.generated_support source input cut position site owner).actual_bound,
    Native.generate (target source input cut position site owner) _, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (target source input cut position site owner).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (target source input cut position site owner).input
      (source.history.length + 2 + cut)).current → Disposition source input cut position site owner
  project := fun _ {_} _ _ _own => generate source input cut position site owner

def root := (Feedback.Runtime.root (target source input cut position site owner) input active empty).withProjectionCoface (projectionLaw source input cut position site owner)

theorem original_emitter_root_is_preserved :
    (root source input active empty cut position site owner).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (target source input cut position site owner).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (target source input cut position site owner).input) :=
  ⟨ProgrammeSource.V (target source input cut position site owner).input, root source input active empty cut position site owner, ProgrammeHistory.temporalVisit (target source input cut position site owner).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (target source input cut position site owner).input) where
  State := Nat
  stateAt := stateAt source input active empty cut position site owner
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (target source input cut position site owner).input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (target source input cut position site owner).input first).current =
        (ProgrammeHistory.visitAt (target source input cut position site owner).input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (target source input cut position site owner).input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Feedback.Runtime.Face)
  | quota

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (target source input cut position site owner).input) where
  process := process source input active empty cut position site owner
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Feedback.Runtime.facade (target source input cut position site owner) input active empty).componentAt (Feedback.Runtime.facade (target source input cut position site owner) input active empty).seed previous
    | .quota => projectionLaw source input cut position site owner
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Feedback.Runtime.facade (target source input cut position site owner) input active empty).installationAt (Feedback.Runtime.facade (target source input cut position site owner) input active empty).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Feedback.Runtime.root (target source input cut position site owner) input active empty).toAuthoritativeRoot.source (projectionLaw source input cut position site owner))
    | quota =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Feedback.Runtime.root (target source input cut position site owner) input active empty).toAuthoritativeRoot.source (projectionLaw source input cut position site owner)
  projectionAt := fun _ face => match face with
    | .previous previous => (Feedback.Runtime.facade (target source input cut position site owner) input active empty).projectionAt (Feedback.Runtime.facade (target source input cut position site owner) input active empty).seed previous
    | .quota => ()

def activated (ordinal : Nat) : LivingRuntimeState (process source input active empty cut position site owner) :=
  (facade source input active empty cut position site owner).seed.advance ordinal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Runtime
