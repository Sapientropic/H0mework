import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {seed : Seed} {oldRequests : Requests.Source} {oldMode : Material.Mode} {cut : Nat}
  (previous : Inherited seed oldRequests oldMode cut)
  (requests : Requests.Source) (authority : Authority)

def familyRun (ordinal : Nat) := Financial.Family.continueVisits_run Finance.sources
  (input previous requests authority) (cut + 1) (ordinal + 1) previous.result.account

structure Result (ordinal : Nat) where
  private mk ::
  frame : Frame seed.basis
  frameExact : frame = run previous requests authority (ordinal + 1)
  account : Finance.Account
  accountExact : account = Financial.Family.continueVisits Finance.sources
    (input previous requests authority) (cut + 1) (ordinal + 1) previous.result.account

def result (ordinal : Nat) : Result previous requests authority ordinal :=
  ⟨run previous requests authority (ordinal + 1), rfl,
    Financial.Family.continueVisits Finance.sources (input previous requests authority) (cut + 1)
      (ordinal + 1) previous.result.account, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input previous requests authority)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (ordinal : Nat) →
    current = (ProgrammeHistory.visitAt (input previous requests authority) (cut + 1 + ordinal)).current →
      Result previous requests authority ordinal
  project := fun _ {_} _ _ ordinal _ => result previous requests authority ordinal

def root := (ProgrammeLiving.livingRoot (input previous requests authority)).withProjectionCoface
  (projectionLaw previous requests authority)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input previous requests authority)) :=
  ⟨ProgrammeSource.V (input previous requests authority), root previous requests authority,
    ProgrammeHistory.temporalVisit (input previous requests authority) (cut + 1 + ordinal)⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (input previous requests authority)) where
  State := Nat
  stateAt := stateAt previous requests authority
  stateAt_injective := by
    intro first second same
    have current := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input previous requests authority)) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact Nat.add_left_cancel (ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj current).2))
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where | execution | settlement

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input previous requests authority)) where
  process := process previous requests authority
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (input previous requests authority)
    | .settlement => projectionLaw previous requests authority
  installationAt := by
    intro tick face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw previous requests authority)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw previous requests authority)
  projectionAt := fun _ face => match face with | .execution => .execution | .settlement => ()

def activated (ordinal : Nat) := (facade previous requests authority).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated previous requests authority ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ n prior => exact congrArg Nat.succ prior

def consume (ordinal : Nat) : Result previous requests authority ordinal :=
  match (facade previous requests authority).readoutAt (activated previous requests authority ordinal) .settlement with
  | .inl ⟨_, payload⟩ => payload ordinal (by
    change (ProgrammeHistory.visitAt (input previous requests authority)
      (cut + 1 + (show Nat from (activated previous requests authority ordinal).state))).current = _
    rw [activated_state])
  | .inr impossible => nomatch impossible

def execution (ordinal : Nat) :=
  match (facade previous requests authority).readoutAt (activated previous requests authority ordinal) .execution with
  | .inl ⟨_, payload⟩ => payload
  | .inr impossible => nomatch impossible

theorem the_original_frame_computes_the_exact_material_successor (ordinal : Nat) :
    (consume previous requests authority ordinal).frame =
      runFrom seed requests authority (Resume.run seed oldRequests oldMode (cut + 1)) (ordinal + 1) := by
  rw [(consume previous requests authority ordinal).frameExact, run, previous.result.frameExact]

theorem actual_after_is_the_published_frame (ordinal : Nat) :
    (execution previous requests authority ordinal).after =
      (consume previous requests authority ordinal).frame.raw := by
  rw [(consume previous requests authority ordinal).frameExact]
  change (ProgrammeLiving.executionFace (input previous requests authority)
    (ProgrammeSource.emitted (input previous requests authority)
      (ProgrammeHistory.visitAt (input previous requests authority)
        (cut + 1 + (show Nat from (activated previous requests authority ordinal).state))).current)).after = _
  rw [activated_state]
  exact (ProgrammeLiving.projected_execution_uses_actual_root_next _ _).trans
    (own_current previous requests authority (ordinal + 1))

theorem same_occurrence_whole_ledger_and_own_next (ordinal : Nat) :
    HEq ((facade previous requests authority).readoutAt (activated previous requests authority ordinal) .settlement)
      ((activated previous requests authority ordinal).tick.generated.projectionOutcome
        (((facade previous requests authority).installationAt (activated previous requests authority ordinal) .settlement).embed
          ((facade previous requests authority).projectionAt (activated previous requests authority ordinal) .settlement))) ∧
    HEq (activated previous requests authority ordinal).tick.generated.wholeLedgerWriteBack
      ((activated previous requests authority ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated previous requests authority ordinal).current.visit.current) ∧
    (activated previous requests authority ordinal).tick.nextCurrent =
      (process previous requests authority).stateAt ((process previous requests authority).successor
        (activated previous requests authority ordinal).state) := by
  have same := ((facade previous requests authority).readoutAt_factorizes
    (activated previous requests authority ordinal) .settlement).2
  exact ⟨same.2.2.1, same.2.1, same.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Runtime
