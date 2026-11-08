import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Root
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable (lane : Lane) (state : State)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input lane state.origin.scope state.raw)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (ordinal : Nat) →
    current=(ProgrammeHistory.visitAt (input lane state.origin.scope state.raw) ordinal).current →
    ordinal=1 → State
  project := fun _ {_} _ _ _ _ _ => Settlement.next lane state

def root := (ProgrammeLiving.livingRoot (input lane state.origin.scope state.raw)).withProjectionCoface (projectionLaw lane state)
def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input lane state.origin.scope state.raw)) :=
  ⟨ProgrammeSource.V (input lane state.origin.scope state.raw),root lane state,
   ProgrammeHistory.temporalVisit (input lane state.origin.scope state.raw) ordinal⟩
def process : SourceNativeLivingRootProcess (ProgrammeSource.N (input lane state.origin.scope state.raw)) where
  State := Nat
  stateAt := stateAt lane state
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input lane state.origin.scope state.raw)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun n => ⟨n+1,rfl,HEq.rfl⟩

inductive Face where | execution | accounts

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input lane state.origin.scope state.raw)) where
  process := process lane state
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (input lane state.origin.scope state.raw)
    | .accounts => projectionLaw lane state
  installationAt := by
    intro tick face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw lane state)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw lane state)
  projectionAt := fun _ face => match face with | .execution => .execution | .accounts => ()

def activated := (facade lane state).seed.advance 1

def next : State :=
  match (facade lane state).readoutAt (activated lane state) .accounts with
  | .inl ⟨_,payload⟩ => payload 1 rfl rfl
  | .inr impossible => nomatch impossible

theorem consumes_the_actual_whole_carrier : next lane state=Settlement.next lane state := rfl

theorem accounts_share_the_same_whole_ledger_and_actual_next :
    HEq ((facade lane state).readoutAt (activated lane state) .accounts)
      ((activated lane state).tick.generated.projectionOutcome
        (((facade lane state).installationAt (activated lane state) .accounts).embed
          ((facade lane state).projectionAt (activated lane state) .accounts))) ∧
    HEq (activated lane state).tick.generated.wholeLedgerWriteBack
      ((activated lane state).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated lane state).current.visit.current) ∧
    (activated lane state).tick.nextCurrent=
      (process lane state).stateAt ((process lane state).successor (activated lane state).state) := by
  have same := ((facade lane state).readoutAt_factorizes (activated lane state) .accounts).2
  exact ⟨same.2.2.1,same.2.1,same.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Root
