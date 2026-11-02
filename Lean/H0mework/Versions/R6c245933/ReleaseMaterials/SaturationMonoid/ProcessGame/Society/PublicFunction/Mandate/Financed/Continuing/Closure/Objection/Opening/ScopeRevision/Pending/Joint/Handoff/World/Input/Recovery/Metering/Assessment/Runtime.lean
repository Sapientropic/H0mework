import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action)

def produce := Assessment.produce inventory word
abbrev I := Metering.Runtime.I inventory word
abbrev ordinal := Metering.Runtime.ordinal inventory word
abbrev baseRoot := Metering.Runtime.root inventory word

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I inventory word)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I inventory word) (ordinal inventory word)).current →
      Report inventory word
  project := fun _ {_} _ _ _own => produce inventory word

def root := (baseRoot inventory word).withProjectionCoface (projectionLaw inventory word)

theorem retains_the_actual_response_root :
    (root inventory word).toAuthoritativeRoot.toRoot =
      (baseRoot inventory word).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I inventory word)) :=
  ⟨ProgrammeSource.V _,root inventory word,ProgrammeHistory.temporalVisit _ index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I inventory word)) where
  State := Nat
  stateAt := stateAt inventory word
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I inventory word)) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective (I inventory word) (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun index => ⟨index+1,rfl,HEq.rfl⟩

abbrev Face := Sum Metering.Runtime.Face Unit
def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I inventory word)) where
  process := process inventory word
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .inl old => (Metering.Runtime.facade inventory word).componentAt
        (Metering.Runtime.facade inventory word).seed old
    | .inr _ => projectionLaw inventory word
  installationAt := by
    intro _ face
    cases face with
    | inl old =>
        exact ((Metering.Runtime.facade inventory word).installationAt
          (Metering.Runtime.facade inventory word).seed old).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (baseRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word))
    | inr _ =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (baseRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word)
  projectionAt := fun _ face => match face with
    | .inl old => (Metering.Runtime.facade inventory word).projectionAt
        (Metering.Runtime.facade inventory word).seed old
    | .inr _ => ()

abbrev activated := (facade inventory word).seed.advance (ordinal inventory word)
theorem activated_state : (activated inventory word).state = ordinal inventory word := by
  have all (n : Nat) : ((facade inventory word).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Report inventory word :=
  match (facade inventory word).readoutAt (activated inventory word) (.inr ()) with
  | .inl actual => actual.2 (by
      change (ProgrammeHistory.visitAt (I inventory word) (activated inventory word).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem read_exact : read inventory word = produce inventory word := rfl

theorem the_original_billed_root_reads_the_complete_source_report_and_own_next :
    (read inventory word).staged = Metering.Runtime.read inventory word ∧
    (read inventory word).packet = Metering.Runtime.packet inventory word ∧
    HEq ((facade inventory word).readoutAt (activated inventory word) (.inr ()))
      ((activated inventory word).tick.generated.projectionOutcome (.component ())) ∧
    HEq (activated inventory word).tick.generated.wholeLedgerWriteBack
      ((activated inventory word).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated inventory word).current.visit.current) ∧
    (activated inventory word).tick.nextCurrent = (facade inventory word).process.stateAt
      ((facade inventory word).process.successor (activated inventory word).state) := by
  have rooted := (facade inventory word).readoutAt_factorizes (activated inventory word) (.inr ())
  exact ⟨(read inventory word).generated,(read inventory word).is_the_original_billed_response,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Runtime
