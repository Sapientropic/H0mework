import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action)

abbrev observed := Event.observed (produce inventory word).finish.saved []
abbrev I := Programme.Completion.I (observed inventory word)
abbrev ordinal := Replacement.Runtime.ordinal (observed inventory word)
abbrev baseRoot := Replacement.Runtime.root (observed inventory word)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I inventory word)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I inventory word) (ordinal inventory word)).current →
      Trace inventory word (begin inventory word)
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

abbrev Face := Sum Replacement.Runtime.Face Unit
def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I inventory word)) where
  process := process inventory word
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .inl old => (Replacement.Runtime.facade (observed inventory word)).componentAt
        (Replacement.Runtime.facade (observed inventory word)).seed old
    | .inr _ => projectionLaw inventory word
  installationAt := by
    intro _ face
    cases face with
    | inl old =>
        exact ((Replacement.Runtime.facade (observed inventory word)).installationAt
          (Replacement.Runtime.facade (observed inventory word)).seed old).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (baseRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word))
    | inr _ =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (baseRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word)
  projectionAt := fun _ face => match face with
    | .inl old => (Replacement.Runtime.facade (observed inventory word)).projectionAt
        (Replacement.Runtime.facade (observed inventory word)).seed old
    | .inr _ => ()

abbrev activated := (facade inventory word).seed.advance (ordinal inventory word)
theorem activated_state : (activated inventory word).state = ordinal inventory word := by
  have all (n : Nat) : ((facade inventory word).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Trace inventory word (begin inventory word) :=
  match (facade inventory word).readoutAt (activated inventory word) (.inr ()) with
  | .inl actual => actual.2 (by
      change (ProgrammeHistory.visitAt (I inventory word) (activated inventory word).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem read_exact : read inventory word = produce inventory word := rfl

theorem the_original_root_consumes_the_repairs_all_responsibilities_and_its_own_next :
    let active := activated inventory word
    (read inventory word).finish.consumed ++ (read inventory word).finish.residual = pending inventory word ∧
    Nonempty (Event.Evolution ⟨epoch,inventory⟩ (packet inventory word)) ∧
    Nonempty ((Financial.Family.process sources).Run inventory.finance.current (packet inventory word).2.finance.current) ∧
    HEq ((facade inventory word).readoutAt active (.inr ()))
      (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (facade inventory word).process.stateAt ((facade inventory word).process.successor active.state) := by
  have rooted := (facade inventory word).readoutAt_factorizes (activated inventory word) (.inr ())
  exact ⟨all_original_refused_positions_are_preserved inventory word,⟨evolution inventory word⟩,
    ⟨financialRun inventory word⟩,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Runtime
