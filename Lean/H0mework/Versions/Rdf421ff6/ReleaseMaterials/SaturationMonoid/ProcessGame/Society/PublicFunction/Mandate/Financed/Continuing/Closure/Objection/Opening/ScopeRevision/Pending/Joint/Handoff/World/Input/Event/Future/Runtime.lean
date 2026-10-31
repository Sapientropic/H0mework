import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action) (depth : Nat)

def ordinal := Event.Runtime.ordinal inventory word
def baseRoot := Event.Runtime.root inventory word

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Programme.Completion.I (observed inventory word))).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) (ordinal inventory word)).current → Response inventory word depth
  project := fun _ {_} _ _ _own => Future.respond inventory word depth

def root := (baseRoot inventory word).withProjectionCoface (projectionLaw inventory word depth)

theorem root_is_the_original_response_root :
    (root inventory word depth).toAuthoritativeRoot.toRoot = (baseRoot inventory word).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.Completion.I (observed inventory word))) :=
  ⟨ProgrammeSource.V (Programme.Completion.I (observed inventory word)),root inventory word depth,
    ProgrammeHistory.temporalVisit (Programme.Completion.I (observed inventory word)) index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Programme.Completion.I (observed inventory word))) where
  State := Nat
  stateAt := stateAt inventory word depth
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.Completion.I (observed inventory word))) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) first).current =
        (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Programme.Completion.I (observed inventory word)) currents
  initial := 0
  successorAt := fun index => ⟨index+1,rfl,HEq.rfl⟩

abbrev Face := Sum Event.Runtime.Face Unit

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Programme.Completion.I (observed inventory word))) where
  process := process inventory word depth
  FaceAt := fun _ => Face
  componentAt := fun _state face => match face with
    | .inl previous => (Event.Runtime.facade inventory word).componentAt (Event.Runtime.activated inventory word 0) previous
    | .inr _ => projectionLaw inventory word depth
  installationAt := by
    intro state face
    have inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (baseRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word depth)
    cases face with
    | inl previous => exact ((Event.Runtime.facade inventory word).installationAt (Event.Runtime.activated inventory word 0) previous).trans inherited
    | inr own =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (baseRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word depth)
  projectionAt := fun _state face => match face with
    | .inl previous => (Event.Runtime.facade inventory word).projectionAt (Event.Runtime.activated inventory word 0) previous
    | .inr _ => ()

def activated (index : Nat) : LivingRuntimeState (process inventory word depth) := (facade inventory word depth).seed.advance index

def fromRoot : Response inventory word depth :=
  (projectionLaw inventory word depth).project ()
    (ProgrammeSource.emitted (Programme.Completion.I (observed inventory word))
      (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) (ordinal inventory word)).current) () rfl

theorem consumes_the_generated_joint_response_and_finite_future :
    fromRoot inventory word depth = Future.respond inventory word depth := rfl

theorem raw_generated_next_is_the_original_complete_after :
    ProgrammeSource.rawCurrent (Programme.Completion.I (observed inventory word))
      (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) (ordinal inventory word+1)).current =
      current epoch (Programme.produce (observed inventory word)).finalInventory.inputs :=
  Event.Runtime.raw_generated_next_is_the_original_complete_after inventory word

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Runtime

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action) (depth : Nat)

theorem joint_openness_full_continuation_and_own_next_share_the_actual_root :
    fromRoot inventory word depth = Future.respond inventory word depth ∧
    (fromRoot inventory word depth).result.openness.kind =
      (fromRoot inventory word depth).result.event.original.original.decision.kind ∧
    (fromRoot inventory word depth).continuation.visits.length = depth ∧
    Financial.Family.ledgerClaims sources (fromRoot inventory word depth).continuation.packet.2.finance.current =
      (current (fromRoot inventory word depth).continuation.packet.1 (fromRoot inventory word depth).continuation.packet.2.inputs).claims ∧
    HEq ((facade inventory word depth).readoutAt
      (activated inventory word depth (ordinal inventory word)) (.inr ()))
      ((activated inventory word depth (ordinal inventory word)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (activated inventory word depth (ordinal inventory word)).tick.generated.wholeLedgerWriteBack
      ((activated inventory word depth (ordinal inventory word)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated inventory word depth (ordinal inventory word)).current.visit.current) ∧
    (activated inventory word depth (ordinal inventory word)).tick.nextCurrent =
      (facade inventory word depth).process.stateAt ((facade inventory word depth).process.successor
        (activated inventory word depth (ordinal inventory word)).state) := by
  have factor := (facade inventory word depth).readoutAt_factorizes
    (activated inventory word depth (ordinal inventory word)) (.inr ())
  exact ⟨rfl,(fromRoot inventory word depth).result.openness.classifies_the_actual_decision,
    (fromRoot inventory word depth).continuation.exact_observation_depth,
    (fromRoot inventory word depth).continuation.packet.2.matrix,
    factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩

theorem every_finite_visit_reenters_its_own_joint_root {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) (index : Fin depth) :
    let visit := chain.visit index
    (fromRoot visit.1.2 (ownWord visit.1.2) 0).result = visit.2 ∧
    HEq ((facade visit.1.2 (ownWord visit.1.2) 0).readoutAt
      (activated visit.1.2 (ownWord visit.1.2) 0 (ordinal visit.1.2 (ownWord visit.1.2))) (.inr ()))
      ((activated visit.1.2 (ownWord visit.1.2) 0 (ordinal visit.1.2 (ownWord visit.1.2))).tick.generated.projectionOutcome (.component ())) ∧
    HEq (activated visit.1.2 (ownWord visit.1.2) 0 (ordinal visit.1.2 (ownWord visit.1.2))).tick.generated.wholeLedgerWriteBack
      ((activated visit.1.2 (ownWord visit.1.2) 0 (ordinal visit.1.2 (ownWord visit.1.2))).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated visit.1.2 (ownWord visit.1.2) 0 (ordinal visit.1.2 (ownWord visit.1.2))).current.visit.current) ∧
    (activated visit.1.2 (ownWord visit.1.2) 0 (ordinal visit.1.2 (ownWord visit.1.2))).tick.nextCurrent =
      (facade visit.1.2 (ownWord visit.1.2) 0).process.stateAt ((facade visit.1.2 (ownWord visit.1.2) 0).process.successor
        (activated visit.1.2 (ownWord visit.1.2) 0 (ordinal visit.1.2 (ownWord visit.1.2))).state) := by
  dsimp only
  have factor := (facade (chain.visit index).1.2 (ownWord (chain.visit index).1.2) 0).readoutAt_factorizes
    (activated (chain.visit index).1.2 (ownWord (chain.visit index).1.2) 0 (ordinal (chain.visit index).1.2 (ownWord (chain.visit index).1.2))) (.inr ())
  refine ⟨?_,factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩
  exact (chain.every_visit_is_generated index).symm

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Runtime
