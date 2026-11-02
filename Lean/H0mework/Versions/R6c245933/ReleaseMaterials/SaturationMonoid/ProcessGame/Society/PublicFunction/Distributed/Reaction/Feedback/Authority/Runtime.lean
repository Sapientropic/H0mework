import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Runtime

open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code)
  (active : bound.source.feedback? = some input) (empty : bound.source.continuation = [])

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource bound.source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (index : Nat) →
    current = (ProgrammeHistory.visitAt bound.source.input (bound.source.history.length + 2 + index)).current →
      Authority.Disposition bound input index active empty
  project := fun _ {_} _ _ index _own => Authority.generate bound input index active empty

def root := (Feedback.Runtime.root bound.source input active empty).withProjectionCoface (projectionLaw bound input active empty)

theorem original_emitter_root_is_preserved :
    (root bound input active empty).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot bound.source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N bound.source.input) :=
  ⟨ProgrammeSource.V bound.source.input, root bound input active empty, ProgrammeHistory.temporalVisit bound.source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N bound.source.input) where
  State := Nat
  stateAt := stateAt bound input active empty
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N bound.source.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt bound.source.input first).current =
        (ProgrammeHistory.visitAt bound.source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective bound.source.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Feedback.Runtime.Face)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N bound.source.input) where
  process := process bound input active empty
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Feedback.Runtime.facade bound.source input active empty).componentAt (Feedback.Runtime.facade bound.source input active empty).seed previous
    | .responsibilities => projectionLaw bound input active empty
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Feedback.Runtime.facade bound.source input active empty).installationAt (Feedback.Runtime.facade bound.source input active empty).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Feedback.Runtime.root bound.source input active empty).toAuthoritativeRoot.source (projectionLaw bound input active empty))
    | responsibilities =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Feedback.Runtime.root bound.source input active empty).toAuthoritativeRoot.source (projectionLaw bound input active empty)
  projectionAt := fun _ face => match face with
    | .previous previous => (Feedback.Runtime.facade bound.source input active empty).projectionAt (Feedback.Runtime.facade bound.source input active empty).seed previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process bound input active empty) :=
  (facade bound input active empty).seed.advance ordinal

theorem activated_state_is_the_generated_ordinal (ordinal : Nat) :
    (activated bound input active empty ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated bound input active empty ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Runtime
