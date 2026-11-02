import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Joint

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Runtime

open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (depth : Nat) →
    current = (ProgrammeHistory.visitAt source.input (depth + 1)).current → Disposition source depth
  project := fun _ {_} _ _ depth _own => generate source depth

def root := (Reaction.Runtime.root source).withProjectionCoface (projectionLaw source)

theorem original_root_is_preserved : (root source).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) :=
  ⟨ProgrammeSource.V source.input, root source, ProgrammeHistory.temporalVisit source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N source.input) where
  State := Nat
  stateAt := stateAt source
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt source.input first).current =
        (ProgrammeHistory.visitAt source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective source.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Reaction.Runtime.Face)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N source.input) where
  process := process source
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Reaction.Runtime.facade source).componentAt (Reaction.Runtime.facade source).seed previous
    | .responsibilities => projectionLaw source
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Reaction.Runtime.facade source).installationAt (Reaction.Runtime.facade source).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Reaction.Runtime.root source).toAuthoritativeRoot.source (projectionLaw source))
    | responsibilities =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Reaction.Runtime.root source).toAuthoritativeRoot.source (projectionLaw source)
  projectionAt := fun _ face => match face with
    | .previous previous => (Reaction.Runtime.facade source).projectionAt (Reaction.Runtime.facade source).seed previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process source) := (facade source).seed.advance ordinal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Runtime
