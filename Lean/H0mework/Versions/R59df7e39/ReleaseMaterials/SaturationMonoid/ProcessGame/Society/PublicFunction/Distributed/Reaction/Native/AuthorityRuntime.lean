import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Mandate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.AuthorityRuntime

open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource bound.source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (depth : Nat) →
    current = (ProgrammeHistory.visitAt bound.source.input (depth + 1)).current → Authority.Disposition bound depth
  project := fun _ {_} _ _ depth _own => Authority.generate bound depth

def root := (Native.Runtime.root bound.source).withProjectionCoface (projectionLaw bound)

theorem original_root_is_preserved : (root bound).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot bound.source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N bound.source.input) :=
  ⟨ProgrammeSource.V bound.source.input, root bound, ProgrammeHistory.temporalVisit bound.source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N bound.source.input) where
  State := Nat
  stateAt := stateAt bound
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
  | previous (face : Native.Runtime.Face)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N bound.source.input) where
  process := process bound
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.Runtime.facade bound.source).componentAt (Native.Runtime.facade bound.source).seed previous
    | .responsibilities => projectionLaw bound
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Native.Runtime.facade bound.source).installationAt (Native.Runtime.facade bound.source).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Native.Runtime.root bound.source).toAuthoritativeRoot.source (projectionLaw bound))
    | responsibilities =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Native.Runtime.root bound.source).toAuthoritativeRoot.source (projectionLaw bound)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.Runtime.facade bound.source).projectionAt (Native.Runtime.facade bound.source).seed previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process bound) := (facade bound).seed.advance ordinal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.AuthorityRuntime
