import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Replay

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.ReplayRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)
  (stable : Stable seed.code.law) (words : List (RawEvent Party Good Port Technology Instrument))
  (accepted : LegalHistory seed.code.law (terminal seed.code seed.reference seed.history seed.opponent) words)

abbrev source := Replay.replacement seed feasible words
abbrev oldSource := Replay.original seed words
abbrev previousFacade := Runtime.facade (seed.withContinuation words) feasible stable
abbrev previousRoot := Runtime.root (seed.withContinuation words) feasible stable

structure Disposition (count : Nat) where
  private mk ::
  newNative : Native.Disposition (source seed feasible words) (seed.history.length + count)
  new_exact : newNative = Native.generate (source seed feasible words) (seed.history.length + count)
  oldNative : Native.Disposition (oldSource seed words) (seed.history.length + count)
  old_exact : oldNative = Native.generate (oldSource seed words) (seed.history.length + count)
  full_carrier : (source seed feasible words).currentAt (seed.history.length + 2 + count) =
    ((oldSource seed words).currentAt (seed.history.length + 2 + count)).addReserve
      (reserve seed.code (selection seed feasible).policy.policy seed.reference seed.history seed.opponent)

def generate (count : Nat) (bounded : count ≤ words.length) : Disposition seed feasible words count :=
  ⟨Native.generate (source seed feasible words) _, rfl, Native.generate (oldSource seed words) _, rfl,
    Replay.every_actual_cut_keeps_the_full_original_carrier seed feasible stable words accepted count bounded⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source seed feasible words).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (count : Nat) → count ≤ words.length →
    current = (ProgrammeHistory.visitAt (source seed feasible words).input (seed.history.length + 1 + count)).current →
      Disposition seed feasible words count
  project := fun _ {_} _ _ count bounded _own => generate seed feasible stable words accepted count bounded

def root := (previousRoot seed feasible stable words).withProjectionCoface (projectionLaw seed feasible stable words accepted)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source seed feasible words).input) :=
  ⟨ProgrammeSource.V (source seed feasible words).input, root seed feasible stable words accepted,
    ProgrammeHistory.temporalVisit (source seed feasible words).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source seed feasible words).input) where
  State := Nat
  stateAt := stateAt seed feasible stable words accepted
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source seed feasible words).input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (source seed feasible words).input first).current =
        (ProgrammeHistory.visitAt (source seed feasible words).input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (source seed feasible words).input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where | previous (face : Runtime.Face) | replay

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source seed feasible words).input) where
  process := process seed feasible stable words accepted
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade seed feasible stable words).componentAt (previousFacade seed feasible stable words).seed previous
    | .replay => projectionLaw seed feasible stable words accepted
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((previousFacade seed feasible stable words).installationAt (previousFacade seed feasible stable words).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (previousRoot seed feasible stable words).toAuthoritativeRoot.source (projectionLaw seed feasible stable words accepted))
    | replay =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (previousRoot seed feasible stable words).toAuthoritativeRoot.source (projectionLaw seed feasible stable words accepted)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade seed feasible stable words).projectionAt (previousFacade seed feasible stable words).seed previous
    | .replay => ()

def activated (ordinal : Nat) : LivingRuntimeState (process seed feasible stable words accepted) :=
  (facade seed feasible stable words accepted).seed.advance ordinal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.ReplayRuntime
