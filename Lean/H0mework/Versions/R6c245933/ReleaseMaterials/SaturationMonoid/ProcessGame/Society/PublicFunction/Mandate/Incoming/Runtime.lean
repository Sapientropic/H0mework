import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.Incoming
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Incoming.Runtime

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (input : BoundSource base scope)

abbrev previousRoot := Lifecycle.Runtime.root input
abbrev previousFacade := Lifecycle.Runtime.facade input

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource input.source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (depth : Nat) → current = (ProgrammeHistory.visitAt input.source.input (depth + 1)).current →
      Option (input.source.ReceivedEvent depth)
  project := fun _ {_} _ _ depth _canonical => input.source.receivedAt depth

def root := (previousRoot input).withProjectionCoface (projectionLaw input)

theorem root_is_the_emitting_source :
    (root input).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot input.source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N input.source.input) :=
  ⟨ProgrammeSource.V input.source.input, root input,
    ProgrammeHistory.temporalVisit input.source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N input.source.input) where
  State := Nat
  stateAt := stateAt input
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N input.source.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt input.source.input first).current =
        (ProgrammeHistory.visitAt input.source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective input.source.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Lifecycle.Runtime.Face input)
  | received

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N input.source.input) where
  process := process input
  FaceAt := fun _ => Face input
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade input).componentAt (previousFacade input).seed previous
    | .received => projectionLaw input
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade input).installationAt (previousFacade input).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (previousRoot input).toAuthoritativeRoot.source (projectionLaw input))
    | received =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface (previousRoot input).toAuthoritativeRoot.source (projectionLaw input)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade input).projectionAt (previousFacade input).seed previous
    | .received => ()

def activated (ordinal : Nat) : LivingRuntimeState (process input) := (facade input).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated input ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem payload_is_received (depth : Nat) :
    (projectionLaw input).project ()
      (ProgrammeSource.emitted input.source.input
        (ProgrammeHistory.visitAt input.source.input (depth + 1)).current) () depth rfl = input.source.receivedAt depth := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Incoming.Runtime
