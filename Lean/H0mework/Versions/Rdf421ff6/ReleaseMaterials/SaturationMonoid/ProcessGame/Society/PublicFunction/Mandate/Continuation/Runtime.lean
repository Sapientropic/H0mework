import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Continuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Incoming.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Continuation.Runtime

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (input : BoundSource base scope)

abbrev previousRoot := Incoming.Runtime.root (bound input)
abbrev previousFacade := Incoming.Runtime.facade (bound input)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source input).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (depth : Nat) → current = (ProgrammeHistory.visitAt (source input).input (depth + 2)).current →
      PublicContinuationDisposition input depth
  project := fun _ {_} _ _ depth _canonical => generate input depth

def root := (previousRoot input).withProjectionCoface (projectionLaw input)

theorem root_is_the_emitting_source :
    (root input).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (source input).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source input).input) :=
  ⟨ProgrammeSource.V (source input).input, root input,
    ProgrammeHistory.temporalVisit (source input).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source input).input) where
  State := Nat
  stateAt := stateAt input
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source input).input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (source input).input first).current =
        (ProgrammeHistory.visitAt (source input).input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (source input).input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Incoming.Runtime.Face (bound input))
  | disposition

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source input).input) where
  process := process input
  FaceAt := fun _ => Face input
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade input).componentAt (previousFacade input).seed previous
    | .disposition => projectionLaw input
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade input).installationAt (previousFacade input).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (previousRoot input).toAuthoritativeRoot.source (projectionLaw input))
    | disposition =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface (previousRoot input).toAuthoritativeRoot.source (projectionLaw input)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade input).projectionAt (previousFacade input).seed previous
    | .disposition => ()

def activated (ordinal : Nat) : LivingRuntimeState (process input) := (facade input).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated input ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem payload_is_generated (depth : Nat) :
    (projectionLaw input).project ()
      (ProgrammeSource.emitted (source input).input
        (ProgrammeHistory.visitAt (source input).input (depth + 2)).current) () depth rfl = generate input depth := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Continuation.Runtime
