import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.ObjectionRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs) (word : List Action)

noncomputable section

abbrev I := TransportRuntime.I cut word
abbrev previousRoot := TransportRuntime.root cut word
abbrev previousFacade := TransportRuntime.facade cut word

structure Disposition where
  private mk ::
  inherited : TransportRuntime.Disposition cut word
  inherited_exact : inherited = TransportRuntime.generate cut word
  objections : List (Sigma fun claim : Objection.Claim fuel (branchInputs cut word) =>
    Objection.History fuel (branchInputs cut word) claim)
  objections_exact : objections = Objection.recordsAt fuel (branchInputs cut word) (cut.depth + 3)

def generate : Disposition cut word :=
  ⟨TransportRuntime.generate cut word, rfl,
    Objection.recordsAt fuel (branchInputs cut word) (cut.depth + 3), rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I cut word)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I cut word) (cut.depth + 2)).current → Disposition cut word
  project := fun _ {_} _ _ _own => generate cut word

def root := (previousRoot cut word).withProjectionCoface (projectionLaw cut word)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I cut word)) :=
  ⟨ProgrammeSource.V (I cut word), root cut word, ProgrammeHistory.temporalVisit (I cut word) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I cut word)) where
  State := Nat
  stateAt := stateAt cut word
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I cut word)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I cut word) first).current =
        (ProgrammeHistory.visitAt (I cut word) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I cut word) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : TransportRuntime.Face)
  | objection

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I cut word)) where
  process := process cut word
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade cut word).componentAt (previousFacade cut word).seed previous
    | .objection => projectionLaw cut word
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade cut word).installationAt (previousFacade cut word).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot cut word).toAuthoritativeRoot.source (projectionLaw cut word))
    | objection =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot cut word).toAuthoritativeRoot.source (projectionLaw cut word)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade cut word).projectionAt (previousFacade cut word).seed previous
    | .objection => ()

def activated (ordinal : Nat) : LivingRuntimeState (process cut word) :=
  (facade cut word).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.ObjectionRuntime
