import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Classification

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.JointRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {fuel : ℚ} (inventory : Joint.Inventory fuel) (word : List Action)

noncomputable section

abbrev I := TransportRuntime.I inventory.cut word
abbrev previousRoot := TransportRuntime.root inventory.cut word
abbrev previousFacade := TransportRuntime.facade inventory.cut word

structure Disposition where
  private mk ::
  inherited : TransportRuntime.Disposition inventory.cut word
  inherited_exact : inherited = TransportRuntime.generate inventory.cut word
  before : Joint.Frame (Joint.submit inventory word).cut
  before_exact : before = Joint.before inventory word
  after : Joint.Frame (Joint.submit inventory word).cut
  after_exact : after = (Joint.submit inventory word).frame
  carried : (row : Joint.Row inventory.cut) → row ∈ inventory.frame.rows → Joint.Carried inventory word row
  carried_exact : ∀ row inside, carried row inside = Joint.carry inventory word row inside
  newborns : (index : Fin (Joint.actualEvents inventory.cut word).length) →
    Option (Joint.BornAt inventory word index)
  newborns_exact : ∀ index, newborns index = Joint.newbornAt inventory word index
  covered : after.CoversOrigins

def generate : Disposition inventory word :=
  ⟨TransportRuntime.generate inventory.cut word, rfl,
    Joint.before inventory word, rfl, (Joint.submit inventory word).frame, rfl,
    Joint.carry inventory word, fun _ _ => rfl,
    Joint.newbornAt inventory word, fun _ => rfl, (Joint.submit inventory word).covered⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I inventory word)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I inventory word) (inventory.cut.depth + 2)).current → Disposition inventory word
  project := fun _ {_} _ _ _own => generate inventory word

def root := (previousRoot inventory word).withProjectionCoface (projectionLaw inventory word)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I inventory word)) :=
  ⟨ProgrammeSource.V (I inventory word), root inventory word, ProgrammeHistory.temporalVisit (I inventory word) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I inventory word)) where
  State := Nat
  stateAt := stateAt inventory word
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I inventory word)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I inventory word) first).current =
        (ProgrammeHistory.visitAt (I inventory word) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I inventory word) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : TransportRuntime.Face)
  | joint

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I inventory word)) where
  process := process inventory word
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory word).componentAt (previousFacade inventory word).seed previous
    | .joint => projectionLaw inventory word
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade inventory word).installationAt (previousFacade inventory word).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word))
    | joint =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory word).projectionAt (previousFacade inventory word).seed previous
    | .joint => ()

def activated (ordinal : Nat) : LivingRuntimeState (process inventory word) :=
  (facade inventory word).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.JointRuntime
