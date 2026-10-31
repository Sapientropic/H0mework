import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable (fuel : ℚ) (inputs : List (List Action))

structure ActualStep (depth : Nat) where
  private mk ::
  observed : inputs.length ≤ depth
  head : Step (Cut.at (fuel := fuel) (inputs := inputs) depth observed)
  generated : head = step (Cut.at depth observed)

noncomputable section

def actualAt (depth : Nat) : Option (ActualStep fuel inputs depth) :=
  if observed : inputs.length ≤ depth then some ⟨observed, step (Cut.at depth observed), rfl⟩ else none

theorem every_cut_has_its_own_actual_head (cut : Cut fuel inputs) :
    ∃ receipt, actualAt fuel inputs cut.depth = some receipt ∧ HEq receipt.head (step cut) := by
  rcases cut with ⟨depth, observed, past, actual⟩
  cases actual
  exact ⟨⟨observed, step (Cut.at depth observed), rfl⟩, by rw [actualAt, dif_pos observed], HEq.rfl⟩

abbrev previousRoot := Continuing.Runtime.root fuel inputs
abbrev previousFacade := Continuing.Runtime.facade fuel inputs

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input fuel inputs)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (depth : Nat) →
    current = (ProgrammeHistory.visitAt (input fuel inputs) (depth + 2)).current → Option (ActualStep fuel inputs depth)
  project := fun _ {_} _ _ depth _own => actualAt fuel inputs depth

def root := (previousRoot fuel inputs).withProjectionCoface (projectionLaw fuel inputs)

theorem root_is_the_same_emitting_source : (root fuel inputs).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (input fuel inputs)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input fuel inputs)) :=
  ⟨ProgrammeSource.V (input fuel inputs), root fuel inputs, ProgrammeHistory.temporalVisit (input fuel inputs) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (input fuel inputs)) where
  State := Nat
  stateAt := stateAt fuel inputs
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input fuel inputs)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (input fuel inputs) first).current =
        (ProgrammeHistory.visitAt (input fuel inputs) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (input fuel inputs) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Continuing.Runtime.Face)
  | continuation

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input fuel inputs)) where
  process := process fuel inputs
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade fuel inputs).componentAt (previousFacade fuel inputs).seed previous
    | .continuation => projectionLaw fuel inputs
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade fuel inputs).installationAt (previousFacade fuel inputs).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot fuel inputs).toAuthoritativeRoot.source (projectionLaw fuel inputs))
    | continuation =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot fuel inputs).toAuthoritativeRoot.source (projectionLaw fuel inputs)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade fuel inputs).projectionAt (previousFacade fuel inputs).seed previous
    | .continuation => ()

def activated (ordinal : Nat) : LivingRuntimeState (process fuel inputs) := (facade fuel inputs).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated fuel inputs ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem payload_is_current_actual_head (depth : Nat) :
    (projectionLaw fuel inputs).project ()
      (ProgrammeSource.emitted (input fuel inputs) (ProgrammeHistory.visitAt (input fuel inputs) (depth + 2)).current)
      () depth rfl = actualAt fuel inputs depth := rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime
