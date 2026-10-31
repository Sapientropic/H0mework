import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.NativeServiceHistory

/-! Install the generated native task history as a dependent coface of the
same programme occurrence. A canonical-visit equality only selects the
history restriction; it supplies no lifecycle target or settlement witness.
The source, ledger compiler, law epoch, and raw successors are unchanged.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.NativeService.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource source.input).restructuringSource.toLedgerSource where
  Projection := source.Slot
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun index {current} _ _ =>
    (depth : Nat) → current = (ProgrammeHistory.visitAt source.input (depth + 1)).current →
      Prefix source index (depth + 1)
  project := fun index {_} _ _ depth _canonical => historyAt source index (depth + 1)

def root := (ProgrammeLiving.livingRoot source.input).withProjectionCoface (projectionLaw source)

theorem original_source_is_preserved :
    (root source).toAuthoritativeRoot.toRoot =
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
        (ProgrammeHistory.visitAt source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective source.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | ledger | execution | consumer | inquiry
  | service (index : source.Slot)

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N source.input) where
  process := process source
  FaceAt := fun _ => Face source
  componentAt := fun _ face => match face with
    | .service _ => projectionLaw source
    | _ => ProgrammeLiving.projectionLaw source.input
  installationAt := by
    intro state face
    cases face <;> first
      | exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.authoritySource source.input) (projectionLaw source)
      | exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.authoritySource source.input) (projectionLaw source)
  projectionAt := fun _ face => match face with
    | .ledger => .ledger
    | .execution => .execution
    | .consumer => .consumer
    | .inquiry => .inquiry
    | .service index => index

def activated (ordinal : Nat) : LivingRuntimeState (process source) :=
  (facade source).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated source ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem service_readout_is_original_restriction (index : source.Slot) (depth : Nat) :
    HEq ((facade source).readoutAt (activated source (depth + 1)) (.service index))
      ((projectionLaw source).outcomeAt index
        (ProgrammeSource.emitted source.input
          (ProgrammeHistory.visitAt source.input (depth + 1)).current)) := by
  change HEq ((projectionLaw source).outcomeAt index
    (ProgrammeSource.emitted source.input
      (ProgrammeHistory.visitAt source.input (activated source (depth + 1)).state).current)) _
  rw [activated_state]

theorem service_payload_generates_native_history (index : source.Slot) (depth : Nat) :
    (projectionLaw source).project index
        (ProgrammeSource.emitted source.input
          (ProgrammeHistory.visitAt source.input (depth + 1)).current) () depth rfl =
      historyAt source index (depth + 1) := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.NativeService.Runtime
