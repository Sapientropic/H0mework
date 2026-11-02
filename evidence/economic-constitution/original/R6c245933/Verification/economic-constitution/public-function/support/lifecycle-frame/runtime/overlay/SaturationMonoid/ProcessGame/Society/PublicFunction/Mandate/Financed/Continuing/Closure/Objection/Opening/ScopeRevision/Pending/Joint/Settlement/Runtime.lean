import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Native
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)
  {originInputs : List (List Action)} (inventory : Inventory ready originInputs)
noncomputable section

abbrev I := Settlement.I ready inventory
abbrev nextInventory := Settlement.advance ready inventory

structure Disposition where
  private mk ::
  next : Inventory ready originInputs
  next_exact : next = nextInventory ready inventory
  initial_exact : (I ready inventory).initial = (ScopeRevision.advance old).cut.past.frame.raw
  actual_word : (Settlement.execution ready inventory).submitted = Settlement.emit ready inventory
  actual_before : (Settlement.execution ready inventory).before = current ready inventory.inputs
  actual_after : current ready next.inputs = (epochLaw ready).next (current ready inventory.inputs) (Settlement.emit ready inventory)
  original_prefix : Joint.emit ready inventory <+: Settlement.emit ready inventory
  native : Settlement.Native ready inventory
  native_exact : native = Settlement.native ready inventory
  slices : (index : Fin (positions ready inventory).length) → Slice ready inventory (positions ready inventory)[index]
  slices_exact : ∀ index, slices index = slice ready inventory index
  saved_balances : (afterPrefix ready inventory).claims = Financial.Family.ledgerClaims Finance.sources inventory.finance.current
  financialInstructions : List (Financial.Family.InstructionRecord Finance.sources)
  financialInstructions_exact : financialInstructions = Finance.appendTrace ready inventory.inputs (Settlement.emit ready inventory) inventory.finance

def generate : Disposition ready inventory :=
  ⟨nextInventory ready inventory, rfl, the_new_source_initial_is_the_actual_old_successor ready,
    (Settlement.actual_word_and_cut ready inventory).1, (Settlement.actual_word_and_cut ready inventory).2,
    Settlement.actual_after ready inventory, original_objection_response_is_the_literal_prefix ready inventory,
    Settlement.native ready inventory, rfl, slice ready inventory, fun _ => rfl,
    saved_native_shares_are_the_actual_suffix_balances ready inventory,
    Finance.appendTrace ready inventory.inputs (Settlement.emit ready inventory) inventory.finance, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I ready inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (I ready inventory) (inventory.inputs.length + 2)).current → Disposition ready inventory
  project := fun _ {_} _ _ _own => generate ready inventory

def root := (ProgrammeLiving.livingRoot (I ready inventory)).withProjectionCoface (projectionLaw ready inventory)

theorem root_is_its_own_emitting_source : (root ready inventory).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (I ready inventory)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I ready inventory)) :=
  ⟨ProgrammeSource.V (I ready inventory), root ready inventory, ProgrammeHistory.temporalVisit (I ready inventory) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I ready inventory)) where
  State := Nat
  stateAt := stateAt ready inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I ready inventory)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I ready inventory) first).current =
        (ProgrammeHistory.visitAt (I ready inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I ready inventory) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I ready inventory)) where
  process := process ready inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (I ready inventory)
    | .responsibilities => projectionLaw ready inventory
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (I ready inventory)).toAuthoritativeRoot.source (projectionLaw ready inventory)
    | responsibilities =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (I ready inventory)).toAuthoritativeRoot.source (projectionLaw ready inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process ready inventory) :=
  (facade ready inventory).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime
