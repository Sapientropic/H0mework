import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Basic
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def state (history : List (Compile.RawInput Party Good Port Technology Instrument)) :=
  Physical.Public.stateAt input depth count 0 0 [] history

def start (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument) :=
  Physical.receive (Physical.Prefix.cursor history) (.primitive request)

def tag (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument) : Epoch.Interface.Tag input depth count :=
  .publicActual 0 0 [] (start history request)

def visit (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument) :=
  (Epoch.Interface.root input depth count (tag input depth count history request)).initialVisit

def oneItems (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument) :=
  Epoch.Finance.inventory input depth count (tag input depth count history request) (visit input depth count history request)

def events : List (Compile.RawInput Party Good Port Technology Instrument) →
    RawEvent Party Good Port Technology Instrument → List (Epoch.Finance.ActualItem input depth count)
  | _, [] => []
  | history, request :: tail => oneItems input depth count history request ++ events (history ++ [.primitive request]) tail

theorem this_primitive_has_the_literal_original_public_execution
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument) :
    Epoch.Interface.execution input depth count (tag input depth count history request)
        (visit input depth count history request).current =
      (Physical.Public.compile input (state input depth count history) (.primitive request)).execution := by
  change (Physical.Public.compile input
    (Physical.Public.stateAt input depth count 0 0 [] (Physical.Prefix.cursor history).past) (.primitive request)).execution = _
  rw [Physical.Prefix.past_readback]
  rfl

theorem one_checked_source_primitive_generates_its_own_original_native_inventory
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument) (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter input).Valid (state input depth count history).raw request) :
    (oneItems input depth count history request).map (Epoch.Finance.ActualItem.instruction input depth count) =
      [⟨0,(state input depth count history).raw,request⟩] :=
  (Epoch.Finance.inventory_is_exact input depth count (tag input depth count history request) (visit input depth count history request)).trans
    ((congrArg ExecutionResult.items (this_primitive_has_the_literal_original_public_execution input depth count history request)).trans
      (one_checked_original_primitive_has_one_actual_material_step input _ request noConsents valid).2.1)

theorem every_item_of_this_primitive_reads_its_source_interpreter
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument)
    (item : Epoch.Finance.ActualItem input depth count) (listed : item ∈ oneItems input depth count history request) :
    item.interpreter input depth count = Physical.Public.interpreter input := by
  obtain ⟨position,rfl⟩ := List.mem_ofFn.mp listed
  rfl

theorem every_item_of_this_checked_primitive_is_actual
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument) (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter input).Valid (state input depth count history).raw request)
    (item : Epoch.Finance.ActualItem input depth count) (listed : item ∈ oneItems input depth count history request) :
    (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request := by
  rw [every_item_of_this_primitive_reads_its_source_interpreter input depth count history request item listed]
  have original : item.instruction input depth count ∈
      (oneItems input depth count history request).map (Epoch.Finance.ActualItem.instruction input depth count) :=
    List.mem_map.mpr ⟨item,listed,rfl⟩
  rw [one_checked_source_primitive_generates_its_own_original_native_inventory input depth count history request noConsents valid] at original
  rw [List.mem_singleton.mp original]
  exact valid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
