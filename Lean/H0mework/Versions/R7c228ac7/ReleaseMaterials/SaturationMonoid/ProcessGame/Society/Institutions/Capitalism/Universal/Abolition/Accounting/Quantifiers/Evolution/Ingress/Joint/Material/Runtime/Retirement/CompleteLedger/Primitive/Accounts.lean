import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open private consumeItems consumeItems_run from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

def accountAfter : List (Compile.RawInput Party Good Port Technology Instrument) →
    RawEvent Party Good Port Technology Instrument → (Epoch.Finance.process input depth count).GeneratedState →
      (Epoch.Finance.process input depth count).GeneratedState
  | _, [], before => before
  | history, request :: tail, before => accountAfter (history ++ [.primitive request]) tail
      (Epoch.Finance.consumeVisit input depth count (tag input depth count history request)
        (visit input depth count history request) before)

private theorem consumeItems_append (first second : List (Epoch.Finance.ActualItem input depth count))
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    consumeItems input depth count (first ++ second) before =
      consumeItems input depth count second (consumeItems input depth count first before) := by
  induction first generalizing before with
  | nil => rfl
  | cons item tail ih => exact ih _

theorem the_actual_sequential_native_account_is_the_same_original_item_fold
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (word : RawEvent Party Good Port Technology Instrument)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    accountAfter input depth count history word before = consumeItems input depth count (events input depth count history word) before := by
  induction word generalizing history before with
  | nil => rfl
  | cons request tail ih =>
      change accountAfter input depth count (history ++ [.primitive request]) tail
          (Epoch.Finance.consumeVisit input depth count (tag input depth count history request) (visit input depth count history request) before) =
        consumeItems input depth count (oneItems input depth count history request ++ events input depth count (history ++ [.primitive request]) tail) before
      rw [consumeItems_append]
      exact ih _ _

def actualNativeRun (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (word : RawEvent Party Good Port Technology Instrument)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    (Epoch.Finance.process input depth count).Run before.current (accountAfter input depth count history word before).current := by
  rw [the_actual_sequential_native_account_is_the_same_original_item_fold]
  exact consumeItems_run input depth count _ before

theorem every_actual_primitive_keeps_the_entire_previous_native_history
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (word : RawEvent Party Good Port Technology Instrument)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    before.current.history <+: (accountAfter input depth count history word before).current.history := by
  rw [(actualNativeRun input depth count history word before).history_eq]
  exact List.prefix_append _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
