import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

theorem entries_finite (actual : FinancialCurrent seed) :
    Finite (OpenResponsibilityAt (Admission.N seed claim) (support seed claim actual)) :=
  Epoch.Finance.Future.Finiteness.active_finite _
    (Epoch.Finance.Future.Finiteness.active_finite _
      (Public.Accounting.every_current_has_finitely_many_original_open_rows
        seed.input seed.depth seed.count (Background.family seed) actual))

def writes (actual : FinancialCurrent seed) : Bool := !actual.bodyPaid ||
  (Public.Accounting.item? seed.input seed.depth seed.count 0 0 [] (cursor seed claim) actual).isSome

def flow : Abolition.Accounting.Root.Compiler.Flow (Admission.N seed claim) where
  Current := FinancialCurrent seed
  initial := initial seed
  support := support seed claim
  next := next seed claim
  writes := writes seed claim
  evolution := evolution seed claim
  finite := entries_finite seed claim
  injective := fun actual =>
    ⟨Financial.Installation.keys_imply_origin_injective _
        (every_original_key_survives_the_joint_actual_write seed claim actual) (Admission.fibres seed claim),
      Financial.Installation.keys_imply_destination_injective _
        (every_original_key_survives_the_joint_actual_write seed claim actual) (Admission.fibres seed claim)⟩
  open_fibres := Admission.fibres seed claim

abbrev V := Abolition.Accounting.Root.Compiler.V (flow seed claim)
abbrev baseRoot := Abolition.Accounting.Root.Compiler.livingRoot (flow seed claim)

theorem the_source_budget_comes_from_the_actual_native_inventory :
    (Execution.Selected.items seed claim).length =
      ((actualLaw seed).rawItems (Material.shared seed claim).raw (Material.word seed claim)).length := by
  have same := congrArg List.length
    (Execution.Selected.the_native_items_are_the_literal_original_source_inventory seed claim)
  simpa only [List.length_map,Execution.Selected.word] using same

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
