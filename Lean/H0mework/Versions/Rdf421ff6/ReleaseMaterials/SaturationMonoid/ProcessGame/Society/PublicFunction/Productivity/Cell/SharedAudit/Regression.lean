import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit

open Institutions.Capitalism.Universal.Source.Program

def noAuditLabor : Current :=
  { (frameAt 4).raw with stock := fun actor good =>
      if actor = 0 ∧ good = .labor then 0 else (frameAt 4).raw.stock actor good }

def noSecondSeed : Current :=
  { (frameAt 7).raw with stock := fun actor good =>
      if actor = 0 ∧ good = .seed then 0 else (frameAt 7).raw.stock actor good }

theorem audit_without_actual_payment_does_not_generate_the_method :
    (compile noAuditLabor).isNone = true := by
  decide +kernel

theorem a_paid_method_cannot_manufacture_missing_seed :
    (respond noSecondSeed (some originalMethod)).word.isEmpty = true := by
  decide +kernel

theorem explicitly_missing_cache_pays_the_fresh_audit :
    (respond (frameAt 7).raw none).word.length = 3 ∧
      (respond (frameAt 7).raw (some originalMethod)).word.length = 2 ∧
      law.totalDebit (law.rawItems (frameAt 7).raw (respond (frameAt 7).raw none).word) 0 .labor = 1 ∧
      law.totalDebit (law.rawItems (frameAt 7).raw (respond (frameAt 7).raw (some originalMethod)).word) 0 .labor = 0 := by
  decide +kernel

theorem strict_saving_does_not_remove_a_material_or_financial_unit :
    (source.currentAt 11).stock 0 .waste = (Cell.source.currentAt 11).stock 0 .waste ∧
      (source.currentAt 11).stock 0 .feed = (Cell.source.currentAt 11).stock 0 .feed ∧
      (source.currentAt 11).claims = (Cell.source.currentAt 11).claims :=
  ⟨all_physical_goods_except_saved_labor_are_identical 0 .waste (by right; decide),
    all_physical_goods_except_saved_labor_are_identical 0 .feed (by right; decide), same_all_financial_positions⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
