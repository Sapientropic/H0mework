import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Contract

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit

open Institutions.Capitalism.Universal.Source.Program

theorem actual_full_prefix_passes_floor_check : floorCheck 19 = true := by
  decide +kernel

def actualCertificate : Certificate 19 := certifyCheckedPrefix 19 (by decide) actual_full_prefix_passes_floor_check

theorem actual_full_prefix_is_certified : generate 19 = .certified actualCertificate :=
  checked_prefix_is_certified 19 (by decide) actual_full_prefix_passes_floor_check

def isService (item : ExecutionItem Party Good Port Technology Unit) : Bool :=
  match item.request.operation with
  | .use .. => true
  | _ => false

def noServiceReceipts : List VisitData := (visits 2).map fun visit =>
  { visit with items := visit.items.filter fun item => !(isService item) }

def lateReceipts : List VisitData := (visits 2).map fun visit =>
  { visit with after := { visit.after with clock := 20 } }

def invalidSigners : List VisitData := (visits 2).map fun visit =>
  { visit with items := visit.items.map fun item =>
      if isService item then { item with request := { item.request with signer := 99 } } else item }

def wrongBundles : List VisitData := (visits 2).map fun visit =>
  { visit with items := visit.items.map fun item =>
      match item.request.operation with
      | .use bearer _ purpose => { item with request := { item.request with operation := .use bearer [] purpose } }
      | _ => item }

theorem independent_replay_rejects_missing_late_invalid_and_partial_payments :
    traceCheck (visits 2) = true ∧ nativeCheck 2 = true ∧ nativeCheck 1 = false ∧
    traceCheck noServiceReceipts = false ∧ traceCheck lateReceipts = false ∧
    traceCheck invalidSigners = false ∧ traceCheck wrongBundles = false := by
  decide +kernel

def firstOriginalItem : ExecutionItem Party Good Port Technology Unit :=
  (law.rawItems (source.frameAt 1).raw (source.frameWord 1 (source.frameAt 1))).head (by decide +kernel)

def starvedOriginalItem : ExecutionItem Party Good Port Technology Unit :=
  { firstOriginalItem with before := { firstOriginalItem.before with stock := fun actor good =>
      if actor = 0 ∧ good = .life then 0 else firstOriginalItem.before.stock actor good } }

theorem floor_rejection_contains_the_actual_bad_cut_and_bearer :
    checkCuts [starvedOriginalItem] [0] = false ∧
    (violations [starvedOriginalItem] [0]).length = 1 ∧
    ((violations [starvedOriginalItem] [0]).map (fun violation => (violation.item.index, violation.actor))) = [(0, 0)] := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit
