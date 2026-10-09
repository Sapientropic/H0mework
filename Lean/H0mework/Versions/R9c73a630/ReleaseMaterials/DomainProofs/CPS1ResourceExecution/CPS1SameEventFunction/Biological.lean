import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Response
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Repair

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1BiologicalUpdate

-- The exact returned biosynthetic body supplies the current. Its original
-- source, second native birth and pending biological duties remain on that body.
def RepairResponse {body : Body} (result : LocalRepairDisposition body) (raw : Raw) : Type 1 :=
  match result with
  | .residual _ _ => PUnit
  | .repaired receipt => FunctionDisposition receipt.nextBody.current.2 raw

def fromRepair {body : Body} (result : LocalRepairDisposition body) (raw : Raw) : RepairResponse result raw :=
  match result with
  | .residual _ _ => PUnit.unit
  | .repaired receipt => fromCursor receipt.nextBody.current.2 raw

theorem repair_consumes_actual_current {body : Body} (receipt : LocalRepairReceipt body) (raw : Raw) :
    fromRepair (LocalRepairDisposition.repaired receipt) raw = fromCursor receipt.nextBody.current.2 raw := rfl

-- Complete source data, including residuals, are retained in this dependent
-- return. A failed interaction does not undo the paid biosynthetic repair.
structure BiologicalFunction (body : Body) (raw : Raw) where
  repair : LocalRepairDisposition body
  response : RepairResponse repair raw
  actual : response = fromRepair repair raw

def biologicalFunction {body : Body} (result : LocalRepairDisposition body) (raw : Raw) : BiologicalFunction body raw :=
  ⟨result,fromRepair result raw,rfl⟩

end
end CPS1SameEventFunction
