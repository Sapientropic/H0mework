import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Biological
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalRead

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1BiologicalUpdate

structure WholeRaw where
  quantum : Raw
  particles : Classical.Raw

def ClassicalRepairResponse {body : Body} (result : LocalRepairDisposition body) (raw : Classical.Raw) :=
  match result with
  | .residual _ _ => PUnit
  | .repaired receipt => Classical.Disposition receipt.nextBody.current.2 raw

def classicalFromRepair {body : Body} (result : LocalRepairDisposition body) (raw : Classical.Raw) :
    ClassicalRepairResponse result raw :=
  match result with
  | .residual _ _ => PUnit.unit
  | .repaired receipt => Classical.fromCursor receipt.nextBody.current.2 raw

structure WholeResponse {body : Body} (repair : LocalRepairDisposition body) (raw : WholeRaw) where
  quantum : RepairResponse repair raw.quantum
  particles : ClassicalRepairResponse repair raw.particles
  quantumActual : quantum = fromRepair repair raw.quantum
  particlesActual : particles = classicalFromRepair repair raw.particles

def wholeResponse {body : Body} (repair : LocalRepairDisposition body) (raw : WholeRaw) : WholeResponse repair raw :=
  ⟨fromRepair repair raw.quantum,classicalFromRepair repair raw.particles,rfl,rfl⟩

theorem whole_repair_current {body : Body} (receipt : LocalRepairReceipt body) (raw : WholeRaw) :
    (wholeResponse (.repaired receipt) raw).quantum = fromCursor receipt.nextBody.current.2 raw.quantum ∧
    (wholeResponse (.repaired receipt) raw).particles = Classical.fromCursor receipt.nextBody.current.2 raw.particles :=
  ⟨rfl,rfl⟩

theorem whole_repair_residual {body : Body} (event : LocalRepairEvent body) (failed : ¬ Successful body event) (raw : WholeRaw) :
    (wholeResponse (.residual event failed) raw).quantum = PUnit.unit ∧
    (wholeResponse (.residual event failed) raw).particles = PUnit.unit := ⟨rfl,rfl⟩

end
end CPS1SameEventFunction
