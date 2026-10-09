import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Energy
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.VariationalResponse

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource ContinuousLinearMap
open scoped Matrix Matrix.Norms.Elementwise
variable {frame : CPS1Recycling.Frame}

theorem occupied_physical_joint (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedConfiguration source)
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source positions)) :
    occupiedDifferential source positions occupied = occupiedPhysicalDifferential source positions occupied := by
  let inclusion : OccupiedConfiguration source →L[ℝ] EnergyConfiguration source :=
    ContinuousLinearMap.inr ℝ _ _
  have coordinates : HasFDerivAt (fun next : OccupiedConfiguration source => (positions,next)) inclusion occupied := by
    exact (hasFDerivAt_const positions occupied).prodMk (hasFDerivAt_id occupied)
  have generated := (energy_hasFDerivAt source positions occupied ready).comp occupied coordinates
  have full : HasFDerivAt (fun next : OccupiedConfiguration source => energyAt source positions next)
      (occupiedDifferential source positions occupied) occupied := generated
  exact full.unique (occupied_physical_hasFDerivAt source positions occupied)

theorem occupied_physical_joint_apply (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied direction : OccupiedConfiguration source)
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source positions)) :
    energyDifferential source positions occupied (0,direction) = 2 *
      (Matrix.trace (occupied.conjTranspose * physicalFockAt source positions occupied * direction)).re := by
  have generated := congrArg (fun derivative : OccupiedConfiguration source →L[ℝ] ℝ => derivative direction)
    (occupied_physical_joint source positions occupied ready)
  exact generated

end
end CPS1Deformation
