import H0mework.Chemistry.LAlanineInertia.SourceSourceBoundLAlanine40KInertialStep
import H0mework.Chemistry.LAlanineForce.GeneratedForceUpdate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Producer

open Force.Interface
open LAlanine40K2025.Inertia.Source

def forceComponentSum (components : Array (Array (Array Int))) (atom : Atom) (axis : Axis) : Int :=
  (components.toList.map fun rows => (rows[atom.val]!)[axis.val]!).sum

theorem current_gradient_six_components : stepReadout.currentGradientComponents.size = 6 := by decide
theorem target_gradient_six_components : stepReadout.targetGradientComponents.size = 6 := by decide

theorem currentGradientWholeLedger : ∀ atom axis,
    forceComponentSum stepReadout.currentGradientComponents atom axis +
      stepReadout.currentGradientRoundingResidual atom axis =
        stepReadout.currentGradientPicohartree atom axis := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem targetGradientWholeLedger : ∀ atom axis,
    forceComponentSum stepReadout.targetGradientComponents atom axis +
      stepReadout.targetGradientRoundingResidual atom axis =
        stepReadout.targetGradientPicohartree atom axis := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem target_nuclei_count : stepReadout.targetNuclei.size = 13 := by decide

theorem currentEnergyRows_exact : stepReadout.currentLedger.rowToIntegralExact :=
  Force.Producer.targetEnergyRows_exact

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem targetEnergyRows_exact : stepReadout.targetLedger.rowToIntegralExact := by
  intro component
  cases component <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem targetWholeEnergyClosure :
    stepReadout.targetLedger.grandRowSum + stepReadout.targetLedger.rowResidualSum +
      stepReadout.targetLedger.componentRoundingResidual +
      stepReadout.targetLedger.scfRecomputationResidual =
        stepReadout.targetLedger.reportedSCF := by decide

theorem currentEnergyReport_eq_parent :
    stepReadout.currentLedger.reportedSCF = Force.Source.updateReadout.targetEnergyNanohartree := by decide

theorem currentWholeEnergyClosure :
    stepReadout.currentLedger.grandRowSum + stepReadout.currentLedger.rowResidualSum +
      stepReadout.currentLedger.componentRoundingResidual +
      stepReadout.currentLedger.scfRecomputationResidual =
        stepReadout.currentLedger.reportedSCF := by
  rw [currentEnergyReport_eq_parent]
  exact Force.Producer.targetWholeEnergyClosure

end LAlanine40K2025.Inertia.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
