import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberUnitTime
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherAction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberSector
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalHalfAxis PreparationVacuumJointFieldResponse PreparationVacuumNoetherChart
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNoether
open PreparationVacuumSourcePreparedResponse GaussComposite.SourceGraph
open FullYSourceCutoffVolterra
attribute [local irreducible] dressedNoetherKernel sourceDressedUnit physicalTime jointResolvent noetherReader

/-- The original five-factor actual kernel directly consumes the three-prefix source unit propagation. -/
theorem actual_noether_created_time_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    dressedNoetherKernel event transfer reader age 0 (sourceDressedUnit event.epsilon event.precision)=
      physicalTime (event.momentum-transfer) event.frame (-age) 0
        (jointResolvent (event.momentum-transfer) event.frame event.energy 0
          (noetherReader reader event.momentum event.frame 0
            (jointResolvent event.momentum event.frame event.energy 0
              (partialEvolution (actualC event.momentum event.frame) (actualA event.momentum event.frame) 2 age
                (sourceDressedUnit event.epsilon event.precision))))) := by
  unfold dressedNoetherKernel
  simp only [mul_apply_eq_comp,actual_time_created_unit]

/-- Same actual unit-minus-background read: only the paid right source propagation is simplified; both independent Green legs and the full unchanged background remain. -/
theorem actual_noether_observer_time_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0)=
      -inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (physicalTime (event.momentum-transfer) event.frame (-age) 0
          (jointResolvent (event.momentum-transfer) event.frame event.energy 0
            (noetherReader reader event.momentum event.frame 0
              (jointResolvent event.momentum event.frame event.energy 0
                (partialEvolution (actualC event.momentum event.frame) (actualA event.momentum event.frame) 2 age
                  (sourceDressedUnit event.epsilon event.precision))))))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (dressedNoetherKernel event transfer reader age 0 (prepared (sourceProfile event.epsilon event.precision))) := by
  rw [dressed_euler_observer_original,actual_noether_created_time_return]

end LowEnergy.GaussComposite.ActualDressedNumberSector
