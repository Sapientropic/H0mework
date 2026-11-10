import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMovingSourceNoether
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightCausalWindow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualQuarterOriginalObserverReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFiniteStaticRead

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMovingSourceLight
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualSourcePreparationBridge ActualSourceLightCircuit
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard
open ActualDressedFullCoulomb ActualDressedNoether ActualElectronWholeNoetherObserver
open ActualElectronFullNoetherMixedSoft ActualCompositeFieldCurrent
open ActualElectronQuarterSourceMatching ActualDressedFiniteStaticRead
open GaussHistoryHilbert MeasureTheory intervalIntegral
open scoped Topology InnerProductSpace Matrix Matrix.Norms.L2Operator BigOperators
local instance instDecidableEqMode_actualMovingSourcePhysicalCircuit : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance movingCircuitReal : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointResolvent jointCurrent physicalTime timeSlope
  actualMovingNoetherReader actualMovingNoetherReaderContact actualPhysicalEulerObserver dressedEulerObserver

def actualMovingSourceInteraction (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (reader : Field289) (age : ℝ) (h : Field289) : H→L[ℂ]H:=
  physicalTime (event.momentum-transfer) event.frame (-age) h*
    jointResolvent (event.momentum-transfer) event.frame event.energy h*
    actualMovingNoetherReader pL pR reference reader event.momentum event.frame h*
    jointResolvent event.momentum event.frame event.energy h*physicalTime event.momentum event.frame age h

def actualMovingSourceVariation (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) : H→L[ℂ]H:=
  let p:=event.momentum-transfer
  let TL:=physicalTime p event.frame (-age) 0
  let L:=jointResolvent p event.frame event.energy 0
  let J:=actualMovingNoetherReader pL pR reference reader event.momentum event.frame 0
  let R:=jointResolvent event.momentum event.frame event.energy 0
  let TR:=physicalTime event.momentum event.frame age 0
  let dTL:=timeSlope force p event.frame (-age)
  let dL:=-(L*jointCurrent p event.frame event.energy 0 force*L)
  let dJ:=actualMovingNoetherReaderContact pL pR reference reader force event.momentum event.frame
  let dR:=-(R*jointCurrent event.momentum event.frame event.energy 0 force*R)
  let dTR:=timeSlope force event.momentum event.frame age
  (((dTL*L+TL*dL)*J+(TL*L)*dJ)*R+((TL*L)*J)*dR)*TR+(((TL*L)*J)*R)*dTR

/-- The changing source Riesz current and its P'J contact enter the original complete five-term physical response. -/
theorem actual_moving_source_interaction_generated (pL pR : PhysicalMomentum) (reference : physicalChart)
    (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ)
    (small : ∀block : RestBlock,‖actualMovingSourceSylvester block pL pR (0,reference.val)-sourceRestHSGenerator block‖<1/8) :
    HasDerivAt (fun r : ℝ=>actualMovingSourceInteraction pL pR reference.val event transfer reader age (r • force))
      (actualMovingSourceVariation pL pR reference.val event transfer reader force age) 0:=by
  have tl:=physicalTime_direction force (event.momentum-transfer) event.frame (-age)
  have l:=inverse_direction (event.momentum-transfer) event.frame event.energy event.nonreal force
  have j:=actual_moving_noether_reader_generated pL pR reference reader force event.momentum event.frame small
  have r:=inverse_direction event.momentum event.frame event.energy event.nonreal force
  have tr:=physicalTime_direction force event.momentum event.frame age
  simpa only [actualMovingSourceInteraction,actualMovingSourceVariation,zero_smul,Pi.mul_apply] using!
    (((tl.mul l).mul j).mul r).mul tr

theorem actual_rest_moving_source_interaction_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>actualMovingSourceInteraction 0 0 GaussHistoryHilbert.sourcePoint.val event transfer reader age (r • force))
      (actualMovingSourceVariation 0 0 GaussHistoryHilbert.sourcePoint.val event transfer reader force age) 0:=by
  apply actual_moving_source_interaction_generated 0 0 GaussHistoryHilbert.sourcePoint event transfer reader force age
  intro block
  rw [actual_moving_sylvester_at_rest]
  norm_num

def actualMovingPhysicalResponse (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (leg : CompositeLeg) (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) : ℂ:=
  actualPhysicalEulerObserver event leg (actualMovingSourceVariation pL pR reference event transfer reader force age)

def actualMovingOriginalResponse (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) : ℂ:=
  dressedEulerObserver event (actualMovingSourceVariation pL pR reference event transfer reader force age)

/-- The original full physical N3 preparation observes all five differentiated legs and both moving-contact terms. -/
theorem actual_rest_moving_physical_response_generated (event : DressedEvent) (leg : CompositeLeg)
    (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>actualPhysicalEulerObserver event leg
      (actualMovingSourceInteraction 0 0 GaussHistoryHilbert.sourcePoint.val event transfer reader age (r • force)))
      (actualMovingPhysicalResponse 0 0 GaussHistoryHilbert.sourcePoint.val event leg transfer reader force age) 0:=
  ((actualPhysicalEulerObserver event leg).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (actual_rest_moving_source_interaction_generated event transfer reader force age)

/-- The old N2-minus-N1 observer consumes the same operator without changing its preparation or becoming the physical N3 observer. -/
theorem actual_rest_moving_original_response_generated (event : DressedEvent)
    (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>dressedEulerObserver event
      (actualMovingSourceInteraction 0 0 GaussHistoryHilbert.sourcePoint.val event transfer reader age (r • force)))
      (actualMovingOriginalResponse 0 0 GaussHistoryHilbert.sourcePoint.val event transfer reader force age) 0:=
  ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (actual_rest_moving_source_interaction_generated event transfer reader force age)

end LowEnergy.GaussComposite.ActualMovingSourceLight
