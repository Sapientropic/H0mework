import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMovingSourcePhysicalCircuit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMovingSourceNoetherPartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
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
open scoped Topology InnerProductSpace Matrix Matrix.Norms.L2Operator BigOperators
local instance instDecidableEqMode_actualMovingSourcePhysicalPartition : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] jointResolvent jointCurrent physicalTime timeSlope noetherReader noetherReaderContact
  actualMovingNoetherReader actualMovingNoetherReaderContact actualMovingHeavyNoetherReader
  actualMovingHeavyNoetherReaderContact projectedNoetherReader projectedNoetherReaderContact
  actualPhysicalEulerObserver dressedEulerObserver

private def responseFive (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289)
    (age : ℝ) (J dJ : H→L[ℂ]H) : H→L[ℂ]H:=
  let p:=event.momentum-transfer
  let TL:=physicalTime p event.frame (-age) 0
  let L:=jointResolvent p event.frame event.energy 0
  let R:=jointResolvent event.momentum event.frame event.energy 0
  let TR:=physicalTime event.momentum event.frame age 0
  let dTL:=timeSlope force p event.frame (-age)
  let dL:=-(L*jointCurrent p event.frame event.energy 0 force*L)
  let dR:=-(R*jointCurrent event.momentum event.frame event.energy 0 force*R)
  let dTR:=timeSlope force event.momentum event.frame age
  (((dTL*L+TL*dL)*J+(TL*L)*dJ)*R+((TL*L)*J)*dR)*TR+(((TL*L)*J)*R)*dTR

def actualMovingHeavySourceVariation (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) : H→L[ℂ]H:=
  responseFive event transfer force age
    (actualMovingHeavyNoetherReader pL pR reference reader event.momentum event.frame 0)
    (actualMovingHeavyNoetherReaderContact pL pR reference reader force event.momentum event.frame)

private theorem response_five_add (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289)
    (age : ℝ) (J K dJ dK : H→L[ℂ]H) :
    responseFive event transfer force age (J+K) (dJ+dK)=
      responseFive event transfer force age J dJ+responseFive event transfer force age K dK:=by
  unfold responseFive
  noncomm_ring

attribute [local irreducible] actualMovingSourceVariation actualMovingHeavySourceVariation
  sourceProjectedVariation actualFullNoetherVariation actualMovingPhysicalResponse actualMovingOriginalResponse

/-- The complete current and complete contact enter every original inverse/time leg; selected I-P heavy and cross/outside are retained. -/
theorem actual_full_noether_moving_source_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) :
    actualFullNoetherVariation event transfer reader force age=
      actualMovingSourceVariation pL pR reference event transfer reader force age+
      actualMovingHeavySourceVariation pL pR reference event transfer reader force age+
      sourceProjectedVariation sourceRestCrossOutsideMap event transfer reader force age:=by
  have current:=actual_moving_noether_reader_whole_partition pL pR reference reader event.momentum event.frame
  have contact:=actual_moving_noether_reader_contact_whole_partition pL pR reference reader force event.momentum event.frame
  unfold actualFullNoetherVariation actualMovingSourceVariation actualMovingHeavySourceVariation sourceProjectedVariation
  change responseFive event transfer force age (noetherReader reader event.momentum event.frame 0)
    (noetherReaderContact reader force event.momentum event.frame)=
    responseFive event transfer force age
      (actualMovingNoetherReader pL pR reference reader event.momentum event.frame 0)
      (actualMovingNoetherReaderContact pL pR reference reader force event.momentum event.frame)+
    responseFive event transfer force age
      (actualMovingHeavyNoetherReader pL pR reference reader event.momentum event.frame 0)
      (actualMovingHeavyNoetherReaderContact pL pR reference reader force event.momentum event.frame)+
    responseFive event transfer force age
      (projectedNoetherReader sourceRestCrossOutsideMap reader event.momentum event.frame 0)
      (projectedNoetherReaderContact sourceRestCrossOutsideMap reader force event.momentum event.frame)
  exact ((congrArg (fun J=>responseFive event transfer force age J
    (noetherReaderContact reader force event.momentum event.frame)) current.symm).trans
    (congrArg (responseFive event transfer force age
      (actualMovingNoetherReader pL pR reference reader event.momentum event.frame 0+
        actualMovingHeavyNoetherReader pL pR reference reader event.momentum event.frame 0+
        projectedNoetherReader sourceRestCrossOutsideMap reader event.momentum event.frame 0)) contact.symm)).trans
    ((response_five_add event transfer force age _ _ _ _).trans
      (congrArg (fun A : H→L[ℂ]H=>A+responseFive event transfer force age
        (projectedNoetherReader sourceRestCrossOutsideMap reader event.momentum event.frame 0)
        (projectedNoetherReaderContact sourceRestCrossOutsideMap reader force event.momentum event.frame))
        (response_five_add event transfer force age _ _ _ _)))

theorem actual_physical_full_response_moving_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (leg : CompositeLeg) (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) :
    actualPhysicalEulerObserver event leg (actualFullNoetherVariation event transfer reader force age)=
      actualMovingPhysicalResponse pL pR reference event leg transfer reader force age+
      actualPhysicalEulerObserver event leg (actualMovingHeavySourceVariation pL pR reference event transfer reader force age)+
      actualPhysicalEulerObserver event leg (sourceProjectedVariation sourceRestCrossOutsideMap event transfer reader force age):=by
  simpa only [map_add,actualMovingPhysicalResponse] using
    congrArg (actualPhysicalEulerObserver event leg)
      (actual_full_noether_moving_source_partition pL pR reference event transfer reader force age)

/-- The old finite full-reader slope consumes exactly the same moving source split on its unchanged preparation. -/
theorem actual_original_finite_slope_moving_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) (age : ℝ) (i : Fin 289) :
    finiteConstantFieldSlope event transfer force age i=
      actualMovingOriginalResponse pL pR reference event transfer (fieldUnit i) force age+
      dressedEulerObserver event (actualMovingHeavySourceVariation pL pR reference event transfer (fieldUnit i) force age)+
      dressedEulerObserver event (sourceProjectedVariation sourceRestCrossOutsideMap event transfer (fieldUnit i) force age):=by
  have original:=(finite_constant_field_slope_actual event transfer force age i).trans
    (actual_original_jet_same_operator event transfer force age i).symm
  apply original.trans
  simpa only [map_add,actualMovingOriginalResponse] using
    congrArg (dressedEulerObserver event)
      (actual_full_noether_moving_source_partition pL pR reference event transfer (fieldUnit i) force age)

/-- The physical output state and its complete original inverse/Y responsibility are kept in the exact observer-change consumer. -/
theorem actual_moving_response_original_observer_return (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (leg : CompositeLeg) (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) :
    actualMovingPhysicalResponse pL pR reference event leg transfer reader force age=
      actualMovingOriginalResponse pL pR reference event transfer reader force age+
      actualPhysicalObserverChange event leg (actualMovingSourceVariation pL pR reference event transfer reader force age):=by
  unfold actualMovingPhysicalResponse actualMovingOriginalResponse
  exact actual_observer_change_same_operator event leg _

end LowEnergy.GaussComposite.ActualMovingSourceLight
