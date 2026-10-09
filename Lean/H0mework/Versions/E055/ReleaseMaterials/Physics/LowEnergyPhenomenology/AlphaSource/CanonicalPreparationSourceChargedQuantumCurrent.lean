import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedFilteredPreparation
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryCurrent.Readback

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedPacketQuantumReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage10 YangMills.FullPairing
open FullQuantum FullSpace SpatialGreen HistoryPrepared HistoryCurrent SpatialResponse
open GaugeGreen ScalarGreen GaugeHistory HistoryVariation PerturbedGreen
open PreparationPhysicalChargedPacketVoltage PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumElectromagneticIdentity MatterSpace.SpatialCAR
open MeasureTheory Filter
open scoped InnerProductSpace Topology

def sourceChargedPreparation (side edge : Fin 2) : Hilbert→L[ℂ] FullMatterL2 :=
  (sourceChargedFilter side edge).comp (HistoryPrepared.preparation.comp
    (operator (actualRestStatePreparation (sourceChargedRestIndex side edge))))

theorem sourceChargedPreparation_applied (side edge : Fin 2) :
    sourceChargedPreparation side edge (YangMills.FullPairing.prepared 0)=sourceChargedFilteredPacket side edge := by
  simp only [sourceChargedPreparation,ContinuousLinearMap.comp_apply]
  rw [←sourceChargedSpatialPacket_maker]
  rfl

/-- Both actual preparation maps remain inside the original source observable. -/
def sourceChargedQuantumMother (sideL edgeL sideR edgeR : Fin 2) (A : SpatialOperators) : YangMills.FullPairing.Mother :=
  fromOperator ((sourceChargedPreparation sideL edgeL).adjoint.comp
    (A.comp (sourceChargedPreparation sideR edgeR)))

def sourceChargedQuantumRead (sideL edgeL sideR edgeR : Fin 2) (A : SpatialOperators) : ℂ :=
  State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Compatibility.responseMatrix (sourceChargedQuantumMother sideL edgeL sideR edgeR A))

theorem sourceChargedQuantumRead_generated (sideL edgeL sideR edgeR : Fin 2) (A : SpatialOperators) :
    sourceChargedQuantumRead sideL edgeL sideR edgeR A=
      inner ℂ (sourceChargedFilteredPacket sideL edgeL) (A (sourceChargedFilteredPacket sideR edgeR)) := by
  rw [sourceChargedQuantumRead,sourceChargedQuantumMother,origin_response,operator_fromOperator]
  change inner ℂ (YangMills.FullPairing.prepared 0)
    ((sourceChargedPreparation sideL edgeL).adjoint
      (A (sourceChargedPreparation sideR edgeR (YangMills.FullPairing.prepared 0))))=_
  rw [ContinuousLinearMap.adjoint_inner_right,sourceChargedPreparation_applied,sourceChargedPreparation_applied]

theorem sourceChargedQuantumRead_fullWord (side edge : Fin 2) {ι : Type*} [Fintype ι]
    (tests : ι→FullMatterL2) (word : List (Letter (Option ι))) :
    sourceChargedQuantumRead side edge side edge
      (wordObservable (sourceChargedFilteredPacket side edge) tests word)=
        spatialMoment (sourceChargedFilteredPacket side edge) tests word := by
  rw [sourceChargedQuantumRead_generated]
  exact wordObservable_response _ tests word

def sourceChargedQuantumFourWord (sideL edgeL sideR edgeR : Fin 2)
    (boundary reader force : SpatialOperators) : ℂ :=
  let initial:=sourceChargedFilteredPacket sideR edgeR
  let tests:=commutatorTests boundary reader force (sourceChargedFilteredPacket sideL edgeL) initial
  sourceChargedQuantumRead sideR edgeR sideR edgeR
    (wordObservable initial tests [.create none,.annihilate (some 0),.create (some 1),.annihilate none])-
  sourceChargedQuantumRead sideR edgeR sideR edgeR
    (wordObservable initial tests [.create none,.annihilate (some 2),.create (some 3),.annihilate none])

theorem sourceChargedQuantumFourWord_generated (sideL edgeL sideR edgeR : Fin 2)
    (boundary reader force : SpatialOperators) :
    sourceChargedQuantumFourWord sideL edgeL sideR edgeR boundary reader force=
      inner ℂ (sourceChargedFilteredPacket sideL edgeL)
        (boundary (reader (force (sourceChargedFilteredPacket sideR edgeR))-
          force (reader (sourceChargedFilteredPacket sideR edgeR)))) := by
  simp only [sourceChargedQuantumFourWord,sourceChargedQuantumRead_fullWord]
  exact commutatorCAR_read boundary reader force _ _ (sourceChargedFilteredPacket_unit sideR edgeR)

variable (gauge direction : ℝ→GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
  (coupling : ℝ) (scalar scalarDirection : ℝ→ScalarProfile)
  (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "B" => returnedReader gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "J" => relativeInsertion gauge direction continuousGauge coupling scalar scalarDirection continuousScalar

/-- The complete original primitive current evolves both independently prepared source legs. -/
def sourceChargedCurrent (probe : GaugeProfile) (scalarProbe : ScalarProfile)
    (sideL edgeL sideR edgeR : Fin 2) (time epsilon : ℝ) : ℂ :=
  complexCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection probe scalarProbe
    (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR) time epsilon

theorem sourceChargedCurrent_read (probe : GaugeProfile) (scalarProbe : ScalarProfile)
    (sideL edgeL sideR edgeR : Fin 2) (time epsilon : ℝ) :
    sourceChargedCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe sideL edgeL sideR edgeR time epsilon=
      volumeWeight*sourceChargedQuantumRead sideL edgeL sideR edgeR
        (principal 0*B (inversePrincipal 0*variation probe scalarProbe) epsilon time) := by
  rw [sourceChargedCurrent,complexCurrent_operator,sourceChargedQuantumRead_generated]
  rfl

def sourceChargedCurrentKernel (probe : GaugeProfile) (scalarProbe : ScalarProfile)
    (sideL edgeL sideR edgeR : Fin 2) (time r : ℝ) : ℂ :=
  sourceChargedQuantumFourWord sideL edgeL sideR edgeR (principal 0)
    (B (inversePrincipal 0*variation probe scalarProbe) 0 time) (J r)

theorem sourceChargedCurrentKernel_generated (probe : GaugeProfile) (scalarProbe : ScalarProfile)
    (sideL edgeL sideR edgeR : Fin 2) (time r : ℝ) :
    sourceChargedCurrentKernel gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe sideL edgeL sideR edgeR time r=
      currentCARKernel gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
        continuousScalar continuousScalarDirection probe scalarProbe
        (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR) time r := by
  rw [sourceChargedCurrentKernel,sourceChargedQuantumFourWord_generated,currentCARKernel,
    commutatorCAR_read _ _ _ _ _ (sourceChargedFilteredPacket_unit sideR edgeR)]

/-- The actual two-leg derivative returns to four complete CAR words in the unchanged original quantum state. -/
theorem sourceChargedCurrent_derivative (probe : GaugeProfile) (scalarProbe : ScalarProfile)
    (sideL edgeL sideR edgeR : Fin 2) (time : ℝ) :
    HasDerivAt (sourceChargedCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe sideL edgeL sideR edgeR time)
      (volumeWeight*∫r in (0 : ℝ)..time,
        sourceChargedCurrentKernel gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
          continuousScalar continuousScalarDirection probe scalarProbe sideL edgeL sideR edgeR time r) 0 := by
  have original:=complexCurrent_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection probe scalarProbe
    (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR) time
  rw [currentResponse_CAR gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection probe scalarProbe
    (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR)
    (sourceChargedFilteredPacket_unit sideR edgeR) time] at original
  change HasDerivAt (complexCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection probe scalarProbe
    (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR) time) _ 0
  simpa only [sourceChargedCurrentKernel_generated] using original

end LowEnergy.PreparationPhysicalChargedPacketQuantumReturn
