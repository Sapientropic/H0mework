import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceUnitAmputatedFourPoint

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualUnitFourPointReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance actualUnitTimeIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

open PreparationPhysicalFinitePoleVertices PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativeWardFiniteObservation
open PreparationPhysicalNativePolarizationEmitter

open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationPhysicalFiniteObservationSoftReturn PreparationVacuumSoftPoleSelection

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalNativePhaseChargeInventory
open SU7MotherGaugeTheory SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction

open PreparationPhysicalActualPhaseChargeReturn
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open GaussQuantumMultiplier GaussHalfDensity CanonicalGradedCharge GaussHistoryHilbert
open SourceQuantumGaugeSliceCoordinates
local instance : DecidableEq Mode:=Classical.decEq _

open PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentRegularAnchor PreparationVacuumPhysicalPoleAmputation

open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumPhysicalPoleLegDynamics
open Stage9DEF Stage9DEF.Compatibility
attribute [local irreducible] jointGenerator jointResolvent sourceChargedGaussPrepared

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

open PreparationPhysicalActualLegNormalization PreparationVacuumPhysicalTailPrice
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian

attribute [local irreducible] physicalTime timeSlope PreparationVacuumRawJointFeedback.rawReader rawReaderContact

/-- The physical clock has the original zero-spectral generator; independent material endpoints remain inside. -/
def sourceUnitTimeCurrent (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (reader : Field289) (age : ℝ) (field : Field289) : ℂ :=
  -sourceUnitRead q sL eL sR eR (fiveKernel reader q.p q.k q.F q.z q.w age field)

def sourceUnitTimeSlope (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (reader force : Field289) (age : ℝ) : ℂ :=
  -sourceUnitRead q sL eL sR eR (fiveDerivative reader force q.p q.k q.F q.z q.w age)

theorem sourceUnitTimeCurrent_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (reader force : Field289) (age : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceUnitTimeCurrent q sL eL sR eR reader age (r • force))
      (sourceUnitTimeSlope q sL eL sR eR reader force age) 0 := by
  exact ((sourceUnitRead q sL eL sR eR).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0
    (fiveKernel_generated reader force q.p q.k q.F q.z q.w left right age)).neg

/-- All five original terms are retained; index2 is the direct reader contact, not part of either time variation. -/
def sourceUnitTimeParts (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (reader force : Field289) (age : ℝ) : Fin 5→ℂ :=
  ![-sourceUnitRead q sL eL sR eR
      (timeSlope force (q.p+q.k) q.F (-age)*jointResolvent (q.p+q.k) q.F q.z 0*
        PreparationVacuumRawJointFeedback.rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0),
    -sourceUnitRead q sL eL sR eR
      (physicalTime (q.p+q.k) q.F (-age) 0*
        (-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*jointResolvent (q.p+q.k) q.F q.z 0))*
        PreparationVacuumRawJointFeedback.rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0),
    -sourceUnitRead q sL eL sR eR
      (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0*
        rawReaderContact reader force q.p q.F*jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0),
    -sourceUnitRead q sL eL sR eR
      (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0*
        PreparationVacuumRawJointFeedback.rawReader reader q.p q.F 0*
        (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0))*physicalTime q.p q.F age 0),
    -sourceUnitRead q sL eL sR eR
      (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0*
        PreparationVacuumRawJointFeedback.rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0*timeSlope force q.p q.F age)]

theorem sourceUnitTimeSlope_parts (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (reader force : Field289) (age : ℝ) :
    sourceUnitTimeSlope q sL eL sR eR reader force age=
      ∑i : Fin 5,sourceUnitTimeParts q sL eL sR eR reader force age i := by
  simp only [sourceUnitTimeSlope,fiveDerivative,map_add,sourceUnitTimeParts,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ]
  ring

/-- The original source price controls the complete same-clock response on the generated unit legs. -/
theorem sourceUnitTimeSlope_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (reader force : Field289) (eta age : ℝ) (positive : 0<eta) (future : 0≤age)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖sourceUnitTimeSlope q sL eL sR eR reader force age‖≤
      fiveCoefficient q reader force eta*Real.exp (4*eta*age) := by
  rw [sourceUnitTimeSlope,norm_neg,sourceUnitRead_original]
  exact (sourceActualUnitLegRead_bound q sL eL sR eR left right
    (fiveDerivative reader force q.p q.k q.F q.z q.w age)).trans
    (fiveKernel_price q reader force eta age positive future)

/-- This actual current preserves every full289 source row. -/
def sourceUnitEulerCurrent (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (age : ℝ) (field : Field289) : Fin 289→ℂ :=
  fun i=>sourceUnitTimeCurrent q sL eL sR eR (fieldUnit i) age field

def sourceUnitEulerSlope (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (force : Field289) (age : ℝ) : Fin 289→ℂ :=
  fun i=>sourceUnitTimeSlope q sL eL sR eR (fieldUnit i) force age

theorem sourceUnitEulerCurrent_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (force : Field289) (age : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceUnitEulerCurrent q sL eL sR eR age (r • force))
      (sourceUnitEulerSlope q sL eL sR eR force age) 0 :=
  hasDerivAt_pi.mpr (fun i=>sourceUnitTimeCurrent_generated q sL eL sR eR (fieldUnit i) force age left right)

/-- The exact original fullfield co-source map consumes the same generated current derivative. -/
theorem sourceUnitCoSource_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (force : Field289) (frequency : Fin 4→ℂ) (age : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>originalCoSource frequency (sourceUnitEulerCurrent q sL eL sR eR age (r • force)))
      (originalCoSource frequency (sourceUnitEulerSlope q sL eL sR eR force age)) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  simp only [originalCoSource,Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum
  intro j _
  exact (sourceUnitTimeCurrent_generated q sL eL sR eR (fieldUnit j) force age left right).const_mul _

/-- At the original background the new source current is the same full kernel read plus its actual leg corrections. -/
theorem sourceUnitEulerCurrent_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (age : ℝ) (i : Fin 289) :
    sourceUnitEulerCurrent q sL eL sR eR age 0 i=
      sourceActualLegNormalization q sL eL sR eR*
        (-sourceQuantumChargedRead q sL eL sR eR (actualJointKernel q (q.p+q.k) q.p age i)-
          sourceActualLegCorrection q sL eL sR eR (actualJointKernel q (q.p+q.k) q.p age i)) := by
  have momentum : (q.p+q.k)-q.p=q.k := by abel
  have original:=actualJointKernel_original q (q.p+q.k) q.p age i
  rw [momentum] at original
  rw [sourceUnitEulerCurrent,sourceUnitTimeCurrent,original,sourceUnitRead_original,sourceActualUnitLegRead_return]
  ring

end LowEnergy.PreparationPhysicalActualUnitFourPointReturn
