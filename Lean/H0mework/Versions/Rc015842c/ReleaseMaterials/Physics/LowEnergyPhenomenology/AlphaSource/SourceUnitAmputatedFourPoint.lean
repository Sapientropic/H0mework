import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceUnitMixedDerivative

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
local instance actualUnitFourAmputationIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian sourceUnitRead sourceActualUnitLegRead

def sourceFourPointForward (q : PhysicalResponsePoint) (f g : Field289) : H→L[ℂ]H :=
  jointCurrent 0 q.F q.z 0 f*jointResolvent 0 q.F q.z 0*jointCurrent 0 q.F q.w 0 g

def sourceFourPointReverse (q : PhysicalResponsePoint) (f g : Field289) : H→L[ℂ]H :=
  jointCurrent 0 q.F q.w 0 g*jointResolvent 0 q.F q.w 0*jointCurrent 0 q.F q.w 0 f

def sourceFourPointContact (q : PhysicalResponsePoint) (f g : Field289) : H→L[ℂ]H :=
  jointHessian 0 q.F q.w f g

def sourceFourPointCore (q : PhysicalResponsePoint) (f g : Field289) : H→L[ℂ]H :=
  sourceFourPointForward q f g+sourceFourPointReverse q f g-sourceFourPointContact q f g

private theorem sandwich {R : Type*} [Ring R] (L Rg A B C S : R) :
    L*A*L*B*Rg+L*B*Rg*C*Rg-L*S*Rg=L*(A*L*B+B*Rg*C-S)*Rg := by
  noncomm_ring

/-- The original two ordered insertions and Hessian keep both independent spectral parameters and signs. -/
theorem sourceFourPoint_factor (q : PhysicalResponsePoint) (f g : Field289) :
    mixedVertex f g 0 0 q.F q.z q.w=
      jointResolvent 0 q.F q.z 0*sourceFourPointCore q f g*jointResolvent 0 q.F q.w 0 := by
  simp only [mixedVertex,zero_add,sourceFourPointCore,sourceFourPointForward,sourceFourPointReverse,sourceFourPointContact]
  exact sandwich _ _ _ _ _ _

/-- The direct mixed contact remains a separate component of the actual four-point read. -/
def sourceUnitFourPointPair (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) : ℂ × ℂ :=
  (sourceUnitRead q sL eL sR eR (sourceFourPointForward q f g)+
    sourceUnitRead q sL eL sR eR (sourceFourPointReverse q f g),
    -sourceUnitRead q sL eL sR eR (sourceFourPointContact q f g))

theorem sourceUnitFourPoint_amputated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceActualLegNormalization q sL eL sR eR*
      ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w)*
      sourceQuantumChargedRead q sL eL sR eR (mixedVertex f g 0 0 q.F q.z q.w)=
    (sourceUnitFourPointPair q sL eL sR eR f g).1+(sourceUnitFourPointPair q sL eL sR eR f g).2 := by
  rw [sourceFourPoint_factor,←sourceActualUnitLegRead_vertex q sL eL sR eR left right]
  rw [←sourceUnitRead_original q sL eL sR eR (sourceFourPointCore q f g)]
  simp only [sourceFourPointCore,map_sub,map_add,sourceUnitFourPointPair]
  ring

/-- The same complete source derivative is the amputated four-point total, not an independently supplied response. -/
theorem sourceUnitFourPoint_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>
      (sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))*
      sourceQuantumChargedRead q sL eL sR eR (jointVertex g 0 0 q.F q.z q.w (r • f)))
      ((sourceUnitFourPointPair q sL eL sR eR f g).1+(sourceUnitFourPointPair q sL eL sR eR f g).2) 0 := by
  have generated:=(sourceQuantumChargedRead q sL eL sR eR).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0
    (mixedVertex_generated f g 0 0 q.F q.z q.w left right)
  have scaled:=generated.const_mul (sourceActualLegNormalization q sL eL sR eR*
    ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))
  exact scaled.congr_deriv (sourceUnitFourPoint_amputated q sL eL sR eR f g left right)

/-- Each ordered component and the independent direct contact keep their own full exterior-leg correction. -/
theorem sourceUnitFourPoint_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (f g : Field289) :
    sourceUnitFourPointPair q sL eL sR eR f g=
      (sourceActualLegNormalization q sL eL sR eR*
        (sourceQuantumChargedRead q sL eL sR eR (sourceFourPointForward q f g)+
          sourceActualLegCorrection q sL eL sR eR (sourceFourPointForward q f g)+
          sourceQuantumChargedRead q sL eL sR eR (sourceFourPointReverse q f g)+
          sourceActualLegCorrection q sL eL sR eR (sourceFourPointReverse q f g)),
      -sourceActualLegNormalization q sL eL sR eR*
        (sourceQuantumChargedRead q sL eL sR eR (sourceFourPointContact q f g)+
          sourceActualLegCorrection q sL eL sR eR (sourceFourPointContact q f g))) := by
  simp only [sourceUnitFourPointPair,sourceUnitRead_original,sourceActualUnitLegRead_return]
  congr 1 <;> ring

theorem sourceUnitFourPoint_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖(sourceUnitFourPointPair q sL eL sR eR f g).1‖≤
      ‖jointCurrent 0 q.F q.z 0 f‖*‖jointResolvent 0 q.F q.z 0‖*‖jointCurrent 0 q.F q.w 0 g‖+
      ‖jointCurrent 0 q.F q.w 0 g‖*‖jointResolvent 0 q.F q.w 0‖*‖jointCurrent 0 q.F q.w 0 f‖ ∧
    ‖(sourceUnitFourPointPair q sL eL sR eR f g).2‖≤‖jointHessian 0 q.F q.w f g‖ := by
  have price (A B C : H→L[ℂ]H) : ‖sourceUnitRead q sL eL sR eR (A*B*C)‖≤‖A‖*‖B‖*‖C‖ := by
    rw [sourceUnitRead_original]
    exact (sourceActualUnitLegRead_bound q sL eL sR eR left right (A*B*C)).trans
      ((norm_mul_le (A*B) C).trans (mul_le_mul_of_nonneg_right (norm_mul_le A B) (norm_nonneg C)))
  constructor
  · exact (norm_add_le _ _).trans (add_le_add (price _ _ _) (price _ _ _))
  · simpa only [sourceUnitFourPointPair,norm_neg,sourceFourPointContact,sourceUnitRead_original] using
      sourceActualUnitLegRead_bound q sL eL sR eR left right (jointHessian 0 q.F q.w f g)

end LowEnergy.PreparationPhysicalActualUnitFourPointReturn
