import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualNormalizedVertex

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
local instance actualUnitFourIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The actual independent source legs give a continuous operator read on their original Gauss carrier. -/
def sourceUnitRead (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) : (H→L[ℂ]H)→L[ℂ]ℂ :=
  (sourceActualUnitDual q sL eL q.z).comp
    (ContinuousLinearMap.apply ℂ H (sourceActualUnitPrimal q sR eR q.w))

theorem sourceUnitRead_original (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (A : H→L[ℂ]H) :
    sourceUnitRead q sL eL sR eR A=sourceActualUnitLegRead q sL eL sR eR A := rfl

def sourceUnitMixedVertex (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) (p k : PhysicalMomentum) (z w : ℂ) : ℂ :=
  sourceUnitRead q sL eL sR eR (mixedVertex f g p k q.F z w)

/-- The original full289 generator derivative generates the mixed read on actual normalized legs. -/
theorem sourceUnitMixedVertex_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) (p k : PhysicalMomentum) (z w : ℂ) (left : z.im≠0) (right : w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceUnitRead q sL eL sR eR (jointVertex g p k q.F z w (r • f)))
      (sourceUnitMixedVertex q sL eL sR eR f g p k z w) 0 := by
  exact (sourceUnitRead q sL eL sR eR).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0
    (mixedVertex_generated f g p k q.F z w left right)

def sourceUnitComplexMixed (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Fin 289→ℂ) (p k : PhysicalMomentum) (z w : ℂ) : ℂ :=
  sourceUnitMixedVertex q sL eL sR eR (fun i=>(f i).re) (fun i=>(g i).re) p k z w+
    Complex.I*sourceUnitMixedVertex q sL eL sR eR (fun i=>(f i).im) (fun i=>(g i).re) p k z w+
    Complex.I*sourceUnitMixedVertex q sL eL sR eR (fun i=>(f i).re) (fun i=>(g i).im) p k z w-
    sourceUnitMixedVertex q sL eL sR eR (fun i=>(f i).im) (fun i=>(g i).im) p k z w

/-- Every complex field coordinate is returned by the four original real derivative paths. -/
theorem sourceUnitComplexMixed_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Fin 289→ℂ) (p k : PhysicalMomentum) (z w : ℂ) (left : z.im≠0) (right : w.im≠0) :
    HasDerivAt (fun r : ℝ=>
      sourceUnitRead q sL eL sR eR (jointVertex (fun i=>(g i).re) p k q.F z w (r • (fun i=>(f i).re)))+
      Complex.I*sourceUnitRead q sL eL sR eR (jointVertex (fun i=>(g i).re) p k q.F z w (r • (fun i=>(f i).im)))+
      Complex.I*sourceUnitRead q sL eL sR eR (jointVertex (fun i=>(g i).im) p k q.F z w (r • (fun i=>(f i).re)))-
      sourceUnitRead q sL eL sR eR (jointVertex (fun i=>(g i).im) p k q.F z w (r • (fun i=>(f i).im))))
      (sourceUnitComplexMixed q sL eL sR eR f g p k z w) 0 := by
  exact (((sourceUnitMixedVertex_generated q sL eL sR eR _ _ p k z w left right).add
    ((sourceUnitMixedVertex_generated q sL eL sR eR _ _ p k z w left right).const_mul Complex.I)).add
    ((sourceUnitMixedVertex_generated q sL eL sR eR _ _ p k z w left right).const_mul Complex.I)).sub
    (sourceUnitMixedVertex_generated q sL eL sR eR _ _ p k z w left right)

/-- This is the complete mixed response with its actual single and double exterior-leg corrections. -/
theorem sourceUnitMixedVertex_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) (p k : PhysicalMomentum) (z w : ℂ) :
    sourceUnitMixedVertex q sL eL sR eR f g p k z w=
      sourceActualLegNormalization q sL eL sR eR*
        (sourceQuantumChargedRead q sL eL sR eR (mixedVertex f g p k q.F z w)+
          sourceActualLegCorrection q sL eL sR eR (mixedVertex f g p k q.F z w)) :=
  sourceActualUnitLegRead_return q sL eL sR eR _

end LowEnergy.PreparationPhysicalActualUnitFourPointReturn
