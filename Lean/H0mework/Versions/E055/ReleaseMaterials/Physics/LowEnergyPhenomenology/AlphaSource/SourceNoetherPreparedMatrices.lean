import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceAbsoluteNoetherVertex

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualNoetherVertexReturn
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
local instance actualNoetherMatrixIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

abbrev ActualPreparedIndex:=Fin 2×Fin 2

/-- Every entry is the actual normalized four-source preparation read, not a supplied matrix. -/
def sourcePreparedCurrentMatrix (q : PhysicalResponsePoint) (A : H→L[ℂ]H) :
    Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  fun i j=>sourceQuantumChargedRead q i.1 i.2 j.1 j.2 A

def sourcePreparedChargeUnitMatrix : Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  Matrix.diagonal (fun i=>(sourceActualPhaseCharge i.2:ℂ))

private theorem source_index_equal (i j : ActualPreparedIndex) :
    sourceChargedRestIndex i.1 i.2=sourceChargedRestIndex j.1 j.2 ↔ i=j := by
  rcases i with ⟨a,b⟩
  rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- The absolute Noether matrix is generated by the original Gram and charge action on all four source columns. -/
theorem sourcePreparedChargeUnit_generated (q : PhysicalResponsePoint) :
    sourcePreparedCurrentMatrix q sourceAbsoluteCharge=
      (Stage10.ActionNormalization.phaseMomentum:ℂ) • sourcePreparedChargeUnitMatrix := by
  ext i j
  simp only [sourcePreparedCurrentMatrix,sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply,sourceAbsoluteCharge_prepared,inner_smul_right,
    sourceChargedGauss_gram,source_index_equal,sourcePreparedChargeUnitMatrix,Matrix.smul_apply,
    Matrix.diagonal_apply,smul_eq_mul]
  by_cases same : i=j
  · subst j;simp
  · simp [same]

def sourceNoetherTwoPointMatrix (q : PhysicalResponsePoint) (p : PhysicalMomentum) (z : ℂ) :
    Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  sourcePreparedCurrentMatrix q (jointResolvent p q.F z 0)

def sourceNoetherVertexMatrix (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  sourcePreparedCurrentMatrix q (sourceAbsoluteNoetherVertex q pL pR)

def sourceNoetherResponseMatrix (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  sourcePreparedCurrentMatrix q (sourceAbsoluteNoetherResponse q pL pR)

/-- Charge normalization uses the nonzero original source h, and retains the full off-diagonal matrix. -/
def sourceNormalizedNoetherVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  (Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹ • sourceNoetherVertexMatrix q pL pR

def sourceNormalizedNoetherResponse (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  (Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹ • sourceNoetherResponseMatrix q pL pR

/-- Unit, neutral, and mixed channels obey the same generated full-resolvent Ward matrix. -/
theorem sourceNormalizedNoether_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w) • sourceNormalizedNoetherVertex q pL pR=
      sourceNoetherTwoPointMatrix q pL q.z*sourcePreparedChargeUnitMatrix-
        sourcePreparedChargeUnitMatrix*sourceNoetherTwoPointMatrix q pR q.w+
          sourceNormalizedNoetherResponse q pL pR := by
  ext i j
  have generated:=sourceAbsoluteNoether_prepared q pL pR i.1 i.2 j.1 j.2 left right
  simp only [sourceNormalizedNoetherVertex,sourceNoetherVertexMatrix,sourceNormalizedNoetherResponse,
    sourceNoetherResponseMatrix,sourceNoetherTwoPointMatrix,sourcePreparedChargeUnitMatrix,
    Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    sourcePreparedCurrentMatrix,smul_eq_mul]
  have nonzero : (Stage10.ActionNormalization.phaseMomentum:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  apply (mul_left_cancel₀ nonzero)
  field_simp
  linear_combination generated

/-- Normalizing the measured original charge itself produces the same source unit matrix. -/
theorem sourcePreparedChargeUnit_normalized (q : PhysicalResponsePoint) :
    (Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹ •
      sourcePreparedCurrentMatrix q sourceAbsoluteCharge=sourcePreparedChargeUnitMatrix := by
  rw [sourcePreparedChargeUnit_generated,smul_smul,inv_mul_cancel₀
    (Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'),one_smul]

end LowEnergy.PreparationPhysicalActualNoetherVertexReturn
