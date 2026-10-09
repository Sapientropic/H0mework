import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargeTransition

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualGaussChargeCurrent
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
local instance actualGaussChargeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- Original real-scalar Fock branches retain the independent conjugate branch of the source Noether operator. -/
def sourceActualGaussChargeMatrix : Matrix Mode Mode ℂ :=
  SourceRealScalarFock.branches (Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether))

theorem sourceActualGaussCharge_original :
    sourceActualGaussChargeMatrix=SourceRealScalarFock.branches
      (Quantum.operatorMatrix (Complex.I • sourceNativeOriginGenerator)) := by
  rw [sourceActualGaussChargeMatrix,sourcePhaseNoether_canonical]

theorem sourceActualGaussCharge_hermitian : sourceActualGaussChargeMatrix.conjTranspose=sourceActualGaussChargeMatrix := by
  rw [sourceActualGaussChargeMatrix,sourcePhaseNoether_matrix]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [SourceRealScalarFock.branches,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
      eq_comm]
  all_goals
    by_cases same : i=j
    · subst j; simp
    · simp [same]

theorem sourceActualGaussCharge_coordinates (side edge : Fin 2) :
    sourceActualGaussChargeMatrix*ᵥsourceChargedCoordinates side edge=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedCoordinates side edge := by
  have primal:=congrArg Quantum.coordinates (sourceActualRestriction_noether side edge)
  rw [←Quantum.matrix_action,map_smul] at primal
  unfold sourceActualGaussChargeMatrix SourceRealScalarFock.branches sourceChargedCoordinates
  rw [Matrix.fromBlocks_mulVec]
  have left : (Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inl=Quantum.coordinates (sourceChargedRestriction side edge) := rfl
  have right : (Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inr=0 := rfl
  rw [left,right,Matrix.zero_mulVec,Matrix.zero_mulVec,Matrix.mulVec_zero,add_zero,zero_add,primal]
  funext i
  cases i with
  | inl i=>rfl
  | inr i=>simp

/-- Full CAR quantization is consumed on the actual source one-particle fiber. -/
theorem sourceActualGaussCharge_fiber (side edge : Fin 2) :
    quantized sourceActualGaussChargeMatrix (sourceChargedFiber side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedFiber side edge := by
  rw [sourceChargedFiber,quantized_oneParticle,sourceActualGaussCharge_coordinates]
  change fiberCoordinates.symm (Fermion.oneParticleLinear
    ((sourceActualPhaseCharge edge:ℂ) • sourceChargedCoordinates side edge))=_
  rw [map_smul,map_smul]
  rfl

def sourceActualGaussCharge : H→L[ℂ]H := lift (quantized sourceActualGaussChargeMatrix)

/-- The four original normalized Gauss preparations, not selected eigenbasis labels, carry the generated charges. -/
theorem sourceActualGaussCharge_prepared (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    sourceActualGaussCharge (sourceChargedGaussPrepared epsilon precision side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedGaussPrepared epsilon precision side edge := by
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  rw [map_smul]
  apply PiLp.ext
  intro word
  rw [sourceActualGaussCharge,sourceChargedGauss_action_coordinates,sourceActualGaussCharge_fiber]
  simp only [PiLp.smul_apply,sourceChargedGaussPrepared_coordinates,smul_smul,smul_eq_mul]

theorem sourceActualGaussCharge_pair (v w : H) :
    inner ℂ (sourceActualGaussCharge v) w=inner ℂ v (sourceActualGaussCharge w) := by
  apply lift_pair
  intro f g
  have generated:=SourceQuantumFockGauge.quantizedFiber_adjoint sourceActualGaussChargeMatrix f g
  rw [sourceActualGaussCharge_hermitian] at generated
  exact generated

/-- Its absolute action-unit read is generated by the same normalized original Gauss source. -/
theorem sourceActualGaussCharge_unit (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    (Stage10.ActionNormalization.phaseMomentum:ℂ)*inner ℂ
      (sourceChargedGaussPrepared epsilon precision side edge)
      (sourceActualGaussCharge (sourceChargedGaussPrepared epsilon precision side edge))=
        (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ) := by
  rw [sourceActualGaussCharge_prepared,inner_smul_right,sourceChargedGauss_gram,if_pos rfl,mul_one]

end LowEnergy.PreparationPhysicalActualGaussChargeCurrent
