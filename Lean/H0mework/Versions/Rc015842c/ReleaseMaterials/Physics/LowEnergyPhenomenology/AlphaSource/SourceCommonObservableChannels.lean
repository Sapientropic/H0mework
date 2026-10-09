import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonPropagationRead
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualRetardedObservation

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCommonObservableUnits
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
local instance SourceCommonPropagationReadIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationVacuumStaticPoleResponse PreparationVacuumFullOriginResponse

open PreparationVacuumStaticSpatialSource PreparationVacuumStaticSimpleCoupling

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalActualRetardedWard

/-- Each coefficient still contains all original gauge, retainer cross and time-reader terms. -/
def sourceObservableChannel (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (i : Fin 3) : ℂ :=
  (sourceChargedSpatialCoefficient i:ℂ)⁻¹*
    sourceSlowRead (sourceNativeSimple q n l r) ⟨i.val,by omega⟩

theorem sourceObservableOrigin_branch (branch : Fin 2) :
    sourceCommonOriginColumn ⟨(residueIndex branch).val,by
      fin_cases branch <;> norm_num [residueIndex]⟩=nativeBranchVector branch := by
  simp only [sourceCommonOriginColumn,nativeBranchVector,Matrix.mulVec_mulVec,Matrix.mul_assoc]

/-- Both propagation columns and the independent full zeroth column are retained before any detector. -/
theorem sourceObservableTensor_channels (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) :
    sourceCommonCoulombTensor q n l r=
      sourceObservableChannel q n l r 0 • sourceCommonOriginColumn 0+
      sourceObservableChannel q n l r 1 • nativeBranchVector 0+
      sourceObservableChannel q n l r 2 • nativeBranchVector 1 := by
  have first:=sourceObservableOrigin_branch 0
  have second:=sourceObservableOrigin_branch 1
  change sourceCommonOriginColumn 1=nativeBranchVector 0 at first
  change sourceCommonOriginColumn 2=nativeBranchVector 1 at second
  simp only [sourceCommonCoulombTensor,Fin.sum_univ_three,sourceObservableChannel,first,second]

theorem sourceObservableChannel_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3) :
    sourceObservableChannel q (s • n) l r i=sourceObservableChannel q n l r i := by
  simp only [sourceObservableChannel,sourceNativeSimple_radial q n s positive]

section Detector
variable (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum) (a b : RestStateIndex)
  (lambda : ℂ) (T : ℝ)
local notation "D" => sourceCommonDetector qd pDL pDR a b lambda T

theorem sourceObservableDetector_channels (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) :
    D (sourceCommonCoulombTensor q n l r)=
      sourceObservableChannel q n l r 0*D (sourceCommonOriginColumn 0)+
      sourceObservableChannel q n l r 1*D (nativeBranchVector 0)+
      sourceObservableChannel q n l r 2*D (nativeBranchVector 1) := by
  rw [sourceObservableTensor_channels]
  simp only [map_add,map_smul,smul_eq_mul]
end Detector

/-- The actual zero-momentum detector suppresses branch1 by its paid source action; channel0 is not deleted. -/
theorem sourceObservableGauss_channels (qd q : PhysicalResponsePoint) (a b l r : RestStateIndex)
    (T : ℝ) (n : PhysicalMomentum) (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0) :
    sourceCommonDetector qd 0 0 a b 0 T (sourceCommonCoulombTensor q n l r)=
      sourceObservableChannel q n l r 0*sourceCommonDetector qd 0 0 a b 0 T (sourceCommonOriginColumn 0)+
      sourceObservableChannel q n l r 1*actualGaussWeight qd a b T := by
  rw [sourceObservableDetector_channels,
    sourceCommonDetector_gauss qd a b T 0 nonrealL nonrealR,
    sourceCommonDetector_gauss qd a b T 1 nonrealL nonrealR]
  norm_num

/-- The original double subtraction is carried through before this complete three-channel simple read. -/
theorem sourceObservableStatic_simple (qd q : PhysicalResponsePoint) (a b l r : RestStateIndex)
    (T : ℝ) (n : PhysicalMomentum) (spatial : 0<spatialSquare n)
    (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*(sourceCommonDetector qd 0 0 a b 0 T
      (sourceJointFieldResidue q n (eta:ℂ) l r)-((eta:ℂ)⁻¹)^2*
      sourceCommonDetector qd 0 0 a b 0 T (sourceCommonStaticDouble q n l r)))
      (𝓝[>] 0) (𝓝 ((spatialSquare n:ℂ)⁻¹*
        (sourceObservableChannel q n l r 0*sourceCommonDetector qd 0 0 a b 0 T (sourceCommonOriginColumn 0)+
         sourceObservableChannel q n l r 1*actualGaussWeight qd a b T))) := by
  have result:=(sourceCommonStatic_read qd 0 0 a b 0 T q n spatial l r).2
  rw [sourceCommonStaticCoulomb_read,sourceObservableGauss_channels qd q a b l r T n nonrealL nonrealR] at result
  exact result

end LowEnergy.PreparationPhysicalCommonObservableUnits
