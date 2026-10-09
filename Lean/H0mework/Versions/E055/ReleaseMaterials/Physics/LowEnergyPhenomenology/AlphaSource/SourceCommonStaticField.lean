import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonCurrentDetector

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCommonCurrentStaticRead
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
local instance SourceCommonStaticFieldIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationVacuumObservedStaticResidue PreparationVacuumStaticSimpleCoupling

/-- Complete origin columns of the original field occurrence; all three inverse channels remain. -/
def sourceCommonOriginColumn (i : Fin 3) : Fin 289→ℂ :=
  (originalChange 0*fullKernelFrame*slowFastFrame)*ᵥfiveVector (Pi.single ⟨i.val,by omega⟩ 1)

private def fiveLinear : (Fin 5→ℂ)→ₗ[ℂ](Fin 289→ℂ) where
  toFun:=fiveVector
  map_add' x y:=by ext i;by_cases h : i.val<5 <;> simp [fiveVector,h]
  map_smul' z x:=by ext i;by_cases h : i.val<5 <;> simp [fiveVector,h]

theorem sourceCommonJoint_channels (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) :
    sourceJointFieldResidue q n zeta.val l r=
      ∑i : Fin 3,((sourceChargedDenominator n zeta.val i)⁻¹*
        sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) ⟨i.val,by omega⟩) •
          sourceCommonOriginColumn i := by
  rw [sourceJointFieldResidue,sourceChargedCornerInverse_generated]
  have split (f : Fin 289→ℂ) : sourceChargedThreeSolution n zeta.val f=
      ∑i : Fin 3,((sourceChargedDenominator n zeta.val i)⁻¹*sourceSlowRead f ⟨i.val,by omega⟩) •
        Pi.single ⟨i.val,by omega⟩ 1 := by
    ext j
    fin_cases j <;> norm_num [sourceChargedThreeSolution,Fin.sum_univ_three,Pi.single_apply] <;>
      norm_num [Fin.ext_iff]
    exact Or.inl rfl
  rw [split]
  have linear (v : Fin 5→ℂ) : fiveVector v=fiveLinear v:=rfl
  simp only [linear,map_sum,map_smul,Matrix.mulVec_sum,Matrix.mulVec_smul]
  rfl

def sourceCommonStaticDouble (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  ∑i : Fin 3,((sourceChargedDenominator n 0 i)⁻¹*
    sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩) • sourceCommonOriginColumn i

def sourceCommonStaticSimple (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  ∑i : Fin 3,((sourceChargedDenominator n 0 i)⁻¹*
    sourceSlowRead (sourceNativeSimple q n l r) ⟨i.val,by omega⟩) • sourceCommonOriginColumn i

/-- The full 289-field static double coefficient is generated before applying a detector. -/
theorem sourceCommonStaticDouble_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^2) • sourceJointFieldResidue q n (eta:ℂ) l r)
      (𝓝[>] 0) (𝓝 (sourceCommonStaticDouble q n l r)) := by
  have slow:=sourceStaticSlow_generated q n l r
  have channel (i : Fin 3) := ((sourceChargedStaticInverse_limit n spatial i).mul
    (slow.apply_nhds ⟨i.val,by omega⟩)).smul_const (sourceCommonOriginColumn i)
  have total:=tendsto_finsetSum Finset.univ (fun i _=>channel i)
  apply total.congr'
  filter_upwards [sourceStatic_causal_eventually n spatial] with eta legal
  rw [sourceCommonJoint_channels q n ⟨(eta:ℂ),legal⟩]
  simp only [Finset.smul_sum,smul_smul,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

private theorem scalar_laurent (z D D0 X X2 : ℂ) (nz : z≠0) :
    D*(z*(X-z⁻¹^2*X2))+(z⁻¹*(D-D0))*X2=z*(D*X-z⁻¹^2*(D0*X2)) := by
  field_simp
  ring

/-- Every full-current retainer cross and the source time-reader jet remain in the simple coefficient. -/
theorem sourceCommonStaticSimple_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • (sourceJointFieldResidue q n (eta:ℂ) l r-
      ((eta:ℂ)⁻¹)^2 • sourceCommonStaticDouble q n l r))
      (𝓝[>] 0) (𝓝 (sourceCommonStaticSimple q n l r)) := by
  have slow:=sourceSlow_simple_generated q n l r
  have channel (i : Fin 3) := (((sourceChargedStaticInverse_limit n spatial i).mul
    (slow.apply_nhds ⟨i.val,by omega⟩)).add
    ((sourceChargedStaticInverse_slope n spatial i).mul_const
      (sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩))).smul_const (sourceCommonOriginColumn i)
  have total:=tendsto_finsetSum Finset.univ (fun i _=>channel i)
  simp only [zero_mul,add_zero] at total
  apply total.congr'
  filter_upwards [sourceStatic_causal_eventually n spatial,self_mem_nhdsWithin] with eta legal positive
  rw [sourceCommonJoint_channels q n ⟨(eta:ℂ),legal⟩,sourceCommonStaticDouble]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,
    smul_sub]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←sub_smul]
  congr 1
  rw [scalar_laurent _ _ _ _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
  ring

section Detector
variable (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum) (a b : RestStateIndex)
  (lambda : ℂ) (T : ℝ)
local notation "D" => sourceCommonDetector qd pDL pDR a b lambda T

/-- The actual full detector consumes the original constrained Jacobi equation. -/
theorem sourceCommonCausal_whole (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) (d : sourceCausalScale n zeta) :
    D (originalJacobi (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥsourceJointCausalField q n zeta.val l r d.val)=
      D (returnedHalfCurrent q (-(d.val • n)) 0 l r ((d.val:ℂ)*zeta.val))-
      D (originalRowLift (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥ
        (nullProjection*ᵥ(originalReadback (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥ
          returnedHalfCurrent q (-(d.val • n)) 0 l r ((d.val:ℂ)*zeta.val)))) := by
  rw [sourceJointCausalField_whole,map_sub]

/-- The common-current observation takes the original full-field radial limit. -/
theorem sourceCommonCausal_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ)^3*D (sourceJointCausalField q n zeta.val l r d))
      (𝓝[>] 0) (𝓝 (D (sourceJointFieldResidue q n zeta.val l r))) := by
  have generated:=(D).continuous.continuousAt.tendsto.comp
    (sourceJointCausalField_residue q n zeta l r nonrealL nonrealR)
  simpa only [Function.comp_def,map_smul,smul_eq_mul] using generated

theorem sourceCommonStatic_read (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)^2*D (sourceJointFieldResidue q n (eta:ℂ) l r))
      (𝓝[>] 0) (𝓝 (D (sourceCommonStaticDouble q n l r))) ∧
    Tendsto (fun eta : ℝ=>(eta:ℂ)*(D (sourceJointFieldResidue q n (eta:ℂ) l r)-
      ((eta:ℂ)⁻¹)^2*D (sourceCommonStaticDouble q n l r)))
      (𝓝[>] 0) (𝓝 (D (sourceCommonStaticSimple q n l r))) := by
  constructor
  · have generated:=(D).continuous.continuousAt.tendsto.comp (sourceCommonStaticDouble_generated q n spatial l r)
    simpa only [Function.comp_def,map_smul,smul_eq_mul] using generated
  · have generated:=(D).continuous.continuousAt.tendsto.comp (sourceCommonStaticSimple_generated q n spatial l r)
    simpa only [Function.comp_def,map_smul,map_sub,smul_eq_mul] using generated

/-- The exact next frame expression keeps its full origin, full residual and independent regular/contact return. -/
theorem sourceCommonFrame_return (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (l r : RestStateIndex) (z : ℂ) :
    D (sourceChargedActualFrameField q n zeta l r z+
      z • (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n zeta l r))=
      D (sourceJointFieldResidue q n zeta l r)+z*D (sourceChargedSecondField q n zeta l r)+
        D (sourceChargedActualFieldResidual q n zeta l r z) := by
  have generated:=congrArg D (sourceChargedActualField_first_return q n zeta l r z)
  simp only [map_sub,map_smul,smul_eq_mul] at generated
  simp only [map_add,map_smul,smul_eq_mul,sourceChargedSecondField]
  linear_combination generated

end Detector
end LowEnergy.PreparationPhysicalCommonCurrentStaticRead
