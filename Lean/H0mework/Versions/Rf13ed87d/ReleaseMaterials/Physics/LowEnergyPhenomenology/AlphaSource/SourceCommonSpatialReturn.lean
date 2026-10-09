import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonSpatialFourier
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPreparedDetector

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCommonSpatialGreen
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
local instance CommonSpatialReturnIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalCommonObservableUnits PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumGaugeSlowFrequency PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumObservedPoleTensor
open PreparationVacuumActualSpatialPacket
open scoped Matrix.Norms.Operator SchwartzMap

open PreparationPhysicalActualGaussChargeCurrent

/-- The zeroth moment is the same spatial channel for every derivative axis. -/
theorem sourceCommonSpatialMoment_zero (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (i j : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceCommonSpatialMoment q c eta l r i j 0 test x=sourceCommonSpatialMoment q c eta l r i 0 0 test x := by
  simp only [sourceCommonSpatialMoment,sourceCommonMomentIntegrand,pow_zero,one_mul]

/-- Actual second coordinate derivatives, rather than a named Fourier multiplier. -/
theorem sourceCommonSpatial_second (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i j : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    deriv (fun t : ℝ=>deriv (fun s : ℝ=>sourceCommonSpatialMoment q c eta l r i 0 0 test
      (x+s • (Pi.single j 1 : PhysicalMomentum))) t) 0=sourceCommonSpatialMoment q c eta l r i j 2 test x := by
  have first : (fun t : ℝ=>deriv (fun s : ℝ=>sourceCommonSpatialMoment q c eta l r i 0 0 test
      (x+s • (Pi.single j 1 : PhysicalMomentum))) t)=fun t=>sourceCommonSpatialMoment q c eta l r i j 1 test (x+t • (Pi.single j 1 : PhysicalMomentum)) := by
    funext t
    have h:=sourceCommonMoment_derivative q c eta nonzero positive l r i j 0 test x t
    simp only [sourceCommonSpatialMoment_zero] at h
    exact h.deriv
  rw [first,(sourceCommonMoment_derivative q c eta nonzero positive l r i j 1 test x 0).deriv]
  simp only [zero_smul,add_zero]

def sourceCommonSpatialLaplacian (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∑j : Fin 3,deriv (fun t : ℝ=>deriv (fun s : ℝ=>sourceCommonSpatialMoment q c eta l r i 0 0 test
    (x+s • (Pi.single j 1 : PhysicalMomentum))) t) 0

def sourceCommonSpatialForcing (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫frequency,sourceSpatialPhase frequency x*test frequency*
    sourceSlowRead (sourceActualNativeResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r) ⟨i.val,by omega⟩

private theorem forcing_integrand (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x frequency : PhysicalMomentum) :
    sourceSpatialPhase frequency x*test frequency*
      sourceSlowRead (sourceActualNativeResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r) ⟨i.val,by omega⟩=
      -(sourceChargedSpatialCoefficient i:ℂ)*(∑j : Fin 3,sourceCommonMomentIntegrand q c eta l r i j 2 test x frequency)+
        (sourceChargedTemporalCoefficient i:ℂ)*(sourcePoleSide c eta)^2*
          sourceCommonMomentIntegrand q c eta l r i 0 0 test x frequency := by
  let n:=sourceSpatialMomentum frequency
  let zeta:=sourcePoleSide c eta
  have canceled : sourceSlowRead (sourceActualNativeResidue q n zeta l r) ⟨i.val,by omega⟩=
      sourceChargedDenominator n zeta i*sourceCommonCausalChannel q n zeta l r i := by
    rw [sourceCommonCausalChannel,←mul_assoc,
      mul_inv_cancel₀ (sourceChargedDenominator_nonzero n c eta nonzero positive i),one_mul]
  change sourceSpatialPhase frequency x*test frequency*sourceSlowRead (sourceActualNativeResidue q n zeta l r) _=_
  rw [canceled]
  simp only [sourceCommonMomentIntegrand,Fin.sum_univ_three,pow_zero,one_mul]
  simp only [sourceChargedDenominator,spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]
  dsimp only [n,zeta]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem sourceCommonSpatialForcing_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun frequency=>sourceSpatialPhase frequency x*test frequency*
      sourceSlowRead (sourceActualNativeResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r) ⟨i.val,by omega⟩) := by
  simp_rw [forcing_integrand q c eta nonzero positive l r i test x]
  exact ((integrable_finsetSum _ (fun j _=>sourceCommonMoment_integrable q c eta nonzero positive l r i j 2 test x)).const_mul _).add
    ((sourceCommonMoment_integrable q c eta nonzero positive l r i 0 0 test x).const_mul _)

/-- The original three field denominators become their actual spatial second-order equations, with complete source forcing. -/
theorem sourceCommonSpatial_equation (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    -(sourceChargedSpatialCoefficient i:ℂ)*sourceCommonSpatialLaplacian q c eta l r i test x+
      (sourceChargedTemporalCoefficient i:ℂ)*(sourcePoleSide c eta)^2*
        sourceCommonSpatialMoment q c eta l r i 0 0 test x=sourceCommonSpatialForcing q c eta l r i test x := by
  unfold sourceCommonSpatialForcing
  simp_rw [forcing_integrand q c eta nonzero positive l r i test x]
  rw [integral_add
    ((integrable_finsetSum _ (fun j _=>sourceCommonMoment_integrable q c eta nonzero positive l r i j 2 test x)).const_mul _)
    ((sourceCommonMoment_integrable q c eta nonzero positive l r i 0 0 test x).const_mul _),
    integral_const_mul,integral_const_mul,
    integral_finsetSum _ (fun j _=>sourceCommonMoment_integrable q c eta nonzero positive l r i j 2 test x)]
  simp only [sourceCommonSpatialLaplacian,sourceCommonSpatial_second q c eta nonzero positive]
  rfl

/-- Complete full289 inverse spatial Fourier field, before any action detector. -/
def sourceCommonSpatialField (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∫frequency,(sourceSpatialPhase frequency x*test frequency) •
    sourceJointFieldResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r

theorem sourceCommonSpatialField_generated (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceCommonSpatialField q c eta l r test x=
      ∑i : Fin 3,sourceCommonSpatialMoment q c eta l r i 0 0 test x • sourceCommonOriginColumn i := by
  have same (frequency : PhysicalMomentum) :
      (sourceSpatialPhase frequency x*test frequency) •
        sourceJointFieldResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r=
      ∑i : Fin 3,sourceCommonMomentIntegrand q c eta l r i 0 0 test x frequency • sourceCommonOriginColumn i := by
    rw [sourceCommonJoint_channels q _ ⟨_,sourcePoleSide_field_domain _ c eta nonzero positive⟩]
    simp only [Finset.smul_sum,smul_smul,sourceCommonMomentIntegrand,pow_zero,one_mul,sourceCommonCausalChannel]
  unfold sourceCommonSpatialField
  simp_rw [same]
  rw [integral_finsetSum _ (fun i _=>(sourceCommonMoment_integrable q c eta nonzero positive l r i 0 0 test x).smul_const _)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_smul_const _ _

/-- The actual action detector contracts the spatial field; the field still contains all three full columns. -/
theorem sourceCommonSpatialField_gauss (qd q : PhysicalResponsePoint) (a b l r : RestStateIndex)
    (T c eta : ℝ) (nonzero : c≠0) (positive : 0<eta)
    (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceCommonDetector qd 0 0 a b 0 T (sourceCommonSpatialField q c eta l r test x)=
      (sourceCommonSpatialMoment q c eta l r 0 0 0 test x+
        sourceCommonSpatialMoment q c eta l r 1 0 0 test x)*actualGaussWeight qd a b T := by
  rw [sourceCommonSpatialField_generated q c eta nonzero positive l r test x]
  simp only [map_add,map_smul,smul_eq_mul,Fin.sum_univ_three]
  have first:=sourceObservableOrigin_branch 0
  have second:=sourceObservableOrigin_branch 1
  change sourceCommonOriginColumn 1=nativeBranchVector 0 at first
  change sourceCommonOriginColumn 2=nativeBranchVector 1 at second
  rw [first,second,sourceObservableColumnZero_read qd a b T nonrealL nonrealR,
    sourceCommonDetector_gauss qd a b T 0 nonrealL nonrealR,
    sourceCommonDetector_gauss qd a b T 1 nonrealL nonrealR]
  norm_num
  ring

private theorem weighted_field_integrable (F : PhysicalMomentum→(Fin 289→ℂ))
    (continuous : Continuous F) (K : ℝ) (bound : ∀n,‖F n‖≤K)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun frequency=>(sourceSpatialPhase frequency x*test frequency) • F (sourceSpatialMomentum frequency)) := by
  have integrand : Continuous (fun frequency=>(sourceSpatialPhase frequency x*test frequency) • F (sourceSpatialMomentum frequency)) := by
    unfold sourceSpatialPhase sourceSpatialMomentum
    fun_prop
  apply (test.integrable.norm.const_mul K).mono' integrand.aestronglyMeasurable
  filter_upwards with frequency
  have phase : ‖sourceSpatialPhase frequency x‖=1 := by simp [sourceSpatialPhase,Complex.norm_exp]
  rw [norm_smul,norm_mul,phase,one_mul,mul_comm K]
  exact mul_le_mul_of_nonneg_left (bound _) (norm_nonneg _)

/-- The next spatial field keeps the genuine native first frame jet and independent regular/contact field. -/
def sourceCommonSpatialSecond (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∫frequency,(sourceSpatialPhase frequency x*test frequency) •
    sourceChargedSecondField q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r

def sourceCommonSpatialNativeJet (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∫frequency,(sourceSpatialPhase frequency x*test frequency) •
    sourceChargedActualFieldJet q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r

def sourceCommonSpatialRegular (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∫frequency,(sourceSpatialPhase frequency x*test frequency) •
    (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r)

/-- Both summands are source-integrable before spatial reconstruction; no regular/contact term is discarded. -/
theorem sourceCommonSpatialSecond_return (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceCommonSpatialSecond q c eta l r test x=
      sourceCommonSpatialNativeJet q c eta l r test x+sourceCommonSpatialRegular q c eta l r test x := by
  have native:=weighted_field_integrable _ (sourceChargedNative_continuous q c eta nonzero positive l r)
    _ (fun n=>sourceChargedNative_uniform q n c eta nonzero positive l r) test x
  have regular:=weighted_field_integrable _ (sourceChargedRegular_continuous q c eta positive l r)
    _ (fun n=>sourceChargedRegular_uniform q n c eta positive l r) test x
  simp only [sourceCommonSpatialSecond,sourceChargedSecondField,smul_add]
  rw [integral_add native regular]
  rfl

/-- Original generated propagation sides supply the spatial equation; damping remains a fixed positive observation parameter. -/
theorem sourceCommonSpatial_sourceSide (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    -(sourceChargedSpatialCoefficient i:ℂ)*sourceCommonSpatialLaplacian q (sourceSignedSpeed branch negative) eta l r i test x+
      (sourceChargedTemporalCoefficient i:ℂ)*(sourcePoleSide (sourceSignedSpeed branch negative) eta)^2*
        sourceCommonSpatialMoment q (sourceSignedSpeed branch negative) eta l r i 0 0 test x=
      sourceCommonSpatialForcing q (sourceSignedSpeed branch negative) eta l r i test x :=
  sourceCommonSpatial_equation q _ eta (sourceSignedSpeed_nonzero branch negative) positive l r i test x

/-- Both original source preparations use their actual fixed-zero-basis expansion, whose moving dependence already remains inside the returned current. -/
def sourceActualSpatialField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (c eta : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∫frequency,(sourceSpatialPhase frequency x*test frequency) •
    (∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
      sourceJointFieldResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r)

theorem sourceActualSpatialField_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (nonzero : c≠0) (positive : 0<eta)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualSpatialField q sL eL sR eR c eta test x=
      ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
        sourceCommonSpatialField q c eta l r test x := by
  have same (frequency : PhysicalMomentum) :
      (sourceSpatialPhase frequency x*test frequency) •
        (∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
          sourceJointFieldResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r)=
      ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
        ((sourceSpatialPhase frequency x*test frequency) •
          sourceJointFieldResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r) := by
    simp only [Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_comm]
  have weighted (l r : RestStateIndex) : Integrable (fun frequency=>
      sourceActualPreparedWeight 0 0 sL eL sR eR l r • ((sourceSpatialPhase frequency x*test frequency) •
        sourceJointFieldResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r)) := by
    let weight:=sourceActualPreparedWeight 0 0 sL eL sR eR l r
    have h:=weighted_field_integrable (fun n=>weight • sourceJointFieldResidue q n (sourcePoleSide c eta) l r)
      ((sourceCommonField_continuous q c eta nonzero positive l r).const_smul weight)
      (‖weight‖*sourceCommonFieldPrice q c eta l r)
      (fun n=>by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (sourceCommonField_bound q n c eta nonzero positive l r) (norm_nonneg weight)) test x
    convert h using 1
    funext frequency
    exact smul_comm _ _ _
  have summed (l : RestStateIndex) : Integrable (fun frequency=>∑r : RestStateIndex,
      sourceActualPreparedWeight 0 0 sL eL sR eR l r • ((sourceSpatialPhase frequency x*test frequency) •
        sourceJointFieldResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r)) :=
    integrable_finsetSum Finset.univ (fun r _=>weighted l r)
  unfold sourceActualSpatialField
  simp_rw [same]
  rw [integral_finsetSum Finset.univ (fun l _=>summed l)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finsetSum Finset.univ (fun r _=>weighted l r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_smul]
  rfl

def sourceActualSpatialAmplitude (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (c eta : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r*
    (sourceCommonSpatialMoment q c eta l r 0 0 0 test x+sourceCommonSpatialMoment q c eta l r 1 0 0 test x)

private theorem actual_detector_gauss (qd q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (l r : RestStateIndex) (T c eta : ℝ) (nonzero : c≠0) (positive : 0<eta)
    (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualPreparedDetector qd 0 0 sL eL sR eR 0 T (sourceCommonSpatialField q c eta l r test x)=
      (sourceCommonSpatialMoment q c eta l r 0 0 0 test x+sourceCommonSpatialMoment q c eta l r 1 0 0 test x)*
        (∑a : RestStateIndex,∑b : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR a b*actualGaussWeight qd a b T) := by
  simp only [sourceActualPreparedDetector,sum_apply,smul_apply,smul_eq_mul,
    sourceCommonSpatialField_gauss qd q _ _ l r T c eta nonzero positive nonrealL nonrealR test x]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Actual source64 and detector64 preparations meet in the same full spatial observable, retaining every original cross coefficient. -/
theorem sourceActualSpatialDetector_generated (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
      (sourceActualSpatialField q sL eL sR eR c eta test x)=
      sourceActualSpatialAmplitude q sL eL sR eR c eta test x*
        (∑a : RestStateIndex,∑b : RestStateIndex,sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*actualGaussWeight qd a b T) := by
  rw [sourceActualSpatialField_generated q sL eL sR eR c eta nonzero positive test x]
  simp only [map_sum,map_smul,smul_eq_mul,
    actual_detector_gauss qd q dSL dEL dSR dER _ _ T c eta nonzero positive nonrealL nonrealR test x,
    sourceActualSpatialAmplitude,Finset.sum_mul,mul_assoc]

/-- The original four actual Gauss preparations consume the spatial field through their unchanged complete action kernel. -/
theorem sourceActualSpatialDetector_action (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T c eta : ℝ)
    (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
      (sourceActualSpatialField q sL eL sR eR c eta test x)=
      -sourceQuantumChargedRead qd dSL dEL dSR dER
        (sourceActualPreparedKernel qd 0 0 0 T (sourceActualSpatialField q sL eL sR eR c eta test x)) :=
  sourceActualPreparedDetector_action qd 0 0 dSL dEL dSR dER 0 T _ nonrealL nonrealR

end LowEnergy.PreparationPhysicalCommonSpatialGreen
