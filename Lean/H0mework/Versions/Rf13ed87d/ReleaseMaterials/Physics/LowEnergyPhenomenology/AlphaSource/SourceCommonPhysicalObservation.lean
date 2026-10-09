import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonPhysicalUnits

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
local instance SourceCommonPhysicalObservationIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- Held matter/dual source support is consumed at the original zero-momentum detector, not erased from the field. -/
theorem sourceObservableColumnZero_read (q : PhysicalResponsePoint) (l r : RestStateIndex)
    (T : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceCommonDetector q 0 0 l r 0 T (sourceCommonOriginColumn 0)=actualGaussWeight q l r T := by
  rw [sourceCommonDetector_current,returnedCurrentWindow_zero]
  have vector : fiveVector (Pi.single (0:Fin 5) (1:ℂ))=Pi.single (0:Fin 289) 1 := by
    funext i
    by_cases inside : i.val<5
    · by_cases zero : i=0
      · subst i
        rfl
      · have zero5 : (⟨i.val,inside⟩:Fin 5)≠0 := by
          intro same
          have values : i.val=0 := congrArg (fun j : Fin 5=>j.val) same
          exact zero (Fin.ext values)
        simp only [fiveVector,dif_pos inside,Pi.single_eq_of_ne zero5,Pi.single_eq_of_ne zero]
    · have outside : i≠0 := by intro same;subst i;norm_num at inside
      simp only [fiveVector,dif_neg inside,Pi.single_eq_of_ne outside]
  change actualCurrent q 0 0 l r 0 T ⬝ᵥ
    ((fullNativeOrigin*slowFastFrame)*ᵥfiveVector (Pi.single 0 1))=_
  rw [vector,Matrix.dotProduct_mulVec,dotProduct_single_one]
  have transpose : (actualCurrent q 0 0 l r 0 T ᵥ* (fullNativeOrigin*slowFastFrame)) 0=
      (slowFastFrame.transpose*ᵥ(fullNativeOrigin.transpose*ᵥactualCurrent q 0 0 l r 0 T)) 0 := by
    rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,Matrix.mulVec_transpose]
  rw [transpose,actual_origin_kernel_read]
  have weight (w : ℂ) : (slowFastFrame.transpose*ᵥ(Pi.single 0 w+Pi.single 1 w)) 0=w := by
    simp only [Matrix.mulVec_add,Matrix.mulVec_single,Pi.add_apply]
    norm_num [slowFastFrame,slowFastFrameTerms,sourceMatrix,SourceTerm.matrix,
      Powers.value,coefficientValue,Matrix.single_apply,Matrix.transpose_apply,Fin.ext_iff,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]
  rw [weight]
  exact actualOriginWeight_completeGauss q l r T nonrealL nonrealR

/-- The complete contracted static coefficient: all gauge, retainer and source-time jet terms survive in the channel sum. -/
theorem sourceObservableStatic_generated (qd q : PhysicalResponsePoint) (a b l r : RestStateIndex)
    (T : ℝ) (n : PhysicalMomentum) (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0) :
    sourceCommonDetector qd 0 0 a b 0 T (sourceCommonCoulombTensor q n l r)=
      (sourceObservableChannel q n l r 0+sourceObservableChannel q n l r 1)*actualGaussWeight qd a b T := by
  rw [sourceObservableGauss_channels qd q a b l r T n nonrealL nonrealR,
    sourceObservableColumnZero_read qd a b T nonrealL nonrealR,add_mul]

/-- This directional source strength is generated before any isotropic potential or electron identification. -/
theorem sourceObservableStrength_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (a b l r : RestStateIndex) (T : ℝ) (n : PhysicalMomentum)
    (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0) :
    sourceCommonDetector qd 0 0 a b 0 T (sourceObservableReducedTensor branch q n l r)=
      ((sourceObservableChannel q n l r 0+sourceObservableChannel q n l r 1)*actualGaussWeight qd a b T)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) := by
  rw [sourceObservableReducedTensor,map_smul,smul_eq_mul,
    sourceObservableStatic_generated qd q a b l r T n nonrealL nonrealR]
  exact (div_eq_inv_mul _ _).symm

/-- The actual static Laurent read and propagation-sheet normalization are sequential source limits, with no exchange of limits. -/
theorem sourceObservableStrength_limit (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (a b l r : RestStateIndex) (T : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0) :
    Tendsto (fun e=>sourceCommonDetector qd 0 0 a b 0 T
      (sourceObservableFiniteReducedTensor branch q n unit l r e)) scaleApproach
      (𝓝 (((sourceObservableChannel q n l r 0+sourceObservableChannel q n l r 1)*actualGaussWeight qd a b T)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ))) := by
  have result:=(sourceCommonDetector qd 0 0 a b 0 T).continuous.tendsto _ |>.comp
    (sourceObservableReducedTensor_generated branch q n unit l r)
  rw [sourceObservableStrength_generated branch qd q a b l r T n nonrealL nonrealR] at result
  exact result

/-- The full retarded window and the independent full-field flux use the very same physical wave number and source phase speed. -/
theorem sourceObservableRetarded_flux (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) :
    ∀ᶠ e in scaleApproach,
      (2*((sourceObservablePhaseSpeed branch n unit e*sourceObservableWaveNumber n e:ℝ):ℂ))^2 •
        sourcePhysicalResidueWindow sideL edgeL sideR edgeR legs branch n unit energy damping T e=
          sourceActualRetardedValue sideL edgeL sideR edgeR legs branch n unit energy damping T e ∧
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (sourcePhotonFrequencyJacobiJet e.val
          (sourceObservablePhaseSpeed branch n unit e*sourceObservableWaveNumber n e) n*ᵥ
            sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)=1 := by
  filter_upwards [sourceActualRetardedWard_return sideL edgeL sideR edgeR legs branch n unit energy damping T,
    sourceNativePolarization_frequencyFlux branch n unit] with e window flux
  have frequency : sourceObservablePhaseSpeed branch n unit e*sourceObservableWaveNumber n e=
      sourceFrequency e.val (sourceSheet branch n unit e.val) := by
    rw [sourceObservablePhaseSpeed_generated,sourceObservableWaveNumber_generated n unit e,sourceFrequency,mul_comm]
  rw [frequency]
  exact ⟨window,flux⟩

end LowEnergy.PreparationPhysicalCommonObservableUnits
