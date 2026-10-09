import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaussPolarizationTensor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualPolarizationResponse
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
local instance polarizationReadQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
local instance polarizationReadModeIndex : DecidableEq Mode:=Classical.decEq _

open PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentRegularAnchor PreparationVacuumPhysicalPoleAmputation

open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumPhysicalPoleLegDynamics
open Stage9DEF Stage9DEF.Compatibility
attribute [local irreducible] jointGenerator jointResolvent sourceChargedGaussPrepared

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

open PreparationPhysicalActualLegNormalization PreparationVacuumPhysicalTailPrice
local instance polarizationReadOperatorReal : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian

attribute [local irreducible] physicalTime timeSlope PreparationVacuumRawJointFeedback.rawReader rawReaderContact


open PreparationPhysicalActualUnitFourPointReturn PreparationPhysicalUnitCurrentFieldReturn
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstPoleGaugeRemainder
open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalFinitePoleVertices PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumActionFieldLift

attribute [local irreducible] sourceGaussPolarizationPair sourceUnitRead sourceUnitFourPointPair
  sourceUnitCompleteField sourceUnitComplexMixed sourceNativeFrequencyPolarization sourceFinitePoleComponents

def sourceGaussBareResponseCurve (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (v w : Fin 289→ℂ) (r : ℝ) : ℂ :=
  sourceQuantumChargedRead q sL eL sR eR (jointVertex (fun i=>(w i).re) 0 0 q.F q.z q.w (r • (fun i=>(v i).re)))-
  sourceQuantumChargedRead q sL eL sR eR (jointVertex (fun i=>(w i).im) 0 0 q.F q.z q.w (r • (fun i=>(v i).im)))+
  Complex.I*(sourceQuantumChargedRead q sL eL sR eR
      (jointVertex (fun i=>(w i).im) 0 0 q.F q.z q.w (r • (fun i=>(v i).re)))+
    sourceQuantumChargedRead q sL eL sR eR
      (jointVertex (fun i=>(w i).re) 0 0 q.F q.z q.w (r • (fun i=>(v i).im))))

/-- The complete actual finite-polarization tensor is the original source derivative with its two measured amputation gaps, not a new tensor witness. -/
theorem sourceGaussPolarization_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (v w : Fin 289→ℂ) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>
      (sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))*
          sourceGaussBareResponseCurve q sL eL sR eR v w r)
      ((sourceGaussPolarizationPair q sL eL sR eR v w).1+
        (sourceGaussPolarizationPair q sL eL sR eR v w).2) 0 := by
  have rr:=sourceUnitFourPoint_generated q sL eL sR eR (fun i=>(v i).re) (fun i=>(w i).re) left right
  have ii:=sourceUnitFourPoint_generated q sL eL sR eR (fun i=>(v i).im) (fun i=>(w i).im) left right
  have ri:=sourceUnitFourPoint_generated q sL eL sR eR (fun i=>(v i).re) (fun i=>(w i).im) left right
  have ir:=sourceUnitFourPoint_generated q sL eL sR eR (fun i=>(v i).im) (fun i=>(w i).re) left right
  have result:=(rr.sub ii).add ((ri.add ir).const_mul Complex.I)
  refine (result.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [sourceGaussPolarizationPair_quadratures]
    simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  · filter_upwards [] with r
    simp only [Pi.add_apply,Pi.sub_apply,sourceGaussBareResponseCurve]
    ring

private def realPairPrice (q : PhysicalResponsePoint) (f g : Field289) : ℝ :=
  ‖jointCurrent 0 q.F q.z 0 f‖*‖jointResolvent 0 q.F q.z 0‖*‖jointCurrent 0 q.F q.w 0 g‖+
  ‖jointCurrent 0 q.F q.w 0 g‖*‖jointResolvent 0 q.F q.w 0‖*‖jointCurrent 0 q.F q.w 0 f‖+
  ‖jointHessian 0 q.F q.w f g‖

private theorem realPair_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (f g : Field289)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖sourceUnitFourPointPair q sL eL sR eR f g‖ ≤ realPairPrice q f g := by
  have price:=sourceUnitFourPoint_bound q sL eL sR eR f g left right
  rw [Prod.norm_def]
  apply max_le
  · exact price.1.trans (le_add_of_nonneg_right (norm_nonneg _))
  · exact price.2.trans (le_add_of_nonneg_left (add_nonneg (by positivity) (by positivity)))

def sourceGaussPolarizationPrice (q : PhysicalResponsePoint) (v w : Fin 289→ℂ) : ℝ :=
  realPairPrice q (fun i=>(v i).re) (fun i=>(w i).re)+
  realPairPrice q (fun i=>(v i).im) (fun i=>(w i).im)+
  (realPairPrice q (fun i=>(v i).re) (fun i=>(w i).im)+
   realPairPrice q (fun i=>(v i).im) (fun i=>(w i).re))

theorem sourceGaussPolarization_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (v w : Fin 289→ℂ) (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖sourceGaussPolarizationPair q sL eL sR eR v w‖ ≤ sourceGaussPolarizationPrice q v w := by
  rw [sourceGaussPolarizationPair_quadratures]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_sub_le _ _).trans (add_le_add (realPair_bound q sL eL sR eR _ _ left right)
      (realPair_bound q sL eL sR eR _ _ left right))
  · rw [norm_smul,Complex.norm_I,one_mul]
    exact (norm_add_le _ _).trans (add_le_add (realPair_bound q sL eL sR eR _ _ left right)
      (realPair_bound q sL eL sR eR _ _ left right))

/-- The whole nine origin/jet/residual crosses carry their actual independent material prices; no uniform gap or source averaging is introduced. -/
theorem sourceGaussWholePolarization_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (a b : Fin 2) (epsilon s t : ℝ) (n m : PhysicalMomentum) (nonzero : epsilon≠0)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖sourceGaussPolarizationPair q sL eL sR eR
      (sourceNativeFrequencyPolarization a epsilon s n) (sourceNativeFrequencyPolarization b epsilon t m)‖ ≤
      ∑i : Fin 3,∑j : Fin 3,sourceGaussPolarizationPrice q
        (sourceFinitePoleComponents a epsilon s n i) (sourceFinitePoleComponents b epsilon t m j) := by
  rw [sourceGaussWholePolarization_return q sL eL sR eR a b epsilon s t n m nonzero]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _=>sourceGaussPolarization_bound q sL eL sR eR _ _ left right)

/-- The original finite source polarization, including all nine literal/fast/origin/residual crosses, is returned by the actual amputated Gauss derivative. -/
theorem sourceActualPolarization_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (a b : Fin 2) (epsilon s t : ℝ) (n m : PhysicalMomentum) (nonzero : epsilon≠0)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>
      (sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))*
      sourceGaussBareResponseCurve q sL eL sR eR
        (sourceNativeFrequencyPolarization a epsilon s n) (sourceNativeFrequencyPolarization b epsilon t m) r)
      ((∑i : Fin 3,∑j : Fin 3,sourceGaussPolarizationPair q sL eL sR eR
          (sourceFinitePoleComponents a epsilon s n i) (sourceFinitePoleComponents b epsilon t m j)).1+
        (∑i : Fin 3,∑j : Fin 3,sourceGaussPolarizationPair q sL eL sR eR
          (sourceFinitePoleComponents a epsilon s n i) (sourceFinitePoleComponents b epsilon t m j)).2) 0 := by
  have actual:=sourceGaussPolarization_generated q sL eL sR eR
    (sourceNativeFrequencyPolarization a epsilon s n) (sourceNativeFrequencyPolarization b epsilon t m) left right
  rw [sourceGaussWholePolarization_return q sL eL sR eR a b epsilon s t n m nonzero] at actual
  exact actual

/-- The same original unit-current Gamma fields feed a complete Gauss response on their own actual legs. This statement does not identify the Gauss carrier with the independent spatial-packet carrier. -/
def sourceGaussCompleteFieldResponse (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left right : SourceUnitFieldLeg) : ℂ × ℂ :=
  sourceGaussPolarizationPair q sL eL sR eR (sourceUnitCompleteField left) (sourceUnitCompleteField right)

theorem sourceGaussCompleteField_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (a b : SourceUnitFieldLeg) (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖sourceGaussCompleteFieldResponse q sL eL sR eR a b‖ ≤
      sourceGaussPolarizationPrice q (sourceUnitCompleteField a) (sourceUnitCompleteField b) :=
  sourceGaussPolarization_bound q sL eL sR eR _ _ left right

theorem sourceGaussCompleteField_equation (left right : SourceUnitFieldLeg) :
    originalJacobi (sourceUnitFieldPoint left).val*ᵥsourceUnitCompleteField left=
      sourceUnitRawForcing left+sourceUnitConstraintSupplement left ∧
    originalJacobi (sourceUnitFieldPoint right).val*ᵥsourceUnitCompleteField right=
      sourceUnitRawForcing right+sourceUnitConstraintSupplement right :=
  ⟨sourceUnitCompleteField_equation left,sourceUnitCompleteField_equation right⟩

/-- The original dressed mixed derivative consumes these very fields with independent momentum and spectral parameters. -/
theorem sourceGaussCompleteField_dressed (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (a b : SourceUnitFieldLeg) (p k : PhysicalMomentum) (z w : ℂ) (left : z.im≠0) (right : w.im≠0) :
    HasDerivAt (fun r : ℝ=>
      sourceUnitRead q sL eL sR eR (jointVertex (fun i=>(sourceUnitCompleteField b i).re) p k q.F z w
        (r • (fun i=>(sourceUnitCompleteField a i).re)))+
      Complex.I*sourceUnitRead q sL eL sR eR (jointVertex (fun i=>(sourceUnitCompleteField b i).re) p k q.F z w
        (r • (fun i=>(sourceUnitCompleteField a i).im)))+
      Complex.I*sourceUnitRead q sL eL sR eR (jointVertex (fun i=>(sourceUnitCompleteField b i).im) p k q.F z w
        (r • (fun i=>(sourceUnitCompleteField a i).re)))-
      sourceUnitRead q sL eL sR eR (jointVertex (fun i=>(sourceUnitCompleteField b i).im) p k q.F z w
        (r • (fun i=>(sourceUnitCompleteField a i).im))))
      (sourceUnitComplexMixed q sL eL sR eR (sourceUnitCompleteField a) (sourceUnitCompleteField b) p k z w) 0 :=
  sourceUnitComplexMixed_generated q sL eL sR eR _ _ p k z w left right

end LowEnergy.PreparationPhysicalActualPolarizationResponse
