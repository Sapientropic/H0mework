import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFieldMixedChargeWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualFieldNoetherResponse
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
local instance actualHarmonicChargeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
local instance : NormedAlgebra ℝ (Operator) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian

open PreparationPhysicalActualUnitFourPointReturn PreparationPhysicalSourceHarmonicReturn

open PreparationPhysicalUnitCurrentFieldReturn
attribute [local irreducible] sourceUnitRead sourceActualUnitLegRead sourceActualLegCorrection

def sourceHarmonicMixedOperator (s : SourceHarmonicOccurrence) (i j : Fin 4) (x : Position)
    (q : PhysicalResponsePoint) (p k : PhysicalMomentum) : Operator :=
  let f:=sourceHarmonicProfile s i x
  let g:=sourceHarmonicProfile s j x
  mixedVertex (fun a=>(f a).re) (fun a=>(g a).re) p k q.F q.z q.w+
  Complex.I • mixedVertex (fun a=>(f a).im) (fun a=>(g a).re) p k q.F q.z q.w+
  Complex.I • mixedVertex (fun a=>(f a).re) (fun a=>(g a).im) p k q.F q.z q.w-
  mixedVertex (fun a=>(f a).im) (fun a=>(g a).im) p k q.F q.z q.w

def sourceHarmonicMixedChargeResponse (s : SourceHarmonicOccurrence) (i j : Fin 4) (x : Position)
    (q : PhysicalResponsePoint) (p k : PhysicalMomentum) : Operator :=
  let f:=sourceHarmonicProfile s i x
  let g:=sourceHarmonicProfile s j x
  sourceFieldMixedChargeResponse q p k (fun a=>(f a).re) (fun a=>(g a).re)+
  Complex.I • sourceFieldMixedChargeResponse q p k (fun a=>(f a).im) (fun a=>(g a).re)+
  Complex.I • sourceFieldMixedChargeResponse q p k (fun a=>(f a).re) (fun a=>(g a).im)-
  sourceFieldMixedChargeResponse q p k (fun a=>(f a).im) (fun a=>(g a).im)

def sourceHarmonicChargeCurve (s : SourceHarmonicOccurrence) (i j : Fin 4) (x : Position)
    (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (r : ℝ) : Operator :=
  let f:=sourceHarmonicProfile s i x
  let g:=sourceHarmonicProfile s j x
  sourceFieldChargeBracket (jointVertex (fun a=>(g a).re) p k q.F q.z q.w (r • (fun a=>(f a).re)))+
  Complex.I • sourceFieldChargeBracket (jointVertex (fun a=>(g a).re) p k q.F q.z q.w (r • (fun a=>(f a).im)))+
  Complex.I • sourceFieldChargeBracket (jointVertex (fun a=>(g a).im) p k q.F q.z q.w (r • (fun a=>(f a).re)))-
  sourceFieldChargeBracket (jointVertex (fun a=>(g a).im) p k q.F q.z q.w (r • (fun a=>(f a).im)))

/-- The actual four signed full289 modes, rather than supplied response directions, drive this charge derivative. -/
theorem sourceHarmonicCharge_generated (s : SourceHarmonicOccurrence) (i j : Fin 4) (x : Position)
    (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceUnitRead q sL eL sR eR (sourceHarmonicChargeCurve s i j x q p k r))
      (sourceUnitRead q sL eL sR eR (sourceHarmonicMixedChargeResponse s i j x q p k)) 0 := by
  have derivative (f g : Field289) := (sourceUnitRead q sL eL sR eR).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0
    (sourceFieldMixedCharge_generated q p k f g left right)
  have rr:=derivative (fun a=>(sourceHarmonicProfile s i x a).re) (fun a=>(sourceHarmonicProfile s j x a).re)
  have ir:=derivative (fun a=>(sourceHarmonicProfile s i x a).im) (fun a=>(sourceHarmonicProfile s j x a).re)
  have ri:=derivative (fun a=>(sourceHarmonicProfile s i x a).re) (fun a=>(sourceHarmonicProfile s j x a).im)
  have ii:=derivative (fun a=>(sourceHarmonicProfile s i x a).im) (fun a=>(sourceHarmonicProfile s j x a).im)
  convert ((rr.add (ir.const_mul Complex.I)).add (ri.const_mul Complex.I)).sub ii using 1
  all_goals first | rfl | (simp only [sourceHarmonicChargeCurve,sourceHarmonicMixedChargeResponse,map_add,map_sub,map_smul,smul_eq_mul]; rfl)

theorem sourceHarmonicMixedCharge_return (s : SourceHarmonicOccurrence) (i j : Fin 4) (x : Position)
    (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceHarmonicMixedChargeResponse s i j x q p k=
      sourceFieldChargeBracket (sourceHarmonicMixedOperator s i j x q p k) := by
  simp only [sourceHarmonicMixedChargeResponse,sourceFieldMixedCharge_return q p k _ _ left right,
    sourceHarmonicMixedOperator,sourceFieldChargeBracket,add_mul,mul_add,sub_mul,mul_sub,
    smul_mul_assoc,mul_smul_comm,smul_sub]
  abel

theorem sourceHarmonicMixedOperator_read (s : SourceHarmonicOccurrence) (i j : Fin 4) (x : Position)
    (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (sL eL sR eR : Fin 2) :
    sourceUnitRead q sL eL sR eR (sourceHarmonicMixedOperator s i j x q p k)=
      sourceUnitComplexMixed q sL eL sR eR (sourceHarmonicProfile s i x) (sourceHarmonicProfile s j x)
        p k q.z q.w := by
  simp only [sourceHarmonicMixedOperator,map_add,map_sub,map_smul,smul_eq_mul,
    sourceUnitComplexMixed,sourceUnitMixedVertex]

/-- The actual normalized legs keep the induced exterior charge correction; their unit norms do not discard it. -/
theorem sourceHarmonicCharge_normalized (s : SourceHarmonicOccurrence) (i j : Fin 4) (x : Position)
    (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceUnitRead q sL eL sR eR (sourceHarmonicMixedChargeResponse s i j x q p k)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*
        ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
        sourceUnitComplexMixed q sL eL sR eR (sourceHarmonicProfile s i x) (sourceHarmonicProfile s j x) p k q.z q.w+
      sourceActualLegNormalization q sL eL sR eR*
        (sourceActualLegCorrection q sL eL sR eR (sourceHarmonicMixedChargeResponse s i j x q p k)-
          (Stage10.ActionNormalization.phaseMomentum:ℂ)*
            ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
            sourceActualLegCorrection q sL eL sR eR (sourceHarmonicMixedOperator s i j x q p k)) := by
  rw [←sourceHarmonicMixedOperator_read s i j x q p k sL eL sR eR]
  simp only [sourceUnitRead_original,sourceActualUnitLegRead_return]
  rw [sourceHarmonicMixedCharge_return s i j x q p k left right,sourceFieldAbsoluteCharge_read]
  ring

/-- The same actual profile read keeps every density/frequency row and the independent mixed contact character. -/
theorem sourceHarmonicCharge_profile (s : SourceHarmonicOccurrence) (i j row : Fin 4) (x : Position) :
    complexCoefficients (originalComplexDirection (sourceHarmonicProfile s i x)) row=
      phase (sourceModeWave s.wave i) x • complexCoefficients (originalComplexDirection (sourceHarmonicField s i)) row ∧
    complexFrequencyCoefficients (originalComplexDirection (sourceHarmonicProfile s j x)) row=
      phase (sourceModeWave s.wave j) x • complexFrequencyCoefficients (originalComplexDirection (sourceHarmonicField s j)) row ∧
    complexMixedCoefficients (originalComplexDirection (sourceHarmonicProfile s i x))
      (originalComplexDirection (sourceHarmonicProfile s j x)) row=
      phase (sourceModeWave s.wave i+sourceModeWave s.wave j) x •
        complexMixedCoefficients (originalComplexDirection (sourceHarmonicField s i))
          (originalComplexDirection (sourceHarmonicField s j)) row :=
  ⟨(sourceHarmonicProfile_coefficients s i row x).1,(sourceHarmonicProfile_coefficients s j row x).2,
    sourceHarmonicProfile_mixed s i j row x⟩

/-- Actual profile quadratures retain the original independently amputated two-order/contact return. -/
theorem sourceHarmonicCharge_fourPoint (s : SourceHarmonicOccurrence) (i j : Fin 4) (x : Position)
    (imaginaryLeft imaginaryRight : Bool) (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    let f : Field289:=fun a=>if imaginaryLeft then (sourceHarmonicProfile s i x a).im else (sourceHarmonicProfile s i x a).re
    let g : Field289:=fun a=>if imaginaryRight then (sourceHarmonicProfile s j x a).im else (sourceHarmonicProfile s j x a).re
    sourceActualLegNormalization q sL eL sR eR*
      ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w)*
        sourceQuantumChargedRead q sL eL sR eR (sourceFieldMixedChargeResponse q 0 0 f g)=
    (Stage10.ActionNormalization.phaseMomentum:ℂ)*
      ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
        ((sourceUnitFourPointPair q sL eL sR eR f g).1+(sourceUnitFourPointPair q sL eL sR eR f g).2) := by
  dsimp only
  rw [sourceFieldMixedCharge_prepared q 0 0 sL eL sR eR _ _ left right,
    ←sourceUnitFourPoint_amputated q sL eL sR eR _ _ left right]
  ring

end LowEnergy.PreparationPhysicalActualFieldNoetherResponse
