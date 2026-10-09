import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteOriginVertices
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeCausalWindow

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteObservationSoftReturn
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
local instance finiteObservationEmitterIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The independent original left reader acts on the complete fixed-rest current, including all moving-state overlaps. -/
def sourceActualSoftEmitter (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : ℂ :=
  sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
    (sourceChargedSoftCurrent leg branch n unit e)

def sourceActualSoftAmplitude (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : ℂ :=
  (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))*sourceActualSoftEmitter leg branch n unit e

/-- Every actual charged soft leg factors through the same full finite-frequency polarization. -/
theorem sourceActualSoftField_factor (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀leg : SourceChargedSoftLeg,
      sourceChargedSoftField leg branch n unit e=
        sourceActualSoftAmplitude leg branch n unit e •
          sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  intro leg
  have original:=factor (sourceChargedSoftCurrent leg branch n unit e)
  rw [sourceWholePhotonResidue_apply] at original
  change nativeInsertion e.val (sourceSheet branch n unit e.val) n
    (sourceResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
      nativeModeForcing e.val (sourceSheet branch n unit e.val) n (sourceChargedSoftCurrent leg branch n unit e))=
      sourceActualSoftEmitter leg branch n unit e •
        sourceNativePolarization branch e.val (sourceSheet branch n unit e.val) n at original
  change (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) •
    ((e.val:ℂ)^2 • nativeInsertion e.val (sourceSheet branch n unit e.val) n
      (sourceResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
        nativeModeForcing e.val (sourceSheet branch n unit e.val) n (sourceChargedSoftCurrent leg branch n unit e)))=_
  rw [original]
  unfold sourceActualSoftAmplitude sourceNativeFrequencyPolarization
  funext i
  simp only [Pi.smul_apply,smul_eq_mul,Complex.real_smul,Complex.ofReal_pow]
  ring

/-- All four coordinate density/frequency rows and every ordered mixed cross retain the complete finite field. -/
theorem sourceActualSoftField_coefficients (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀left right : SourceChargedSoftLeg,
      complexCoefficients (originalComplexDirection (sourceChargedSoftField left branch n unit e))=
        sourceActualSoftAmplitude left branch n unit e • sourceFinitePoleDensity branch e.val (sourceSheet branch n unit e.val) n ∧
      complexFrequencyCoefficients (originalComplexDirection (sourceChargedSoftField left branch n unit e))=
        sourceActualSoftAmplitude left branch n unit e • sourceFinitePoleFrequency branch e.val (sourceSheet branch n unit e.val) n ∧
      complexMixedCoefficients (originalComplexDirection (sourceChargedSoftField left branch n unit e))
        (originalComplexDirection (sourceChargedSoftField right branch n unit e))=
        (sourceActualSoftAmplitude left branch n unit e*sourceActualSoftAmplitude right branch n unit e) •
          sourceFinitePoleMixed branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceActualSoftField_factor branch n unit] with e factor
  intro left right
  rw [factor left,factor right]
  exact ⟨sourceFinitePoleDensity_actual _ _ _ _ _ e.property.1.ne',
    sourceFinitePoleFrequency_actual _ _ _ _ _ e.property.1.ne',
    sourceFinitePoleMixed_actual _ _ _ _ _ _ e.property.1.ne'⟩

/-- The source lambda identification is consumed only inside the original action coefficients; full matter/dual remainder ownership is preserved. -/
theorem sourceActualSoftDensity_origin (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀leg : SourceChargedSoftLeg,∀k : Fin 4,
      complexCoefficients (originalComplexDirection (sourceChargedSoftField leg branch n unit e)) k=
        sourceActualSoftAmplitude leg branch n unit e •
          ((if k=0 then sourceFiniteOriginAmplitude branch e.val (sourceSheet branch n unit e.val) n •
              sourceNativeOriginCanonicalFiber 0 else 0)+
            (e.val:ℂ)^2 • complexCoefficients (originalComplexDirection (sourcePoleLiteralJet branch e.val
              (sourceSheet branch n unit e.val) n)) k+
            (e.val:ℂ)^2 • complexCoefficients (originalComplexDirection (sourcePoleFastJet branch e.val
              (sourceSheet branch n unit e.val) n)) k+
            complexCoefficients (originalComplexDirection (sourcePoleFrameResidual branch e.val
              (sourceSheet branch n unit e.val) n)) k) := by
  filter_upwards [sourceActualSoftField_coefficients branch n unit] with e coefficients
  intro leg k
  rw [(coefficients leg leg).1]
  change sourceActualSoftAmplitude leg branch n unit e • sourceFinitePoleDensity branch e.val (sourceSheet branch n unit e.val) n k=_
  rw [sourceFinitePoleDensity_origin]

/-- These are the same four normalized source fields and the original physical transfer, not selected component limits. -/
def sourceActualSoftParameters (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) : SourceFieldParameters :=
  (sourceChargedSoftFields legs branch n unit e,e.val^2 • n)

def sourceActualSoftParametersLimit (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) : SourceFieldParameters :=
  (sourceChargedSoftFieldsLimit legs branch,0)

theorem sourceActualSoftParameters_tendsto (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (sourceActualSoftParameters legs branch n unit) scaleApproach
      (𝓝 (sourceActualSoftParametersLimit legs branch)) := by
  have leg (i : Fin 4):=sourceChargedSoftField_tendsto (legs i) branch n unit (nonrealL i) (nonrealR i)
  have fields : Tendsto (sourceChargedSoftFields legs branch n unit) scaleApproach
      (𝓝 (sourceChargedSoftFieldsLimit legs branch)) := by
    unfold sourceChargedSoftFields sourceChargedSoftFieldsLimit
    exact (leg 0 |>.prodMk_nhds (leg 1)).prodMk_nhds (leg 2 |>.prodMk_nhds (leg 3))
  have transfer : Tendsto (fun e : scaleDomain=>e.val^2 • n) scaleApproach (𝓝 (0:PhysicalMomentum)) := by
    simpa only [zero_pow (by decide : 2≠0),zero_smul] using
      (scaleVal_tendsto.pow 2).smul (tendsto_const_nhds (x:=n))
  exact fields.prodMk_nhds transfer

end LowEnergy.PreparationPhysicalFiniteObservationSoftReturn
