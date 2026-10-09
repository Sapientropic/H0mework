import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeWindowPrice
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativeWardFiniteObservation
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
local instance causalWindowQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open MatterSpace.Response

def sourceWindowExponent (energy damping : ℝ) : ℂ := -(damping:ℂ)+Complex.I*(energy:ℂ)

/-- The original retarded source weight is evaluated on its actual lag, T-age. -/
def sourceWindowWeight (energy damping T age : ℝ) : ℂ := temporalWeight energy damping (T-age)

private theorem weight_continuous (energy damping T : ℝ) : Continuous (sourceWindowWeight energy damping T) :=
  (temporalWeight_continuous energy damping).comp (continuous_const.sub continuous_id)

private theorem weight_derivative (energy damping T age : ℝ) :
    HasDerivAt (sourceWindowWeight energy damping T)
      (-(sourceWindowWeight energy damping T age*sourceWindowExponent energy damping)) age := by
  have generated:=(Retarded.temporalWeight_derivative energy damping (T-age)).scomp age
    ((hasDerivAt_id age).const_sub T)
  convert! generated using 1
  simp only [sourceWindowWeight,sourceWindowExponent,_root_.neg_one_smul]

private theorem boundary_continuous (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (T : ℝ) :
    Continuous (sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T) :=
  continuous_iff_continuousAt.mpr fun age=>(sourceWindowKernel_derivative sideL edgeL sideR edgeR legs branch T age).continuousAt

/-- The source-generated age-zero value is paid before any initial-boundary simplification. -/
theorem sourcePhysicalSoftBoundary_initial (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (T : ℝ) :
    sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T 0=0 := by
  unfold sourcePhysicalSoftBoundary
  split_ifs
  · simp only [sourceSoftExternalBoundary,sub_self,zero_apply,map_zero,inner_zero_right,
      mul_zero,intervalIntegral.integral_same,add_zero]
  · rfl

/-- The direct contact stays outside the retarded age integration. -/
def sourceFiniteCausalPair (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (energy damping T : ℝ) : ℂ × ℂ :=
  (∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
    (sourceWindowScatteringPair sideL edgeL sideR edgeR legs branch T age).1,
    (sourceWindowScatteringPair sideL edgeL sideR edgeR legs branch T T).2)

/-- Finite causal integration returns the actual initial/final preparation boundaries and the original damping-energy term. -/
theorem sourceFiniteCausalPair_boundary (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (energy damping T : ℝ) (future : 0 ≤ T) :
    sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T=
      (sourceWindowWeight energy damping T T*sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T T-
        sourceWindowWeight energy damping T 0*sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T 0+
        sourceWindowExponent energy damping*(∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
          sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T age),0) := by
  have generated:=intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun age _=>weight_derivative energy damping T age)
    (fun age _=>sourceWindowKernel_derivative sideL edgeL sideR edgeR legs branch T age)
    (((weight_continuous energy damping T).mul_const (sourceWindowExponent energy damping)).neg.intervalIntegrable (0:ℝ) T)
    (sourceWindowKernel_integrable sideL edgeL sideR edgeR legs branch T future)
  simp only [sourceFiniteCausalPair,sourceWindowScatteringPair_read]
  apply Prod.ext
  · dsimp only [Prod.fst]
    rw [generated]
    have integrand (age : ℝ) :
        -(sourceWindowWeight energy damping T age*sourceWindowExponent energy damping)*
          sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T age=
        -sourceWindowExponent energy damping*(sourceWindowWeight energy damping T age*
          sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T age) := by ring
    simp_rw [integrand]
    rw [intervalIntegral.integral_const_mul]
    ring
  · rfl

/-- The upper endpoint is one from the original retarded mode, never a deleted final preparation. -/
theorem sourceWindowWeight_final (energy damping T : ℝ) : sourceWindowWeight energy damping T T=1 := by
  simp only [sourceWindowWeight,sub_self,temporalWeight,Fermion.retardedMode,Complex.ofReal_zero,mul_zero,Complex.exp_zero]

theorem sourceFiniteCausalPair_return (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (energy damping T : ℝ) (future : 0 ≤ T) :
    sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T=
      (sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T T+
        sourceWindowExponent energy damping*(∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
          sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T age),0) := by
  rw [sourceFiniteCausalPair_boundary sideL edgeL sideR edgeR legs branch energy damping T future,
    sourceWindowWeight_final,sourcePhysicalSoftBoundary_initial,mul_zero,one_mul,sub_zero]

private theorem weight_norm_le_one (energy damping T age : ℝ) (positive : 0 < damping) (window : age ≤ T) :
    ‖sourceWindowWeight energy damping T age‖ ≤ 1 := by
  rw [sourceWindowWeight,temporalWeight_norm]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr positive.le) (sub_nonneg.mpr window))

/-- Original normalized preparations and full source growth supply the finite causal observation bound. -/
theorem sourceFiniteCausalPair_bound (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (energy damping T : ℝ)
    (future : 0 ≤ T) (positive : 0 < damping) :
    ‖(sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T).1‖ ≤
      T*sourceWindowPrice sideL edgeL sideR edgeR legs branch T ∧
    (sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T).2=0 := by
  constructor
  · simp only [sourceFiniteCausalPair,sourceWindowScatteringPair_read]
    have estimate : ∀ᵐ age ∂volume.restrict (Ioc 0 T),
        ‖sourceWindowWeight energy damping T age*sourceWindowKernel sideL edgeL sideR edgeR legs branch T age‖ ≤
          sourceWindowPrice sideL edgeL sideR edgeR legs branch T := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with age hage
      rw [norm_mul]
      calc
        _ ≤ 1*sourceWindowPrice sideL edgeL sideR edgeR legs branch T:=
          mul_le_mul (weight_norm_le_one energy damping T age positive hage.2)
            (sourceWindowKernel_bound sideL edgeL sideR edgeR legs branch T age future ⟨hage.1.le,hage.2⟩)
            (norm_nonneg _) (by norm_num)
        _=_:=one_mul _
    have generated:=intervalIntegral.norm_integral_le_of_norm_le future ((ae_restrict_iff' measurableSet_Ioc).mp estimate)
      (intervalIntegrable_const (c:=sourceWindowPrice sideL edgeL sideR edgeR legs branch T))
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using generated
  · simp only [sourceFiniteCausalPair,sourceWindowScatteringPair_read]

/-- The same original soft pair supplies both its actual boundary response and its source-priced finite measurement. -/
theorem sourceFiniteCausalPair_actual (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (energy damping T : ℝ)
    (future : 0 ≤ T) (positive : 0 < damping) :
    sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T=
      (sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T T+
        sourceWindowExponent energy damping*(∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
          sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T age),0) ∧
    ‖(sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T).1‖ ≤
      T*sourceWindowPrice sideL edgeL sideR edgeR legs branch T :=
  ⟨sourceFiniteCausalPair_return sideL edgeL sideR edgeR legs branch energy damping T future,
    (sourceFiniteCausalPair_bound sideL edgeL sideR edgeR legs branch energy damping T future positive).1⟩

end LowEnergy.PreparationPhysicalNativeWardFiniteObservation
