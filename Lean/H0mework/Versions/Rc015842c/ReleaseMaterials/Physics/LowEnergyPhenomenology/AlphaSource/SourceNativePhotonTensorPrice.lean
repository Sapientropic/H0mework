import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedScatteringPairPrice
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePolarizationScatteringTensor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedScatteringDomainPrice
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
local instance chargedPhotonPriceQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalNativePhotonScatteringSheetReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic

/-- The native source field, both independent frequency branches and the actual charged packets determine this price. -/
theorem sourcePhotonScatteringPair_domain_bound (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) :
    ‖(sourcePhotonScatteringPair sideL edgeL sideR edgeR Ap An Bp Bn epsilon s n time age).1‖ ≤
      (sourceScatteringPairDomainPrice sideL edgeL sideR edgeR
        (sourcePhotonTransfer Ap An epsilon s n) (sourcePhotonTransfer Bp Bn epsilon s n)
        (epsilon^2 • n) time age).1 ∧
    ‖(sourcePhotonScatteringPair sideL edgeL sideR edgeR Ap An Bp Bn epsilon s n time age).2‖ ≤
      (sourceScatteringPairDomainPrice sideL edgeL sideR edgeR
        (sourcePhotonTransfer Ap An epsilon s n) (sourcePhotonTransfer Bp Bn epsilon s n)
        (epsilon^2 • n) time age).2 :=
  sourcePreparedScatteringPair_domain_bound sideL edgeL sideR edgeR _ _ _ time age

/-- The four tensor prices retain all ordered terms and both original contact coefficients. -/
def sourceNativeTensorDomainPrice (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) (time age : ℝ) : Fin 4→ℝ × ℝ :=
  let mode:=sourceNativePolarization branch epsilon s n
  let shift:=epsilon^2 • n
  let D:=complexCoefficients (originalComplexDirection mode)
  let F:=complexFrequencyCoefficients (originalComplexDirection mode)
  let J:=adjointCoefficients (shiftCoefficients D (-shift))
  let W:=shiftCoefficients (adjointCoefficients F) shift
  let C:=complexMixedCoefficients (originalComplexDirection mode) (originalComplexDirection mode)
  ![((1/2)*sourceOrderedSumPrice sideL edgeL sideR edgeR W D (-shift) age time,0),
    ((1/2)*sourceOrderedSumPrice sideL edgeL sideR edgeR W J (-shift) age time,
      (1/2)*sourceContactDomainPrice sideR edgeR (adjointCoefficients C) time),
    ((1/2)*sourceOrderedSumPrice sideL edgeL sideR edgeR D F shift time age,
      (1/2)*sourceContactDomainPrice sideR edgeR C time),
    ((1/2)*sourceOrderedSumPrice sideL edgeL sideR edgeR J F shift time age,0)]

private theorem half_phase_bound (z : ℂ) (bound : ℝ) (price : ‖z‖ ≤ bound) :
    ‖Complex.I*(2:ℂ)⁻¹*z‖ ≤ (1/2)*bound ∧ ‖-Complex.I*(2:ℂ)⁻¹*z‖ ≤ (1/2)*bound := by
  have positive : ‖Complex.I*(2:ℂ)⁻¹‖=(1/2:ℝ) := by norm_num
  have negative : ‖-Complex.I*(2:ℂ)⁻¹‖=(1/2:ℝ) := by norm_num
  constructor
  · rw [norm_mul,positive]
    exact mul_le_mul_of_nonneg_left price (by norm_num)
  · rw [norm_mul,negative]
    exact mul_le_mul_of_nonneg_left price (by norm_num)

private theorem half_bound (z : ℂ) (bound : ℝ) (price : ‖z‖ ≤ bound) :
    ‖(2:ℂ)⁻¹*z‖ ≤ (1/2)*bound := by
  have scalar : ‖(2:ℂ)⁻¹‖=(1/2:ℝ) := by norm_num
  rw [norm_mul,scalar]
  exact mul_le_mul_of_nonneg_left price (by norm_num)

/-- Every polarization entry is controlled on the two actual source preparations, without discarding its contact component. -/
theorem sourceNativeScatteringTensor_domain_bound (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) (time age : ℝ) (i : Fin 4) :
    ‖(sourceNativeScatteringTensor branch epsilon s n sideL edgeL sideR edgeR time age i).1‖ ≤
      (sourceNativeTensorDomainPrice branch epsilon s n sideL edgeL sideR edgeR time age i).1 ∧
    ‖(sourceNativeScatteringTensor branch epsilon s n sideL edgeL sideR edgeR time age i).2‖ ≤
      (sourceNativeTensorDomainPrice branch epsilon s n sideL edgeL sideR edgeR time age i).2 := by
  fin_cases i
  · exact ⟨(half_phase_bound _ _ (sourcePreparedOrderedWord_domain_bound sideL edgeL sideR edgeR _ _ _ _ _)).1,
      by change ‖(0:ℂ)‖ ≤ (0:ℝ); simp only [norm_zero,le_refl]⟩
  · exact ⟨(half_phase_bound _ _ (sourcePreparedOrderedWord_domain_bound sideL edgeL sideR edgeR _ _ _ _ _)).1,
      half_bound _ _ (sourcePreparedContact_domain_bound sideL edgeL sideR edgeR _ _)⟩
  · exact ⟨(half_phase_bound _ _ (sourcePreparedOrderedWord_domain_bound sideL edgeL sideR edgeR _ _ _ _ _)).2,
      half_bound _ _ (sourcePreparedContact_domain_bound sideL edgeL sideR edgeR _ _)⟩
  · exact ⟨(half_phase_bound _ _ (sourcePreparedOrderedWord_domain_bound sideL edgeL sideR edgeR _ _ _ _ _)).2,
      by change ‖(0:ℂ)‖ ≤ (0:ℝ); simp only [norm_zero,le_refl]⟩


def sourcePhotonEmitterDomainPrice (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (time age : ℝ) : ℝ × ℝ :=
  let weights:=sourceEmitterMonomials (sourcePhotonEmitter Ap branch epsilon s n)
    (sourcePhotonEmitter An branch epsilon s n) (sourcePhotonEmitter Bp branch epsilon s n)
    (sourcePhotonEmitter Bn branch epsilon s n)
  let price:=sourceNativeTensorDomainPrice branch epsilon s n sideL edgeL sideR edgeR time age
  (∑i : Fin 4,‖weights i‖*(price i).1,∑i : Fin 4,‖weights i‖*(price i).2)

/-- Actual source emitters, rather than freely chosen polarization amplitudes, pay both residue components. -/
theorem sourcePhotonScatteringResidue_domain_bound (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (time age : ℝ) :
    ∀ᶠ e in scaleApproach,
      ‖(sourcePhotonScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn
        e.val (sourceSheet branch n unit e.val) n time age).1‖ ≤
        (sourcePhotonEmitterDomainPrice sideL edgeL sideR edgeR Ap An Bp Bn branch
          e.val (sourceSheet branch n unit e.val) n time age).1 ∧
      ‖(sourcePhotonScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn
        e.val (sourceSheet branch n unit e.val) n time age).2‖ ≤
        (sourcePhotonEmitterDomainPrice sideL edgeL sideR edgeR Ap An Bp Bn branch
          e.val (sourceSheet branch n unit e.val) n time age).2 := by
  filter_upwards [sourcePhotonScatteringResidue_emitterTensor sideL edgeL sideR edgeR
    Ap An Bp Bn branch n unit time age] with e tensor
  rw [tensor]
  simp only [Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  dsimp only [sourcePhotonEmitterDomainPrice]
  constructor
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (sourceNativeScatteringTensor_domain_bound branch e.val (sourceSheet branch n unit e.val)
        n sideL edgeL sideR edgeR time age i).1 (norm_nonneg _)
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (sourceNativeScatteringTensor_domain_bound branch e.val (sourceSheet branch n unit e.val)
        n sideL edgeL sideR edgeR time age i).2 (norm_nonneg _)

/-- The physical-frequency residue keeps its original epsilon-fourth scaling exactly once in both components. -/
theorem sourcePhotonScatteringFrequencyResidue_domain_bound (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (time age : ℝ) :
    ∀ᶠ e in scaleApproach,
      ‖(sourcePhotonScatteringFrequencyResidue sideL edgeL sideR edgeR Ap An Bp Bn
        e.val (sourceSheet branch n unit e.val) n time age).1‖ ≤
        ‖(e.val:ℂ)^4‖*(sourcePhotonEmitterDomainPrice sideL edgeL sideR edgeR Ap An Bp Bn branch
          e.val (sourceSheet branch n unit e.val) n time age).1 ∧
      ‖(sourcePhotonScatteringFrequencyResidue sideL edgeL sideR edgeR Ap An Bp Bn
        e.val (sourceSheet branch n unit e.val) n time age).2‖ ≤
        ‖(e.val:ℂ)^4‖*(sourcePhotonEmitterDomainPrice sideL edgeL sideR edgeR Ap An Bp Bn branch
          e.val (sourceSheet branch n unit e.val) n time age).2 := by
  filter_upwards [sourcePhotonScatteringResidue_domain_bound sideL edgeL sideR edgeR
    Ap An Bp Bn branch n unit time age] with e bounds
  rw [sourcePhotonScattering_frequencyScale]
  simp only [Prod.smul_fst,Prod.smul_snd,norm_smul]
  exact ⟨mul_le_mul_of_nonneg_left bounds.1 (norm_nonneg _),
    mul_le_mul_of_nonneg_left bounds.2 (norm_nonneg _)⟩

end LowEnergy.PreparationPhysicalChargedScatteringDomainPrice
