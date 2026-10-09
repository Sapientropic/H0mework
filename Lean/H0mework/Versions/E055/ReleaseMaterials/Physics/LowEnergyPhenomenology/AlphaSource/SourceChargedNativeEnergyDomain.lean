import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedEnergyAxisDomain
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePhotonScatteringPreparation

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedVertexDomainReturn
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
local instance chargedNativeDomainQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- Each of the three original channels keeps all four actual energy-axis prices. -/
def sourceChargedChannelDomainPrice (shift : Position) (zeta : ℂ) (i : Fin 3) (side edge : Fin 2) : ℝ :=
  ∑k : Fin 4,‖fixedMomentum (physicalMomentum shift) zeta k‖*
    sourceChargedEnergyAxisPrice (fieldDirection (sourceEnergyAxisField i k)) side edge

theorem sourcePhysicalEnergyChannel_domain_bound (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourcePhysicalEnergyChannel shift zeta i sideL edgeL sideR edgeR‖ ≤
      sourceChargedChannelDomainPrice shift zeta i sideR edgeR := by
  rw [sourcePhysicalEnergyChannel_axes]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sourceChargedEnergyRead_domain_bound _ shift sideL edgeL sideR edgeR) (norm_nonneg _)

def sourceChargedFullDomainPrice (V : Fin 289→ℂ) (side edge : Fin 2) : ℝ :=
  ∑j : Fin 289,‖V j‖*sourceChargedEnergyAxisPrice (fieldDirection (fieldUnit j)) side edge

theorem sourcePhysicalEnergyReader_domain_bound (shift : Position) (V : Fin 289→ℂ)
    (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR V‖ ≤ sourceChargedFullDomainPrice V sideR edgeR := by
  rw [sourcePhysicalEnergyReader_original,sourceFullEnergyRead_generated]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sourceChargedEnergyRead_domain_bound _ shift sideL edgeL sideR edgeR) (norm_nonneg _)

/-- The actual source current and all three denominators determine the complete price, including the regular field. -/
theorem sourcePhysicalEnergy_three_domain_bound (q : PhysicalResponsePoint) (shift : Position)
    (zeta : sourceCausalDomain (physicalMomentum shift))
    (sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR : Fin 2) :
    let residue:=sourceActualNativeResidue q (physicalMomentum shift) zeta.val
      (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)
    let coefficient:=fun i : Fin 3=>(sourceChargedDenominator (physicalMomentum shift) zeta.val i)⁻¹*
      sourceSlowRead residue ⟨i.val,by omega⟩
    let regular:=sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q (physicalMomentum shift) zeta.val
      (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)
    ‖sourceChargedModeEnergyRead q shift zeta.val sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR‖ ≤
      (∑i : Fin 3,‖coefficient i‖*sourceChargedChannelDomainPrice shift zeta.val i sideR edgeR)+
        sourceChargedFullDomainPrice regular sideR edgeR := by
  dsimp only
  rw [sourcePhysicalEnergy_three_channels]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (sourcePhysicalEnergyChannel_domain_bound shift zeta.val i sideL edgeL sideR edgeR) (norm_nonneg _)
  · exact sourcePhysicalEnergyReader_domain_bound shift _ sideL edgeL sideR edgeR

open PreparationPhysicalNativePhotonScatteringSheetReturn PreparationPhysicalScatteringFrequencyWard

/-- Physical sheet momentum and the Fourier translation coordinate differ by the original 2π. -/
def sourcePhotonEnergyShift (epsilon : ℝ) (n : PhysicalMomentum) : Position :=
  WithLp.toLp 2 (fun j=>epsilon^2*n j/(2*Real.pi))

theorem sourcePhotonEnergyShift_momentum (epsilon : ℝ) (n : PhysicalMomentum) :
    physicalMomentum (sourcePhotonEnergyShift epsilon n)=epsilon^2 • n := by
  funext j
  change 2*Real.pi*(epsilon^2*n j/(2*Real.pi))=epsilon^2*n j
  field_simp [Real.pi_ne_zero]

/-- The original quantum observable reads the actual sheet field emitted by its charged maker pair. -/
def sourcePhotonEnergyRead (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  sourceFullEnergyRead (sourcePhotonField leg epsilon s n) (sourcePhotonEnergyShift epsilon n)
    sideL edgeL sideR edgeR

/-- The sheet field enters the exact frequency vertex already used in the two-time scattering kernel. -/
theorem sourcePhotonEnergyRead_frequency (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhotonEnergyRead leg epsilon s n sideL edgeL sideR edgeR=
      ∫k : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
        (affine (complexFrequencyCoefficients (originalComplexDirection (sourcePhotonField leg epsilon s n)))
          (physicalMomentum (k-sourcePhotonEnergyShift epsilon n))
          (fourier (sourceChargedFilteredPacket sideR edgeR) (k-sourcePhotonEnergyShift epsilon n))) := by
  simp only [sourceScatteringFrequency_affine,map_sum,map_smul,sum_apply,smul_apply,inner_sum,inner_smul_right]
  rw [integral_finsetSum]
  · simp only [sourcePhotonEnergyRead,sourceFullEnergyRead_generated,integral_const_mul,sourceChargedEnergyRead_fourier]
  · intro j _
    exact (sourceChargedEnergyRead_integrable (fieldDirection (fieldUnit j))
      (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR).const_mul _

theorem sourcePhotonEnergyRead_domain_bound (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourcePhotonEnergyRead leg epsilon s n sideL edgeL sideR edgeR‖ ≤
      sourceChargedFullDomainPrice (sourcePhotonField leg epsilon s n) sideR edgeR := by
  rw [sourcePhotonEnergyRead,←sourcePhysicalEnergyReader_original]
  exact sourcePhysicalEnergyReader_domain_bound _ _ sideL edgeL sideR edgeR

end LowEnergy.PreparationPhysicalChargedVertexDomainReturn
