import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedScatteringWordsPrice

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
local instance chargedPairPriceQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

def sourceOrderedSumPrice (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) : ℝ :=
  ∑i : Fin 4,∑j : Fin 4,sourceOrderedCARPrice sideL edgeL sideR edgeR A B shift time age i j

theorem sourcePreparedOrderedSum_domain_bound (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) :
    ‖∑i : Fin 4,∑j : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR A B shift time age i j‖ ≤
      sourceOrderedSumPrice sideL edgeL sideR edgeR A B shift time age := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun j _=>sourcePreparedOrderedCAR_domain_bound sideL edgeL sideR edgeR A B shift time age i j)

theorem sourcePreparedOrderedWord_domain_bound (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) :
    ‖sourceActualScatteringRead sideL edgeL sideR edgeR (orderedWord A B shift time age)‖ ≤
      sourceOrderedSumPrice sideL edgeL sideR edgeR A B shift time age := by
  simp only [sourceActualScatteringRead_source,orderedWord,sum_apply,inner_sum,mul_apply_eq_comp,
    ←sourcePreparedOrderedCAR_source]
  exact sourcePreparedOrderedSum_domain_bound sideL edgeL sideR edgeR A B shift time age

/-- Positive and negative vertices keep their original adjoint, momentum and time ordering. -/
def sourceScatteringPairDomainPrice (sideL edgeL sideR edgeR : Fin 2)
    (A B : TransferPair) (shift : Fin 3→ℝ) (time age : ℝ) : ℝ × ℝ :=
  (sourceOrderedSumPrice sideL edgeL sideR edgeR
      (shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients B.negative)) shift)
      (realReaderCoefficients A shift) (-shift) age time+
    sourceOrderedSumPrice sideL edgeL sideR edgeR
      (realReaderCoefficients A shift) (complexFrequencyCoefficients B.positive) shift time age,
    sourceContactDomainPrice sideR edgeR (realMixedCoefficients A B) time)

/-- The complete original two-time scattering pair is bounded componentwise; direct contact is never absorbed into the age kernel. -/
theorem sourcePreparedScatteringPair_domain_bound (sideL edgeL sideR edgeR : Fin 2)
    (A B : TransferPair) (shift : Fin 3→ℝ) (time age : ℝ) :
    ‖(sourcePreparedScatteringPair sideL edgeL sideR edgeR A B shift time age).1‖ ≤
      (sourceScatteringPairDomainPrice sideL edgeL sideR edgeR A B shift time age).1 ∧
    ‖(sourcePreparedScatteringPair sideL edgeL sideR edgeR A B shift time age).2‖ ≤
      (sourceScatteringPairDomainPrice sideL edgeL sideR edgeR A B shift time age).2 := by
  constructor
  · rw [sourcePreparedScatteringPair_fullCAR]
    simp only [sourceScatteringPairDomainPrice,norm_mul,Complex.norm_I,one_mul]
    exact (norm_sub_le _ _).trans (add_le_add
      (sourcePreparedOrderedSum_domain_bound sideL edgeL sideR edgeR _ _ _ _ _)
      (sourcePreparedOrderedSum_domain_bound sideL edgeL sideR edgeR _ _ _ _ _))
  · change ‖sourceActualScatteringRead sideL edgeL sideR edgeR (contactWord (realMixedCoefficients A B) time)‖ ≤ _
    exact sourcePreparedContact_domain_bound sideL edgeL sideR edgeR _ time

end LowEnergy.PreparationPhysicalChargedScatteringDomainPrice
