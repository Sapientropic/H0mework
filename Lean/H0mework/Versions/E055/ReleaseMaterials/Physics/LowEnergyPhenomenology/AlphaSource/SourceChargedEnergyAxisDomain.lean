import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedMomentumDomain

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
local instance chargedAxisDomainQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

private theorem coefficient_leg_fourier (A : FiberOperators) (side edge : Fin 2) (i : Fin 4) :
    fourier (A.compLpL 2 volume (coordinateLeg i (sourceActualScatteringInput side edge)))=ᵐ[volume]
      fun k=>A (sourceActualCoordinateMomentum i (physicalMomentum k) •
        fourier (sourceChargedFilteredPacket side edge) k) := by
  rw [GaugeGreen.constant_fourier]
  filter_upwards [A.coeFn_compLpL (fourier (coordinateLeg i (sourceActualScatteringInput side edge))),
    sourceActualScatteringCoordinateLeg_fourier side edge i] with k read leg
  rw [read,leg]

/-- Each original energy vector is generated from the same four actual scattering legs. -/
theorem sourceChargedEnergyVector_coordinates (v : ActionState) (side edge : Fin 2) :
    sourceChargedEnergyVector v side edge=
      ∑i : Fin 4,(sourceEnergyCoefficients v i).compLpL 2 volume
        (coordinateLeg i (sourceActualScatteringInput side edge)) := by
  apply fourier.injective
  rw [map_sum]
  apply Lp.ext
  filter_upwards [sourceChargedEnergyVector_fourier v side edge,
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4=>fourier
      ((sourceEnergyCoefficients v i).compLpL 2 volume (coordinateLeg i (sourceActualScatteringInput side edge)))),
    Filter.eventually_all.mpr (fun i : Fin 4=>coefficient_leg_fourier (sourceEnergyCoefficients v i) side edge i)]
    with k energy total coefficients
  rw [energy,total,←sourceEnergyCoefficients_affine]
  simp only [Finset.sum_apply,coefficients,Fin.sum_univ_succ,sourceActualCoordinateMomentum,
    Fin.cases_zero,Fin.cases_succ,map_smul,one_smul,affine,add_apply,sum_apply,smul_apply]

/-- All prices read the actual coframe, connection and scalar coefficients, with the paid packet graph norm. -/
def sourceChargedEnergyAxisPrice (v : ActionState) (side edge : Fin 2) : ℝ :=
  ‖sourceEnergyCoefficients v 0‖+
    ∑j : Fin 3,‖sourceEnergyCoefficients v j.succ‖*sourceChargedMomentumPrice side edge

theorem sourceChargedEnergyVector_domain_bound (v : ActionState) (side edge : Fin 2) :
    ‖sourceChargedEnergyVector v side edge‖ ≤ sourceChargedEnergyAxisPrice v side edge := by
  rw [sourceChargedEnergyVector_coordinates]
  apply (norm_sum_le _ _).trans
  have bound : ∀i : Fin 4,
      ‖(sourceEnergyCoefficients v i).compLpL 2 volume
        (coordinateLeg i (sourceActualScatteringInput side edge))‖ ≤ 
      ‖sourceEnergyCoefficients v i‖*Fin.cases 1 (fun _=>sourceChargedMomentumPrice side edge) i := by
    intro i
    exact ((sourceEnergyCoefficients v i).compLpL 2 volume |>.le_opNorm _).trans
      (mul_le_mul ((sourceEnergyCoefficients v i).norm_compLpL_le)
        (sourceChargedCoordinateLeg_bound side edge i) (norm_nonneg _) (norm_nonneg _))
  exact (Finset.sum_le_sum (fun i _=>bound i)).trans_eq (by
    simp only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,mul_one,sourceChargedEnergyAxisPrice])

theorem sourceChargedEnergyRead_domain_bound (v : ActionState) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourceChargedEnergyRead v shift sideL edgeL sideR edgeR‖ ≤ sourceChargedEnergyAxisPrice v sideR edgeR := by
  rw [sourceChargedEnergyRead_generated]
  apply (norm_inner_le_norm _ _).trans
  rw [sourceChargedFilteredPacket_unit,one_mul,PacketNoise.phaseShift_norm]
  exact sourceChargedEnergyVector_domain_bound v sideR edgeR

end LowEnergy.PreparationPhysicalChargedVertexDomainReturn
