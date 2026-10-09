import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedNativeEnergyDomain

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
local instance chargedScatteringPriceQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

def sourceScatteringGrowth (time : ℝ) : ℝ := 1+|time| * sourceRate 0

private theorem sourceShiftFlow_domain_bound (shift : Fin 3→ℝ) (time : ℝ) :
    ‖shiftFlow shift time‖ ≤ sourceScatteringGrowth time := by
  have bound : ‖momentumShiftFlow shift time‖ ≤ sourceScatteringGrowth time :=
    multiplier_norm _ _ _ _ (by unfold sourceRate; positivity)
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold sourceScatteringGrowth sourceRate; positivity)
  intro v
  change ‖fourier.symm (momentumShiftFlow shift time (fourier v))‖ ≤ _
  rw [fourier.symm.norm_map]
  exact ((momentumShiftFlow shift time).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right bound (norm_nonneg _)).trans_eq (by rw [fourier.norm_map]))

/-- The four prices belong to the actual charged preparations already used by the scattering legs. -/
def sourceScatteringLegPrice (side edge : Fin 2) (i : Fin 4) : ℝ :=
  Fin.cases 1 (fun _=>sourceChargedMomentumPrice side edge) i

theorem sourceScatteringLegPrice_nonnegative (side edge : Fin 2) (i : Fin 4) :
    0 ≤ sourceScatteringLegPrice side edge i :=
  (norm_nonneg _).trans (sourceChargedCoordinateLeg_bound side edge i)

/-- The full source evolution keeps its one-way Yukawa sourceScatteringGrowth on each of the three time intervals. -/
def sourceOrderedInteriorPrice (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ)
    (time age : ℝ) (i j : Fin 4) : ℝ :=
  sourceScatteringGrowth time*‖shiftCoefficients A shift i‖*sourceScatteringGrowth (time-age)*‖B j‖*sourceScatteringGrowth age

theorem sourceOrderedInterior_domain_bound (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ)
    (time age : ℝ) (i j : Fin 4) :
    ‖sourceOrderedInterior A B shift time age i j‖ ≤ sourceOrderedInteriorPrice A B shift time age i j := by
  have first : ‖spatialFlow 0 (-time)‖ ≤ sourceScatteringGrowth time := by
    simpa only [sourceScatteringGrowth,abs_neg] using spatialFlow_norm 0 (-time)
  have step1:=norm_mul_le_of_le first ((shiftCoefficients A shift i).norm_compLpL_le (p:=2) (μ:=volume))
  have step2:=norm_mul_le_of_le step1 (sourceShiftFlow_domain_bound shift (time-age))
  have step3:=norm_mul_le_of_le step2 ((B j).norm_compLpL_le (p:=2) (μ:=volume))
  exact norm_mul_le_of_le step3 (spatialFlow_norm 0 age)

def sourceOrderedCARPrice (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) : ℝ :=
  sourceScatteringLegPrice sideL edgeL i*
    (sourceOrderedInteriorPrice A B shift time age i j*sourceScatteringLegPrice sideR edgeR j)

/-- Every complete four-CAR word is bounded on its two independent source-generated coordinate legs. -/
theorem sourcePreparedOrderedCAR_domain_bound (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    ‖sourcePreparedOrderedCAR sideL edgeL sideR edgeR A B shift time age i j‖ ≤
      sourceOrderedCARPrice sideL edgeL sideR edgeR A B shift time age i j := by
  rw [sourcePreparedOrderedCAR_source]
  change ‖inner ℂ (sourceActualScatteringInput sideL edgeL)
    ((coordinateLeg i).adjoint (sourceOrderedInterior A B shift time age i j
      (coordinateLeg j (sourceActualScatteringInput sideR edgeR))))‖ ≤ _
  rw [ContinuousLinearMap.adjoint_inner_right]
  apply (norm_inner_le_norm _ _).trans
  have right := ((sourceOrderedInterior A B shift time age i j).le_opNorm _).trans
    (mul_le_mul (sourceOrderedInterior_domain_bound A B shift time age i j)
      (sourceChargedCoordinateLeg_bound sideR edgeR j) (norm_nonneg _)
      ((norm_nonneg _).trans (sourceOrderedInterior_domain_bound A B shift time age i j)))
  exact mul_le_mul (sourceChargedCoordinateLeg_bound sideL edgeL i) right
    (norm_nonneg _) (sourceScatteringLegPrice_nonnegative sideL edgeL i)

def sourceContactInteriorPrice (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) : ℝ :=
  sourceScatteringGrowth time*‖C j‖*sourceScatteringGrowth time

theorem sourceContactInterior_domain_bound (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) :
    ‖sourceContactInterior C time j‖ ≤ sourceContactInteriorPrice C time j := by
  have first : ‖spatialFlow 0 (-time)‖ ≤ sourceScatteringGrowth time := by
    simpa only [sourceScatteringGrowth,abs_neg] using spatialFlow_norm 0 (-time)
  exact norm_mul_le_of_le (norm_mul_le_of_le first ((C j).norm_compLpL_le (p:=2) (μ:=volume)))
    (spatialFlow_norm 0 time)

def sourceContactDomainPrice (sideR edgeR : Fin 2) (C : Fin 4→FiberOperators) (time : ℝ) : ℝ :=
  ∑j : Fin 4,sourceContactInteriorPrice C time j*sourceScatteringLegPrice sideR edgeR j

/-- The original direct contact is kept outside the age integral and includes every mixed coefficient. -/
theorem sourcePreparedContact_domain_bound (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) :
    ‖sourceActualScatteringRead sideL edgeL sideR edgeR (contactWord C time)‖ ≤
      sourceContactDomainPrice sideR edgeR C time := by
  rw [sourceActualScatteringRead_source,contactWord]
  simp only [sum_apply,inner_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  change ‖inner ℂ (sourceActualScatteringInput sideL edgeL)
    ((coordinateLeg 0).adjoint (sourceContactInterior C time j
      (coordinateLeg j (sourceActualScatteringInput sideR edgeR))))‖ ≤ _
  rw [ContinuousLinearMap.adjoint_inner_right,sourceActualScatteringInput_return]
  apply (norm_inner_le_norm _ _).trans
  rw [sourceChargedFilteredPacket_unit,one_mul]
  exact ((sourceContactInterior C time j).le_opNorm _).trans
    (mul_le_mul (sourceContactInterior_domain_bound C time j)
      (sourceChargedCoordinateLeg_bound sideR edgeR j) (norm_nonneg _)
      ((norm_nonneg _).trans (sourceContactInterior_domain_bound C time j)))

end LowEnergy.PreparationPhysicalChargedScatteringDomainPrice
