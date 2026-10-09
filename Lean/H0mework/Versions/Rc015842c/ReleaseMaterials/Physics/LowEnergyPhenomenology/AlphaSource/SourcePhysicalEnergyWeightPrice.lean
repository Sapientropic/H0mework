import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhysicalEnergyWeightOperators

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalEnergyWeightsReturn
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
local instance weightPriceQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder


/-- All three weights retain the original varying inverse, connection and scalar in one actual Hamiltonian jet. -/
theorem sourcePhysicalPrimalWeight_components (p : PhysicalMomentum) (v : Fin 4→ℂ) (i : Fin 3) :
    let s:=sourceVoltageActualState
    let inverse:=Ring.inverse (principalMatrix s.1)
    let axis:=fun k=>fieldDirection (sourceEnergyAxisField i k)
    let inverseJet:=fun k=> -(inverse*sourceCoframeCoefficientJet s.1 (axis k).1 0*inverse)
    sourcePhysicalPrimalWeight p v i=∑k : Fin 4,v k •
      ((-Complex.I) • (inverseJet k*stateLower s+inverse*
        ((∑mu : Fin 4,(sourceCoframeCoefficientJet s.1 (axis k).1 mu*s.2.1 mu+
          coefficientMatrix mu s.1*(axis k).2.1 mu))+(axis k).2.2))+
        ∑j : Fin 3,(p j:ℂ) • (inverseJet k*coefficientMatrix j.succ s.1+
          inverse*sourceCoframeCoefficientJet s.1 (axis k).1 j.succ)) := by
  rw [sourcePhysicalPrimalWeight_axes]
  rfl

/-- The same twelve original field insertions act on the actual independently filtered legs. -/
theorem sourcePhysicalEnergyChannel_axes (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyChannel shift zeta i sideL edgeL sideR edgeR=
      ∑k : Fin 4,fixedMomentum (physicalMomentum shift) zeta k*
        sourceChargedEnergyRead (fieldDirection (sourceEnergyAxisField i k)) shift sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyChannel_weights]
  simp only [sourcePhysicalWeightIntegrand,sourcePhysicalPrimalWeight_axes,map_sum,map_smul,
    sum_apply,smul_apply,inner_sum,inner_smul_right]
  rw [integral_finsetSum]
  · simp only [integral_const_mul,sourceChargedEnergyRead_fourier]
  · intro k _
    exact (sourceChargedEnergyRead_integrable (fieldDirection (sourceEnergyAxisField i k)) shift sideL edgeL sideR edgeR).const_mul _

def sourcePhysicalAxisReference (shift : Position) (i : Fin 3) (k : Fin 4) : ℂ :=
  inner ℂ (PacketNoise.filteredPacket 0 1 (by norm_num))
    (PacketNoise.phaseShift shift (sourceOriginalEnergyVector (fieldDirection (sourceEnergyAxisField i k))))

def sourcePhysicalAxisPreparationPrice (i : Fin 3) (k : Fin 4) (sideL edgeL sideR edgeR : Fin 2) : ℝ :=
  sourceChargedQuantumPrice sideL edgeL*
    (sourceEnergyDiracPrice (fieldDirection (sourceEnergyAxisField i k))/‖sourceChargedRawPacket sideR edgeR‖)+
    sourceEnergyPreparationPrice (fieldDirection (sourceEnergyAxisField i k)) sideR edgeR

def sourcePhysicalChannelReference (shift : Position) (zeta : ℂ) (i : Fin 3) : ℂ :=
  ∑k : Fin 4,fixedMomentum (physicalMomentum shift) zeta k*sourcePhysicalAxisReference shift i k

def sourcePhysicalChannelPreparationPrice (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) : ℝ :=
  ∑k : Fin 4,‖fixedMomentum (physicalMomentum shift) zeta k‖*
    sourcePhysicalAxisPreparationPrice i k sideL edgeL sideR edgeR

/-- The reference packet and both charged preparations have distinct, explicitly priced normalizations. -/
theorem sourcePhysicalEnergyChannel_preparation_difference (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourcePhysicalEnergyChannel shift zeta i sideL edgeL sideR edgeR-sourcePhysicalChannelReference shift zeta i‖≤
      sourcePhysicalChannelPreparationPrice shift zeta i sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyChannel_axes]
  unfold sourcePhysicalChannelReference sourcePhysicalChannelPreparationPrice
  rw [←Finset.sum_sub_distrib]
  simp only [←mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sourceEnergyRead_preparation_difference (fieldDirection (sourceEnergyAxisField i k)) shift sideL edgeL sideR edgeR)
    (norm_nonneg _)

/-- No coordinate of the regular full-current field is dropped from its reference or price. -/
def sourcePhysicalRegularReference (shift : Position) (V : Fin 289→ℂ) : ℂ :=
  ∑j : Fin 289,V j*inner ℂ (PacketNoise.filteredPacket 0 1 (by norm_num))
    (PacketNoise.phaseShift shift (sourceOriginalEnergyVector (fieldDirection (fieldUnit j))))

def sourcePhysicalRegularPreparationPrice (V : Fin 289→ℂ) (sideL edgeL sideR edgeR : Fin 2) : ℝ :=
  ∑j : Fin 289,‖V j‖*(sourceChargedQuantumPrice sideL edgeL*
    (sourceEnergyDiracPrice (fieldDirection (fieldUnit j))/‖sourceChargedRawPacket sideR edgeR‖)+
    sourceEnergyPreparationPrice (fieldDirection (fieldUnit j)) sideR edgeR)

theorem sourcePhysicalRegular_preparation_difference (shift : Position) (V : Fin 289→ℂ)
    (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR V-sourcePhysicalRegularReference shift V‖≤
      sourcePhysicalRegularPreparationPrice V sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyReader_original]
  exact sourceFullEnergyRead_preparation_difference V shift sideL edgeL sideR edgeR

/-- The complete pole/regular response has one error bound on the original source-current coefficients. -/
theorem sourcePhysicalEnergy_three_preparation_difference (q : PhysicalResponsePoint) (shift : Position)
    (zeta : sourceCausalDomain (physicalMomentum shift))
    (sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR : Fin 2) :
    let residue:=sourceActualNativeResidue q (physicalMomentum shift) zeta.val
      (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)
    let coefficient:=fun i : Fin 3=>(sourceChargedDenominator (physicalMomentum shift) zeta.val i)⁻¹*
      sourceSlowRead residue ⟨i.val,by omega⟩
    let regular:=sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q (physicalMomentum shift) zeta.val
      (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)
    ‖sourceChargedModeEnergyRead q shift zeta.val sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR-
      ((∑i : Fin 3,coefficient i*sourcePhysicalChannelReference shift zeta.val i)+
        sourcePhysicalRegularReference shift regular)‖≤
      (∑i : Fin 3,‖coefficient i‖*sourcePhysicalChannelPreparationPrice shift zeta.val i sideL edgeL sideR edgeR)+
        sourcePhysicalRegularPreparationPrice regular sideL edgeL sideR edgeR := by
  dsimp only
  rw [sourcePhysicalEnergy_three_channels]
  rw [add_sub_add_comm]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [←Finset.sum_sub_distrib]
    simp only [←mul_sub]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (sourcePhysicalEnergyChannel_preparation_difference shift zeta.val i sideL edgeL sideR edgeR)
      (norm_nonneg _)
  · exact sourcePhysicalRegular_preparation_difference shift _ sideL edgeL sideR edgeR

end LowEnergy.PreparationPhysicalEnergyWeightsReturn
