import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedEnergyObservable

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedEnergyVariation
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage10 Stage9C.Material.SpinPair
open FullQuantum FullSpace YangMills.FullPairing
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationPhysicalNormalizedFullField PreparationVacuumVoltageGaussGreen
open PreparationVacuumActualFieldQuantization
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

def sourceFullEnergyPreparation (V : Fin 289→ℂ) (shift : Position) (side edge : Fin 2) :
    Hilbert→L[ℂ] FullMatterL2 :=
  ∑j : Fin 289,V j • sourceChargedEnergyPreparation (fieldDirection (fieldUnit j)) shift side edge

def sourceFullEnergyMother (V : Fin 289→ℂ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    YangMills.FullPairing.Mother :=
  fromOperator ((sourceChargedPreparation sideL edgeL).adjoint.comp
    (sourceFullEnergyPreparation V shift sideR edgeR))

def sourceFullEnergyRead (V : Fin 289→ℂ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Compatibility.responseMatrix (sourceFullEnergyMother V shift sideL edgeL sideR edgeR))

/-- Complex fields multiply the original real-axis energy insertions after their full source generation. -/
theorem sourceFullEnergyRead_generated (V : Fin 289→ℂ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceFullEnergyRead V shift sideL edgeL sideR edgeR=
      ∑j : Fin 289,V j*sourceChargedEnergyRead (fieldDirection (fieldUnit j)) shift sideL edgeL sideR edgeR := by
  rw [sourceFullEnergyRead,sourceFullEnergyMother,origin_response,operator_fromOperator]
  change inner ℂ (YangMills.FullPairing.prepared 0)
    ((sourceChargedPreparation sideL edgeL).adjoint
      (sourceFullEnergyPreparation V shift sideR edgeR (YangMills.FullPairing.prepared 0)))=_
  rw [ContinuousLinearMap.adjoint_inner_right,sourceChargedPreparation_applied]
  simp only [sourceFullEnergyPreparation,sum_apply,smul_apply,
    sourceChargedEnergyPreparation_applied,inner_sum,inner_smul_right,sourceChargedEnergyRead_generated]

def sourceFullEnergyPrice (V : Fin 289→ℂ) (side edge : Fin 2) : ℝ :=
  ∑j : Fin 289,‖V j‖*(sourceEnergyDiracPrice (fieldDirection (fieldUnit j))/‖sourceChargedRawPacket side edge‖)

theorem sourceFullEnergyRead_norm (V : Fin 289→ℂ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourceFullEnergyRead V shift sideL edgeL sideR edgeR‖ ≤ sourceFullEnergyPrice V sideR edgeR := by
  rw [sourceFullEnergyRead_generated]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (sourceChargedEnergyRead_norm _ shift sideL edgeL sideR edgeR) (norm_nonneg _)

/-- The actual complete returned field includes its native jet and regular/contact response. -/
def sourceChargedModeEnergyRead (q : PhysicalResponsePoint) (shift : Position) (zeta : ℂ)
    (sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  sourceFullEnergyRead (sourceChargedSecondField q (physicalMomentum shift) zeta
    (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR))
    shift sideL edgeL sideR edgeR

theorem sourceChargedModeEnergyRead_generated (q : PhysicalResponsePoint) (shift : Position) (zeta : ℂ)
    (sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedModeEnergyRead q shift zeta sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR=
      ∑j : Fin 289,(sourceChargedSecondField q (physicalMomentum shift) zeta
        (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)) j*
        ∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
          (sourceEnergyMatrixRead
            (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (fieldUnit j)))
              (physicalMomentum (frequency-shift)))
            (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
  simp only [sourceChargedModeEnergyRead,sourceFullEnergyRead_generated,sourceChargedEnergyRead_fourier]

theorem sourceChargedModeEnergyRead_norm (q : PhysicalResponsePoint) (shift : Position) (zeta : ℂ)
    (sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR : Fin 2) :
    ‖sourceChargedModeEnergyRead q shift zeta sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR‖ ≤
      sourceFullEnergyPrice (sourceChargedSecondField q (physicalMomentum shift) zeta
        (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)) sideR edgeR :=
  sourceFullEnergyRead_norm _ shift sideL edgeL sideR edgeR

/-- The original matching packet keeps its original normalization, before comparison with the charged maker. -/
def sourceOriginalEnergyVector (v : ActionState) : FullMatterL2 :=
  ((‖PacketNoise.rawPacket 0 1 (by norm_num)‖⁻¹ : ℝ):ℂ) •
    sourceEnergyDiracLeg v HistoryPrepared.preparedPacket

def sourceEnergyPreparationPrice (v : ActionState) (side edge : Fin 2) : ℝ :=
  ‖sourceChargedRawPacket side edge‖⁻¹*sourceEnergyDiracPrice v*sourceChargedPreparationDistance side edge+
    |‖sourceChargedRawPacket side edge‖⁻¹-‖PacketNoise.rawPacket 0 1 (by norm_num)‖⁻¹| *sourceEnergyDiracPrice v

attribute [local irreducible] sourceEnergyDiracLeg sourceEnergyDiracPrice sourceEnergyCoefficients

theorem sourceEnergyVector_preparation_difference (v : ActionState) (side edge : Fin 2) :
    ‖sourceChargedEnergyVector v side edge-sourceOriginalEnergyVector v‖ ≤ sourceEnergyPreparationPrice v side edge := by
  let a : ℝ:=‖sourceChargedRawPacket side edge‖⁻¹
  let b : ℝ:=‖PacketNoise.rawPacket 0 1 (by norm_num)‖⁻¹
  let L:=sourceEnergyDiracLeg v
  let x:=sourceChargedSpatialPacket side edge
  let y:=HistoryPrepared.preparedPacket
  have oldBound : ‖L y‖ ≤ sourceEnergyDiracPrice v := by
    calc
      _ ≤ ‖L‖*‖y‖:=L.le_opNorm y
      _ = ‖L‖:=by rw [HistoryPrepared.preparedPacket_unit,mul_one]
      _ ≤ _:=sourceEnergyDiracLeg_norm v
  have differenceBound : ‖L (x-y)‖ ≤ sourceEnergyDiracPrice v*sourceChargedPreparationDistance side edge := by
    calc
      _ ≤ ‖L‖*‖x-y‖:=L.le_opNorm _
      _ ≤ sourceEnergyDiracPrice v*‖x-y‖:=
        mul_le_mul_of_nonneg_right (sourceEnergyDiracLeg_norm v) (norm_nonneg _)
      _ = _:=by rw [sourceChargedPacket_difference]
  have split : (a:ℂ) • L x-(b:ℂ) • L y=(a:ℂ) • L (x-y)+((a-b:ℝ):ℂ) • L y := by
    rw [map_sub,Complex.ofReal_sub]
    module
  change ‖(a:ℂ) • L x-(b:ℂ) • L y‖ ≤ a*sourceEnergyDiracPrice v*sourceChargedPreparationDistance side edge+
    |a-b| *sourceEnergyDiracPrice v
  rw [split]
  calc
    _ ≤ ‖(a:ℂ) • L (x-y)‖+‖((a-b:ℝ):ℂ) • L y‖:=norm_add_le _ _
    _ = a*‖L (x-y)‖+|a-b| *‖L y‖:=by
      rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (sourceChargedRawPacket side edge)))]
    _ ≤ a*(sourceEnergyDiracPrice v*sourceChargedPreparationDistance side edge)+|a-b| *sourceEnergyDiracPrice v:=
      add_le_add (mul_le_mul_of_nonneg_left differenceBound (inv_nonneg.mpr (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left oldBound (abs_nonneg _))
    _ = _:=by ring

/-- Both preparation errors are priced on the actual filtered domain of the full energy variation. -/
theorem sourceEnergyRead_preparation_difference (v : ActionState) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourceChargedEnergyRead v shift sideL edgeL sideR edgeR-
      inner ℂ (PacketNoise.filteredPacket 0 1 (by norm_num))
        (PacketNoise.phaseShift shift (sourceOriginalEnergyVector v))‖ ≤
      sourceChargedQuantumPrice sideL edgeL*(sourceEnergyDiracPrice v/‖sourceChargedRawPacket sideR edgeR‖)+
        sourceEnergyPreparationPrice v sideR edgeR := by
  rw [sourceChargedEnergyRead_generated]
  let old:=PacketNoise.filteredPacket 0 1 (by norm_num)
  let left:=sourceChargedFilteredPacket sideL edgeL
  let right:=PacketNoise.phaseShift shift (sourceChargedEnergyVector v sideR edgeR)
  let oldRight:=PacketNoise.phaseShift shift (sourceOriginalEnergyVector v)
  have split : inner ℂ left right-inner ℂ old oldRight=
      inner ℂ (left-old) right+inner ℂ old (right-oldRight) := by
    rw [inner_sub_left,inner_sub_right]
    ring
  change ‖inner ℂ left right-inner ℂ old oldRight‖ ≤ _
  rw [split]
  calc
    _ ≤ ‖inner ℂ (left-old) right‖+‖inner ℂ old (right-oldRight)‖:=norm_add_le _ _
    _ ≤ ‖left-old‖*‖right‖+‖old‖*‖right-oldRight‖:=add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = ‖left-old‖*‖sourceChargedEnergyVector v sideR edgeR‖+
        ‖sourceChargedEnergyVector v sideR edgeR-sourceOriginalEnergyVector v‖:=by
      rw [PacketNoise.filteredPacket_unit,one_mul,PacketNoise.phaseShift_norm,
        ←map_sub,PacketNoise.phaseShift_norm]
    _ ≤ _:=add_le_add
      (mul_le_mul (sourceChargedFilteredPacket_difference sideL edgeL)
        (sourceChargedEnergyVector_norm v sideR edgeR) (norm_nonneg _)
        ((norm_nonneg _).trans (sourceChargedFilteredPacket_difference sideL edgeL)))
      (sourceEnergyVector_preparation_difference v sideR edgeR)

theorem sourceFullEnergyRead_preparation_difference (V : Fin 289→ℂ) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourceFullEnergyRead V shift sideL edgeL sideR edgeR-
      ∑j : Fin 289,V j*inner ℂ (PacketNoise.filteredPacket 0 1 (by norm_num))
        (PacketNoise.phaseShift shift (sourceOriginalEnergyVector (fieldDirection (fieldUnit j))))‖ ≤
      ∑j : Fin 289,‖V j‖*(sourceChargedQuantumPrice sideL edgeL*
        (sourceEnergyDiracPrice (fieldDirection (fieldUnit j))/‖sourceChargedRawPacket sideR edgeR‖)+
        sourceEnergyPreparationPrice (fieldDirection (fieldUnit j)) sideR edgeR) := by
  rw [sourceFullEnergyRead_generated,←Finset.sum_sub_distrib]
  simp only [←mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sourceEnergyRead_preparation_difference (fieldDirection (fieldUnit j)) shift sideL edgeL sideR edgeR)
    (norm_nonneg _)

end LowEnergy.PreparationPhysicalChargedEnergyVariation
