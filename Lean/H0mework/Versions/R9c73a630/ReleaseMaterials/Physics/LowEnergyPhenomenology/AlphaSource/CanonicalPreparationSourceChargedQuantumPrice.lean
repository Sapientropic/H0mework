import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedQuantumCurrent

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedPacketQuantumReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9DEF FullQuantum FullSpace SpatialGreen HistoryPrepared HistoryCurrent SpatialResponse
open GaugeGreen ScalarGreen GaugeHistory HistoryVariation PerturbedGreen
open MeasureTheory Filter
open scoped InnerProductSpace Topology

private theorem normalized_difference (a b : FullMatterL2) (nonzeroA : a≠0) (nonzeroB : b≠0) :
    ‖((‖a‖⁻¹ : ℝ):ℂ) • a-((‖b‖⁻¹ : ℝ):ℂ) • b‖≤2*‖a‖⁻¹*‖a-b‖ := by
  have positiveA : 0<‖a‖:=norm_pos_iff.mpr nonzeroA
  have positiveB : 0<‖b‖:=norm_pos_iff.mpr nonzeroB
  have inversePrice : |‖a‖⁻¹-‖b‖⁻¹| *‖b‖≤‖a‖⁻¹*‖a-b‖ := by
    rw [inv_sub_inv positiveA.ne' positiveB.ne',abs_div,abs_of_pos (mul_pos positiveA positiveB)]
    calc
      |‖b‖-‖a‖| /(‖a‖*‖b‖)*‖b‖=‖a‖⁻¹*|‖b‖-‖a‖| := by field_simp
      _≤_ := mul_le_mul_of_nonneg_left
        (by simpa only [norm_sub_rev] using abs_norm_sub_norm_le b a) (inv_nonneg.mpr positiveA.le)
  have expression : ((‖a‖⁻¹ : ℝ):ℂ) • a-((‖b‖⁻¹ : ℝ):ℂ) • b=
      ((‖a‖⁻¹ : ℝ):ℂ) • (a-b)+(((‖a‖⁻¹-‖b‖⁻¹ : ℝ):ℂ)) • b := by
    push_cast
    module
  rw [expression]
  calc
    _≤‖((‖a‖⁻¹ : ℝ):ℂ) • (a-b)‖+‖(((‖a‖⁻¹-‖b‖⁻¹ : ℝ):ℂ)) • b‖ := norm_add_le _ _
    _=‖a‖⁻¹*‖a-b‖+|‖a‖⁻¹-‖b‖⁻¹| *‖b‖ := by
      rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr positiveA),Real.norm_eq_abs]
    _≤‖a‖⁻¹*‖a-b‖+‖a‖⁻¹*‖a-b‖ := add_le_add le_rfl inversePrice
    _=_ := by ring

/-- The price is generated from the original Green norm, the finite source preparation and its actual nonzero raw response. -/
def sourceChargedQuantumPrice (side edge : Fin 2) : ℝ :=
  2*‖sourcePacketDiracFilter‖*sourceChargedPreparationDistance side edge/‖sourceChargedRawPacket side edge‖

theorem sourceChargedFilteredPacket_difference (side edge : Fin 2) :
    ‖sourceChargedFilteredPacket side edge-PacketNoise.filteredPacket 0 1 (by norm_num)‖≤
      sourceChargedQuantumPrice side edge := by
  have price:=normalized_difference (sourceChargedRawPacket side edge)
    (PacketNoise.rawPacket 0 1 (by norm_num)) (sourceChargedRawPacket_nonzero side edge)
    (PacketNoise.rawPacket_nonzero 0 1 (by norm_num))
  change ‖((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourceChargedRawPacket side edge-
    ((‖PacketNoise.rawPacket 0 1 (by norm_num)‖⁻¹ : ℝ):ℂ) • PacketNoise.rawPacket 0 1 (by norm_num)‖≤_
  apply price.trans
  calc
    _≤2*‖sourceChargedRawPacket side edge‖⁻¹*
        (‖sourcePacketDiracFilter‖*sourceChargedPreparationDistance side edge) :=
      mul_le_mul_of_nonneg_left (sourceChargedRawPacket_difference side edge)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr (norm_nonneg _)))
    _=sourceChargedQuantumPrice side edge := by unfold sourceChargedQuantumPrice;ring

/-- Complete source observables compare the two independent new preparations with the original fixed matching packet. -/
theorem sourceChargedQuantumRead_difference (sideL edgeL sideR edgeR : Fin 2) (A : SpatialOperators) :
    ‖sourceChargedQuantumRead sideL edgeL sideR edgeR A-
      State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (PacketNoise.filteredMother 0 1 (by norm_num) A))‖≤
      ‖A‖*(sourceChargedQuantumPrice sideL edgeL+sourceChargedQuantumPrice sideR edgeR) := by
  rw [sourceChargedQuantumRead_generated,PacketNoise.filtered_source_read]
  let old:=PacketNoise.filteredPacket 0 1 (by norm_num)
  let left:=sourceChargedFilteredPacket sideL edgeL
  let right:=sourceChargedFilteredPacket sideR edgeR
  change ‖inner ℂ left (A right)-inner ℂ old (A old)‖≤_
  have split : inner ℂ left (A right)-inner ℂ old (A old)=
      inner ℂ (left-old) (A right)+inner ℂ old (A (right-old)) := by
    rw [inner_sub_left,map_sub,inner_sub_right]
    ring
  have first : ‖inner ℂ (left-old) (A right)‖≤‖A‖*sourceChargedQuantumPrice sideL edgeL := by
    calc
      _≤‖left-old‖*‖A right‖ := norm_inner_le_norm _ _
      _≤‖left-old‖*(‖A‖*‖right‖) := mul_le_mul_of_nonneg_left (A.le_opNorm right) (norm_nonneg _)
      _=‖A‖*‖left-old‖ := by rw [sourceChargedFilteredPacket_unit];ring
      _≤_ := mul_le_mul_of_nonneg_left (sourceChargedFilteredPacket_difference sideL edgeL) (norm_nonneg _)
  have second : ‖inner ℂ old (A (right-old))‖≤‖A‖*sourceChargedQuantumPrice sideR edgeR := by
    calc
      _≤‖old‖*‖A (right-old)‖ := norm_inner_le_norm _ _
      _=‖A (right-old)‖ := by rw [PacketNoise.filteredPacket_unit,one_mul]
      _≤‖A‖*‖right-old‖ := A.le_opNorm _
      _≤_ := mul_le_mul_of_nonneg_left (sourceChargedFilteredPacket_difference sideR edgeR) (norm_nonneg _)
  rw [split]
  exact (norm_add_le _ _).trans ((add_le_add first second).trans_eq (by ring))

variable (gauge direction : ℝ→GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
  (coupling : ℝ) (scalar scalarDirection : ℝ→ScalarProfile)
  (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "B" => returnedReader gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection

/-- The original full primitive current consumes the generated two-preparation error, with its complete fields and ordering. -/
theorem sourceChargedCurrent_difference (probe : GaugeProfile) (scalarProbe : ScalarProfile)
    (sideL edgeL sideR edgeR : Fin 2) (time epsilon : ℝ) :
    ‖sourceChargedCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe sideL edgeL sideR edgeR time epsilon-
      complexCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
        continuousScalar continuousScalarDirection probe scalarProbe
        (PacketNoise.filteredPacket 0 1 (by norm_num)) (PacketNoise.filteredPacket 0 1 (by norm_num)) time epsilon‖≤
      ‖volumeWeight‖*‖principal 0*B (inversePrincipal 0*variation probe scalarProbe) epsilon time‖*
        (sourceChargedQuantumPrice sideL edgeL+sourceChargedQuantumPrice sideR edgeR) := by
  rw [sourceChargedCurrent_read,complexCurrent_operator,←mul_sub,norm_mul]
  have price:=sourceChargedQuantumRead_difference sideL edgeL sideR edgeR
    (principal 0*B (inversePrincipal 0*variation probe scalarProbe) epsilon time)
  rw [PacketNoise.filtered_source_read] at price
  simpa only [bilinearRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    innerSL_apply_apply,mul_assoc] using mul_le_mul_of_nonneg_left price (norm_nonneg volumeWeight)

end LowEnergy.PreparationPhysicalChargedPacketQuantumReturn
