import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.TailPositive.Projection

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def tailSourceBody : LoadedJoint :=
  LoadExecution.receivedWord*maskTail InputProducts.bodyInput*star LoadExecution.receivedWord

def tailReferenceBody : LoadedJoint :=
  LoadExecution.receivedWord*maskTail positiveReferenceInput*star LoadExecution.receivedWord

private theorem raw_energy_pullback (O ρ U : LoadedJoint) :
    energy O (U*ρ*star U)=energy (star U*O*U) ρ := by
  unfold energy
  apply congrArg Complex.re
  calc
    (O*(U*ρ*star U)).trace = ((O*U*ρ)*star U).trace := by simp only [Matrix.mul_assoc]
    _ = (star U*(O*U*ρ)).trace := Matrix.trace_mul_comm _ _
    _ = ((star U*O*U)*ρ).trace := by simp only [Matrix.mul_assoc]

theorem positive_tail_energy_bound :
    |energy LoadExecution.loadedNet tailReferenceBody| < (5/10^7 : ℝ) := by
  rw [tailReferenceBody,raw_energy_pullback]
  have positive := positive_masked_input
  have mass : (maskTail positiveReferenceInput).trace.re < (21/10^8 : ℝ) := by
    rw [masked_reference_trace]
    exact positive_tail_trace_bound
  have massNonnegative : 0 ≤ (maskTail positiveReferenceInput).trace.re :=
    (Complex.nonneg_iff.mp positive.trace_nonneg).1
  have operator := Prepared.sandwich_norm LoadExecution.receivedWord LoadExecution.loadedNet
  have operatorBound : ‖star LoadExecution.receivedWord*LoadExecution.loadedNet*
      LoadExecution.receivedWord‖ ≤ (1001/1000 : ℝ)^2*2 := by
    have square := pow_le_pow_left₀ (norm_nonneg LoadExecution.receivedWord)
      source_received_word_norm_sharp 2
    exact operator.trans (mul_le_mul square source_loaded_net_norm_two
      (norm_nonneg LoadExecution.loadedNet) (by norm_num))
  have raw := energy_norm_mass (star LoadExecution.receivedWord*LoadExecution.loadedNet*
    LoadExecution.receivedWord) (maskTail positiveReferenceInput) positive
  have combined := mul_le_mul operatorBound (le_of_lt mass) massNonnegative (by positivity)
  exact lt_of_le_of_lt (raw.trans combined) (by norm_num)

theorem tail_source_body_error :
    ‖tailSourceBody-tailReferenceBody‖ ≤ (4/10^17 : ℝ) := by
  unfold tailSourceBody tailReferenceBody
  have h := Input.raw_input_error LoadExecution.receivedWord
    (maskTail InputProducts.bodyInput) (maskTail positiveReferenceInput)
  exact h.trans <| le_trans
    (mul_le_mul_of_nonneg_left source_masked_input_error (sq_nonneg _)) <| by
      have sq := pow_le_pow_left₀ (norm_nonneg LoadExecution.receivedWord)
        source_received_word_norm_sharp 2
      nlinarith only [sq]

theorem tail_source_energy_bound :
    |energy LoadExecution.loadedNet tailSourceBody| < (6/10^7 : ℝ) := by
  have dimension : Fintype.card (PairController × Fin 2) = 38416 := by
    simp [PairController,Basis]
  have difference : |energy LoadExecution.loadedNet tailSourceBody-
      energy LoadExecution.loadedNet tailReferenceBody| ≤
      (38416 : ℝ)*2*(4/10^17 : ℝ) := by
    have h := Input.energy_dimension_norm LoadExecution.loadedNet
      (tailSourceBody-tailReferenceBody)
    simp only [energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re] at h ⊢
    rw [dimension] at h
    exact h.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left source_loaded_net_norm_two (by norm_num))
      tail_source_body_error (norm_nonneg _) (by positivity))
  have triangle := abs_add_le
    (energy LoadExecution.loadedNet tailSourceBody-
      energy LoadExecution.loadedNet tailReferenceBody)
    (energy LoadExecution.loadedNet tailReferenceBody)
  have original : energy LoadExecution.loadedNet tailSourceBody =
      (energy LoadExecution.loadedNet tailSourceBody-
        energy LoadExecution.loadedNet tailReferenceBody)+
      energy LoadExecution.loadedNet tailReferenceBody := by ring
  rw [original]
  linarith only [triangle,difference,positive_tail_energy_bound]

def tailSector (k : Sym2 Basis) : Prop :=
  ∃ a b : Basis, k = s(a,b) ∧ 6 ≤ a.val ∧ 6 ≤ b.val

noncomputable instance tailSectorDecidable (k : Sym2 Basis) : Decidable (tailSector k) :=
  Classical.propDecidable _

theorem tail_sector_iff (a b : Basis) :
    tailSector (s(a,b)) ↔ 6 ≤ a.val ∧ 6 ≤ b.val := by
  constructor
  · rintro ⟨x,y,h,hx,hy⟩
    have orientation : (a,b) = (x,y) ∨ (a,b) = (y,x) :=
      Sym2.mk_eq_mk_iff.mp h
    rcases orientation with direct | reverse
    · cases direct
      exact ⟨hx,hy⟩
    · cases reverse
      exact ⟨hy,hx⟩
  · intro h
    exact ⟨a,b,rfl,h⟩

theorem in_tail_iff_sector (i : PairController × Fin 2) :
    inTail i ↔ tailSector (pceOrbit i) := by
  change (6 ≤ i.1.1.1.val ∧ 6 ≤ i.1.1.2.val) ↔
    tailSector (s(i.1.1.1,i.1.1.2))
  exact (tail_sector_iff _ _).symm

theorem mask_tail_apply (A : LoadedJoint) (i j : PairController × Fin 2) :
    maskTail A i j = if inTail i ∧ inTail j then A i j else 0 := by
  rw [maskTail,tailProjection,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : inTail i <;> by_cases hj : inTail j <;> simp [hi,hj]

theorem restrict_mask_tail (A : LoadedJoint) (k : Sym2 Basis) :
    restrict pceOrbit k (maskTail A) =
      if tailSector k then restrict pceOrbit k A else 0 := by
  classical
  ext i j
  have hi : inTail i.val ↔ tailSector k := by rw [in_tail_iff_sector,i.property]
  have hj : inTail j.val ↔ tailSector k := by rw [in_tail_iff_sector,j.property]
  simp only [restrict,Matrix.submatrix_apply,mask_tail_apply]
  by_cases hk : tailSector k
  · simp [hk,hi.mpr hk,hj.mpr hk]
  · simp [hk,hi,hj]

theorem local_tail_body (k : Sym2 Basis) :
    restrict pceOrbit k tailSourceBody =
      if tailSector k then localBody k else 0 := by
  classical
  rw [tailSourceBody]
  rw [Matrix.star_eq_conjTranspose,
    restrict_mul_right (preserves_star received_preserves),
    restrict_mul received_preserves,restrict_star]
  rw [restrict_mask_tail]
  by_cases hk : tailSector k
  · simp only [if_pos hk]
    rfl
  · simp only [if_neg hk,Matrix.mul_zero,zero_mul]

theorem actual_tail_sector_energy :
    energy LoadExecution.loadedNet tailSourceBody =
      ∑ k : Sym2 Basis, if tailSector k then programEnergy k else 0 := by
  classical
  rw [energy_eq_sum_restrict net_preserves]
  apply Finset.sum_congr rfl
  intro k _
  rw [local_tail_body,local_readout_exact]
  by_cases hk : tailSector k <;> simp [hk,programEnergy,energy]

theorem actual_tail_sector_budget :
    |∑ k : Sym2 Basis, if tailSector k then programEnergy k else 0| <
      (6/10^7 : ℝ) := by
  rw [← actual_tail_sector_energy]
  exact tail_source_energy_bound

theorem original_rational_tail_budget :
    |((∑ k : Sym2 Basis, if tailSector k then smallGainQ k else 0 : ℚ) : ℝ)| <
      (6/10^7 : ℝ) := by
  rw [Rat.cast_sum]
  have same : (∑ k : Sym2 Basis,
      ((if tailSector k then smallGainQ k else 0 : ℚ) : ℝ)) =
      ∑ k : Sym2 Basis, if tailSector k then programEnergy k else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : tailSector k
    · rw [if_pos hk,if_pos hk,← block_gain_small,block_gain_value]
    · simp [hk]
  rw [same]
  exact actual_tail_sector_budget

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
