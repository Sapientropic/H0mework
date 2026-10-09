import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Value.Coarsening

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble.ValueCoarsening

open SourceGeneratedBodyEnsemble SourceGeneratedWorkInformation SourceGeneratedConditionalWork Collision
open LAlanine40K2025.Thermal.Population
open scoped ENNReal
noncomputable section

private theorem weighted_log_mul (x y : ℝ) :
    x * y * Real.log (x * y) = (x * Real.log x) * y + x * (y * Real.log y) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.log_mul hx hy]
  ring

private theorem branch_entropy {A : Type*} [Fintype A] (p : ℝ) (q : PMF A) :
    ∑ a : A, p * (q a).toReal * Real.log (p * (q a).toReal) =
      p * Real.log p + p * (∑ a : A, (q a).toReal * Real.log (q a).toReal) := by
  conv_lhs =>
    arg 2
    ext a
    rw [weighted_log_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, pmf_sum_toReal, mul_one,
    ← Finset.mul_sum]

theorem original_value_joint_entropy :
    entropy joint = entropy pointerPMF + p0 * entropy observed0 + p1 * entropy observed1 := by
  have h0 : (pointerPMF 0).toReal = p0 := pointer_zero_probability
  have h1 : (pointerPMF 1).toReal = p1 :=
    Born.pointer_one_read contrast contrast_hermitian receivedState
  have j0 := branch_entropy p0 observed0
  have j1 := branch_entropy p1 observed1
  have hj : entropy joint =
      -((∑ v : Value, (joint (0, v)).toReal * Real.log (joint (0, v)).toReal) +
        (∑ v : Value, (joint (1, v)).toReal * Real.log (joint (1, v)).toReal)) := by
    simp only [entropy, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hp : entropy pointerPMF = -(p0 * Real.log p0 + p1 * Real.log p1) := by
    simp only [entropy, Fin.sum_univ_two, h0, h1]
  rw [hj]
  simp_rw [source_joint_left_value, source_joint_right_value]
  rw [j0, j1, hp]
  simp only [entropy]
  ring

theorem original_value_information_entropy :
    sourceMutualInformation = entropy valuePMF -
      p0 * entropy observed0 - p1 * entropy observed1 := by
  rw [source_information_entropy, original_value_joint_entropy]
  ring

theorem indexed_left (i : Current.FullIndex) :
    indexedJoint (0, i) = sourcePMF (Sum.inl i) := by
  classical
  simp [indexedJoint, branchIndex, PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]

theorem indexed_right (i : Current.FullIndex) :
    indexedJoint (1, i) = sourcePMF (Sum.inr i) := by
  classical
  simp [indexedJoint, branchIndex, PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]

theorem original_index_joint_entropy :
    entropy indexedJoint =
      entropy pointerPMF + p0 * entropy measured0 + p1 * entropy measured1 := by
  have h0 : (pointerPMF 0).toReal = p0 := pointer_zero_probability
  have h1 : (pointerPMF 1).toReal = p1 :=
    Born.pointer_one_read contrast contrast_hermitian receivedState
  have j0 := branch_entropy p0 measured0
  have j1 := branch_entropy p1 measured1
  have hj : entropy indexedJoint =
      -((∑ i : Current.FullIndex,
          (indexedJoint (0, i)).toReal * Real.log (indexedJoint (0, i)).toReal) +
        (∑ i : Current.FullIndex,
          (indexedJoint (1, i)).toReal * Real.log (indexedJoint (1, i)).toReal)) := by
    simp only [entropy, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hp : entropy pointerPMF = -(p0 * Real.log p0 + p1 * Real.log p1) := by
    simp only [entropy, Fin.sum_univ_two, h0, h1]
  rw [hj]
  simp_rw [indexed_left, indexed_right, source_index_left, source_index_right]
  rw [j0, j1, hp]
  simp only [entropy]
  ring

local instance : MeasurableSpace (Fin 2) := ⊤
local instance : MeasurableSingletonClass (Fin 2) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace Current.FullIndex := ⊤
local instance : MeasurableSingletonClass Current.FullIndex := ⟨fun _ => trivial⟩

theorem original_index_information_entropy :
    indexedInformation = entropy (Quantum.sndMarginal indexedJoint) -
      p0 * entropy measured0 - p1 * entropy measured1 := by
  rw [indexedInformation, Quantum.jointKL_entropy_commutes,
    indexed_pointer, original_index_joint_entropy]
  ring

theorem value_information_loss_entropy :
    valueInformationLoss =
      (entropy (Quantum.sndMarginal indexedJoint) - entropy valuePMF) -
      p0 * (entropy measured0 - entropy observed0) -
      p1 * (entropy measured1 - entropy observed1) := by
  have hi := original_index_information_entropy
  have hv := original_value_information_entropy
  unfold valueInformationLoss
  rw [hi, hv]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble.ValueCoarsening
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
