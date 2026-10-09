import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Table
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceFiniteData
open scoped BigOperators
noncomputable section

theorem quartetERI_le (a b : Fin 4851) :
    |electronRepulsion (targetLeft a.val) (targetRight a.val)
        (targetLeft b.val) (targetRight b.val)| ≤
      (addressMajorant a.val : ℝ) * (addressMajorant b.val : ℝ) :=
  electron_repulsion_majorant _ _ _ _

theorem quartetCoefficientBound (i j : Basis) (address : Fin 4851) :
    (1/10^12 : ℝ) *
        |electronRepulsion (targetLeft address.val) (targetRight address.val) i j| ≤
      (1/10^12 : ℝ) * ((addressMajorant address.val : ℝ) * (pairMajorant i j : ℝ)) :=
  mul_le_mul_of_nonneg_left (electron_repulsion_majorant _ _ i j) (by norm_num)

private theorem quartet_term_bound (address : Fin 4851) (i j : Basis) :
    (1/10^12 : ℝ) *
        |electronRepulsion (targetLeft address.val) (targetRight address.val) i j| ≤
      ((addressMajorant address.val : ℝ) * (pairMajorant i j : ℝ)) * (1/10^12 : ℝ) := by
  have h := quartetCoefficientBound i j address
  calc (1/10^12 : ℝ) *
        |electronRepulsion (targetLeft address.val) (targetRight address.val) i j|
      ≤ (1/10^12 : ℝ) *
        ((addressMajorant address.val : ℝ) * (pairMajorant i j : ℝ)) := h
    _ = ((addressMajorant address.val : ℝ) * (pairMajorant i j : ℝ)) *
          (1/10^12 : ℝ) := by ring

theorem quartet_error_weight_le (i j : Basis) :
    quartetErrorWeight i j ≤
      (1/10^12 : ℝ) * (pairMajorant i j : ℝ) * (sumBound : ℝ) := by
  unfold quartetErrorWeight
  calc ∑ a : Fin 4851, (1/10^12 : ℝ) *
        |electronRepulsion (targetLeft a.val) (targetRight a.val) i j|
      ≤ ∑ a : Fin 4851, (1/10^12 : ℝ) * ((pairMajorant i j : ℝ) *
          (addressMajorant a.val : ℝ)) := by
        apply Finset.sum_le_sum
        intro a _
        calc (1/10^12 : ℝ) *
            |electronRepulsion (targetLeft a.val) (targetRight a.val) i j|
            ≤ ((addressMajorant a.val : ℝ) * (pairMajorant i j : ℝ)) *
                (1/10^12 : ℝ) := quartet_term_bound a i j
          _ = (1/10^12 : ℝ) * ((pairMajorant i j : ℝ) *
                (addressMajorant a.val : ℝ)) := by ring
    _ = (1/10^12 : ℝ) * ∑ a : Fin 4851, ((pairMajorant i j : ℝ) *
          (addressMajorant a.val : ℝ)) := by
          rw [← Finset.mul_sum]
    _ = (1/10^12 : ℝ) * ((pairMajorant i j : ℝ) *
          ∑ a : Fin 4851, (addressMajorant a.val : ℝ)) := by
          congr 1
          rw [← Finset.mul_sum]
    _ = _ := by
          rw [fin4851_sum_addressMajorant]
          ring

theorem pairMajorant_le_amax (p q : Basis) (h : p ≤ q) :
    (pairMajorant p q : ℝ) ≤ (amaxBound : ℝ) := by
  have key := target_upper_pair_surjective ⟨(p, q), by
    simp only [UpperTriangle.sourceUpperPairs, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact h⟩
  rcases key with ⟨a, ha⟩
  have hpair : targetUpperPair a = ⟨(p, q), _⟩ := ha
  have ht : targetPair a = (p, q) := congrArg Subtype.val hpair
  have h1 : targetLeft a.val = p := congrArg Prod.fst ht
  have h2 : targetRight a.val = q := congrArg Prod.snd ht
  rw [Rat.cast_le]
  calc pairMajorant p q = addressMajorant a.val := by
        show pairMajorant p q = pairMajorant (targetLeft a.val) (targetRight a.val)
        rw [h1, h2]
    _ ≤ amaxBound := addressMajorant_le_amax a.val a.isLt

theorem quartetErrorWeight_symm (i j : Basis) :
    quartetErrorWeight i j = quartetErrorWeight j i := by
  unfold quartetErrorWeight
  apply Finset.sum_congr rfl
  intro a _
  rw [electronRepulsion_second_swap]

private theorem quartet_error_weight_upper (i j : Basis) (h : i ≤ j) :
    quartetErrorWeight i j ≤
      (1/10^12 : ℝ) * (amaxBound : ℝ) * (sumBound : ℝ) := by
  calc quartetErrorWeight i j
      ≤ (1/10^12 : ℝ) * (pairMajorant i j : ℝ) * (sumBound : ℝ) :=
        quartet_error_weight_le i j
    _ ≤ (1/10^12 : ℝ) * (amaxBound : ℝ) * (sumBound : ℝ) := by
        apply mul_le_mul _ le_rfl
          (Rat.cast_nonneg.mpr (by unfold sumBound; norm_num))
          (mul_nonneg (by norm_num)
            (Rat.cast_nonneg.mpr (by unfold amaxBound; norm_num)))
        exact mul_le_mul_of_nonneg_left (pairMajorant_le_amax i j h) (by norm_num)

theorem quartet_error_weight_uniform (i j : Basis) :
    quartetErrorWeight i j ≤
      (1/10^12 : ℝ) * (amaxBound : ℝ) * (sumBound : ℝ) := by
  rcases le_total i j with h | h
  · exact quartet_error_weight_upper i j h
  · rw [quartetErrorWeight_symm]
    exact quartet_error_weight_upper j i h

theorem report_J_replacement (i j : Basis) :
    |SourceJoin.material.targetJ i j - SourceJoin.material.reportWeightedJ i j| ≤
      (1/10^12 : ℝ) * (amaxBound : ℝ) * (sumBound : ℝ) := by
  calc |SourceJoin.material.targetJ i j - SourceJoin.material.reportWeightedJ i j|
      ≤ SourceJoin.material.quartetErrorWeight i j := target_J_report_bound i j
    _ = quartetErrorWeight i j := rfl
    _ ≤ (1/10^12 : ℝ) * (amaxBound : ℝ) * (sumBound : ℝ) :=
        quartet_error_weight_uniform i j

theorem report_J_replacement_picohartree (i j : Basis) :
    10^12 * |SourceJoin.material.targetJ i j -
        SourceJoin.material.reportWeightedJ i j| ≤
      (amaxBound : ℝ) * (sumBound : ℝ) := by
  calc 10^12 * |SourceJoin.material.targetJ i j -
        SourceJoin.material.reportWeightedJ i j|
      ≤ 10^12 * ((1/10^12 : ℝ) * (amaxBound : ℝ) * (sumBound : ℝ)) :=
        mul_le_mul_of_nonneg_left (report_J_replacement i j) (by norm_num)
    _ = (amaxBound : ℝ) * (sumBound : ℝ) := by ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
