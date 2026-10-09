import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Weight
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceFiniteData
open scoped BigOperators
noncomputable section

private theorem targetJ_eq_sourceJUpper (i j : Basis) :
    SourceJoin.material.targetJ i j = UpperTriangle.sourceJUpper i j :=
  SourceJoin.target_J_exact i j

private theorem pairWeight_diag (i : Basis) :
    pairWeight (i, i) = Proxy.Correction.d3AO i i := by
  unfold pairWeight
  rw [if_pos rfl]

private theorem pairWeight_of_lt (i j : Basis) (h : i < j) :
    pairWeight (i, j) = Proxy.Correction.d3AO i j + Proxy.Correction.d3AO j i := by
  unfold pairWeight
  rw [if_neg (ne_of_lt h)]

theorem hartree_upper_address :
    UpperTriangle.hartreeUpper = (1/2 : ℝ) * ∑ a : Fin 4851,
      (sourceCoefficientAt a : ℝ) *
        SourceJoin.material.targetJ (targetLeft a.val) (targetRight a.val) := by
  have key : ((∑ i : Basis, Proxy.Correction.d3AO i i * sourceJUpper i i) +
      (∑ i : Basis, ∑ j : Basis, if i < j then
        (Proxy.Correction.d3AO i j + Proxy.Correction.d3AO j i) *
          sourceJUpper i j else 0)) =
      ∑ pair ∈ UpperTriangle.sourceUpperPairs,
        pairWeight (pair.1, pair.2) * sourceJUpper pair.1 pair.2 := by
    rw [← diagonal_upper_eq_source_pairs
      (fun k l => pairWeight (k,l) * sourceJUpper k l)]
    congr 1
  calc UpperTriangle.hartreeUpper
      = (1/2 : ℝ) * ((∑ i : Basis, Proxy.Correction.d3AO i i * sourceJUpper i i) +
          (∑ i : Basis, ∑ j : Basis, if i < j then
            (Proxy.Correction.d3AO i j + Proxy.Correction.d3AO j i) *
              sourceJUpper i j else 0)) := rfl
    _ = (1/2 : ℝ) * ∑ pair ∈ UpperTriangle.sourceUpperPairs,
          pairWeight (pair.1, pair.2) * sourceJUpper pair.1 pair.2 := by
        rw [key]
    _ = (1/2 : ℝ) * ∑ a : Fin 4851,
          pairWeight (targetPair a) *
            sourceJUpper (targetLeft a.val) (targetRight a.val) := by
        rw [← Finset.sum_coe_sort]
        rw [← (targetUpperEquiv.sum_comp (fun pair : UpperTriangle.sourceUpperPairs =>
          pairWeight pair.1 * sourceJUpper pair.1.1 pair.1.2))]
        refine congrArg (fun X : ℝ => (1/2 : ℝ) * X) ?_
        apply Finset.sum_congr rfl
        intro a _
        change pairWeight (targetPair a) *
          sourceJUpper (targetPair a).1 (targetPair a).2 = _
        rfl
    _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        rw [pair_weight_target, targetJ_eq_sourceJUpper]

theorem d3_hartree_address :
    Interaction.d3HartreeEnergy = (1/2 : ℝ) * ∑ a : Fin 4851,
      (sourceCoefficientAt a : ℝ) *
        SourceJoin.material.targetJ (targetLeft a.val) (targetRight a.val) := by
  rw [UpperTriangle.original_hartree_eq_upper]
  exact hartree_upper_address

def reportHartreeEnergy : ℝ :=
  (1/2 : ℝ) * ∑ a : Fin 4851, (reportCoefficientAt a : ℝ) *
    reportWeightedJ (targetLeft a.val) (targetRight a.val)

private theorem source_coeff_diff_bound (a : Fin 4851) :
    |(sourceCoefficientAt a : ℝ) - (reportCoefficientAt a : ℝ)| ≤ (1/10^12 : ℝ) := by
  have h := source_coefficient_report_bound a
  have key : ((|sourceCoefficientAt a - reportCoefficientAt a| : ℚ) : ℝ) <
      ((1/10^12 : ℚ) : ℝ) := by exact_mod_cast h
  rw [Rat.cast_abs, Rat.cast_sub] at key
  have rhs : ((1/10^12 : ℚ) : ℝ) = (1/10^12 : ℝ) := by norm_num
  rw [rhs] at key
  exact le_of_lt key

private theorem product_diff_bound (a b : Fin 4851) :
    |(sourceCoefficientAt a : ℝ) * (sourceCoefficientAt b : ℝ) -
        (reportCoefficientAt a : ℝ) * (reportCoefficientAt b : ℝ)| ≤
      (1/10^12 : ℝ) * (|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|) := by
  calc |(sourceCoefficientAt a : ℝ) * (sourceCoefficientAt b : ℝ) -
        (reportCoefficientAt a : ℝ) * (reportCoefficientAt b : ℝ)|
      = |(sourceCoefficientAt a : ℝ) * ((sourceCoefficientAt b : ℝ) - (reportCoefficientAt b : ℝ)) +
          (reportCoefficientAt b : ℝ) * ((sourceCoefficientAt a : ℝ) - (reportCoefficientAt a : ℝ))| := by
        ring_nf
    _ ≤ |(sourceCoefficientAt a : ℝ)| * |(sourceCoefficientAt b : ℝ) - (reportCoefficientAt b : ℝ)| +
          |(reportCoefficientAt b : ℝ)| * |(sourceCoefficientAt a : ℝ) - (reportCoefficientAt a : ℝ)| := by
        apply (abs_add_le _ _).trans
        rw [abs_mul, abs_mul]
    _ ≤ |(sourceCoefficientAt a : ℝ)| * (1/10^12 : ℝ) +
          |(reportCoefficientAt b : ℝ)| * (1/10^12 : ℝ) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (source_coeff_diff_bound b) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left (source_coeff_diff_bound a) (abs_nonneg _)
    _ = _ := by ring

private theorem term_bound (a b : Fin 4851) :
    |((sourceCoefficientAt a : ℝ) * (sourceCoefficientAt b : ℝ) -
        (reportCoefficientAt a : ℝ) * (reportCoefficientAt b : ℝ)) *
      electronRepulsion (targetLeft a.val) (targetRight a.val)
        (targetLeft b.val) (targetRight b.val)| ≤
      ((1/10^12 : ℝ) * (|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|)) *
        ((addressMajorant a.val : ℝ) * (addressMajorant b.val : ℝ)) := by
  rw [abs_mul]
  exact mul_le_mul (product_diff_bound a b) (quartetERI_le a b)
    (abs_nonneg _)
    (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _)))

private theorem doubleSum_factor :
    ∑ a : Fin 4851, ∑ b : Fin 4851,
        ((1/10^12 : ℝ) * (|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|)) *
          ((addressMajorant a.val : ℝ) * (addressMajorant b.val : ℝ)) =
      (1/10^12 : ℝ) * (sumBound : ℝ) * ((sourceBound : ℝ) + (reportBound : ℝ)) := by
  have inner (a : Fin 4851) :
      (∑ b : Fin 4851,
        ((1/10^12 : ℝ) * (|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|)) *
          ((addressMajorant a.val : ℝ) * (addressMajorant b.val : ℝ))) =
      (1/10^12 : ℝ) * (addressMajorant a.val : ℝ) *
        ((|(sourceCoefficientAt a : ℝ)| * (sumBound : ℝ)) + (reportBound : ℝ)) := by
    calc ∑ b : Fin 4851,
          ((1/10^12 : ℝ) * (|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|)) *
            ((addressMajorant a.val : ℝ) * (addressMajorant b.val : ℝ))
        = ∑ b : Fin 4851,
            ((1/10^12 : ℝ) * (addressMajorant a.val : ℝ)) *
              ((|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|) *
                (addressMajorant b.val : ℝ)) :=
          Finset.sum_congr rfl (fun b _ => by ring)
      _ = ((1/10^12 : ℝ) * (addressMajorant a.val : ℝ)) *
            ∑ b : Fin 4851,
              ((|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|) *
                (addressMajorant b.val : ℝ)) := by
          rw [← Finset.mul_sum]
      _ = ((1/10^12 : ℝ) * (addressMajorant a.val : ℝ)) *
            ((|(sourceCoefficientAt a : ℝ)| *
                ∑ b : Fin 4851, (addressMajorant b.val : ℝ)) +
              ∑ b : Fin 4851, |(reportCoefficientAt b : ℝ)| *
                (addressMajorant b.val : ℝ)) := by
          congr 1
          calc ∑ b : Fin 4851,
                ((|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|) *
                  (addressMajorant b.val : ℝ))
              = ∑ b : Fin 4851,
                  (|(sourceCoefficientAt a : ℝ)| * (addressMajorant b.val : ℝ) +
                    |(reportCoefficientAt b : ℝ)| * (addressMajorant b.val : ℝ)) :=
                Finset.sum_congr rfl (fun b _ => by ring)
            _ = |(sourceCoefficientAt a : ℝ)| *
                  (∑ b : Fin 4851, (addressMajorant b.val : ℝ)) +
                  (∑ b : Fin 4851, |(reportCoefficientAt b : ℝ)| *
                    (addressMajorant b.val : ℝ)) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ((1/10^12 : ℝ) * (addressMajorant a.val : ℝ)) *
            ((|(sourceCoefficientAt a : ℝ)| * (sumBound : ℝ)) + (reportBound : ℝ)) := by
          rw [fin4851_sum_addressMajorant, fin4851_sum_reportCoeffMajorant]
  rw [Finset.sum_congr rfl (fun a _ => inner a)]
  have expand (a : Fin 4851) :
      (1/10^12 : ℝ) * (addressMajorant a.val : ℝ) *
          ((|(sourceCoefficientAt a : ℝ)| * (sumBound : ℝ)) + (reportBound : ℝ)) =
        ((1/10^12 : ℝ) * (sumBound : ℝ)) *
          (|(sourceCoefficientAt a : ℝ)| * (addressMajorant a.val : ℝ)) +
        ((1/10^12 : ℝ) * (reportBound : ℝ)) * (addressMajorant a.val : ℝ) := by
    ring
  rw [Finset.sum_congr rfl (fun a _ => expand a), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    fin4851_sum_sourceCoeffMajorant, fin4851_sum_addressMajorant]
  ring

theorem blyp_coulomb_replacement :
    |Interaction.d3HartreeEnergy - reportHartreeEnergy| ≤ (hartreeBound : ℝ) := by
  have hprod (a : Fin 4851) :
      (sourceCoefficientAt a : ℝ) *
          SourceJoin.material.targetJ (targetLeft a.val) (targetRight a.val) -
        (reportCoefficientAt a : ℝ) *
          reportWeightedJ (targetLeft a.val) (targetRight a.val) =
        ∑ b : Fin 4851,
          ((sourceCoefficientAt a : ℝ) * (sourceCoefficientAt b : ℝ) -
              (reportCoefficientAt a : ℝ) * (reportCoefficientAt b : ℝ)) *
            electronRepulsion (targetLeft a.val) (targetRight a.val)
              (targetLeft b.val) (targetRight b.val) := by
    show (sourceCoefficientAt a : ℝ) * targetAddressedJ (targetLeft a.val) (targetRight a.val) -
        (reportCoefficientAt a : ℝ) * reportWeightedJ (targetLeft a.val) (targetRight a.val) = _
    unfold targetAddressedJ reportWeightedJ
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [electronRepulsion_pair_swap (targetLeft b.val) (targetRight b.val)
      (targetLeft a.val) (targetRight a.val)]
    ring
  rw [d3_hartree_address]
  unfold reportHartreeEnergy
  calc
    |(1/2 : ℝ) * ∑ a : Fin 4851, (sourceCoefficientAt a : ℝ) *
        SourceJoin.material.targetJ (targetLeft a.val) (targetRight a.val) -
      (1/2 : ℝ) * ∑ a : Fin 4851, (reportCoefficientAt a : ℝ) *
        reportWeightedJ (targetLeft a.val) (targetRight a.val)|
        = |(1/2 : ℝ) * ∑ a : Fin 4851,
            ((sourceCoefficientAt a : ℝ) * SourceJoin.material.targetJ
                (targetLeft a.val) (targetRight a.val) -
              (reportCoefficientAt a : ℝ) * reportWeightedJ
                (targetLeft a.val) (targetRight a.val))| := by
          rw [← mul_sub, ← Finset.sum_sub_distrib]
    _ = |(1/2 : ℝ) * ∑ a : Fin 4851, ∑ b : Fin 4851,
          ((sourceCoefficientAt a : ℝ) * (sourceCoefficientAt b : ℝ) -
              (reportCoefficientAt a : ℝ) * (reportCoefficientAt b : ℝ)) *
            electronRepulsion (targetLeft a.val) (targetRight a.val)
              (targetLeft b.val) (targetRight b.val)| := by
          refine congrArg (fun X : ℝ => |X|) ?_
          refine congrArg (fun X : ℝ => (1/2 : ℝ) * X) ?_
          apply Finset.sum_congr rfl
          intro a _
          exact hprod a
    _ = (1/2 : ℝ) * |∑ a : Fin 4851, ∑ b : Fin 4851,
          ((sourceCoefficientAt a : ℝ) * (sourceCoefficientAt b : ℝ) -
              (reportCoefficientAt a : ℝ) * (reportCoefficientAt b : ℝ)) *
            electronRepulsion (targetLeft a.val) (targetRight a.val)
              (targetLeft b.val) (targetRight b.val)| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    _ ≤ (1/2 : ℝ) * ∑ a : Fin 4851, ∑ b : Fin 4851,
          ((1/10^12 : ℝ) * (|(sourceCoefficientAt a : ℝ)| + |(reportCoefficientAt b : ℝ)|)) *
            ((addressMajorant a.val : ℝ) * (addressMajorant b.val : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro a _
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro b _
          exact term_bound a b
    _ = (1/2 : ℝ) * ((1/10^12 : ℝ) * (sumBound : ℝ) *
          ((sourceBound : ℝ) + (reportBound : ℝ))) := by
          congr 1
          exact doubleSum_factor
    _ ≤ (hartreeBound : ℝ) := by
        have h : (1/2 : ℚ) * (1/10^12) * sumBound * (sourceBound + reportBound) ≤
            hartreeBound := by
          unfold hartreeBound sumBound sourceBound reportBound
          decide +kernel
        calc (1/2 : ℝ) * ((1/10^12 : ℝ) * (sumBound : ℝ) *
              ((sourceBound : ℝ) + (reportBound : ℝ)))
            = (((1/2 : ℚ) * (1/10^12) * sumBound * (sourceBound + reportBound) : ℚ) : ℝ) := by
              simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
                Rat.cast_one]
              ring
          _ ≤ (hartreeBound : ℝ) := by exact_mod_cast h

theorem blyp_coulomb_nanohartree :
    10^9 * |Interaction.d3HartreeEnergy - reportHartreeEnergy| ≤ (hartreeNanoBound : ℝ) := by
  calc 10^9 * |Interaction.d3HartreeEnergy - reportHartreeEnergy|
      ≤ 10^9 * (hartreeBound : ℝ) :=
        mul_le_mul_of_nonneg_left blyp_coulomb_replacement (by norm_num)
    _ = (859 : ℝ) := by unfold hartreeBound; norm_num
    _ = (hartreeNanoBound : ℝ) := by unfold hartreeNanoBound; norm_num

theorem hartreeNanoBound_lt : (hartreeNanoBound : ℝ) < 2426 := by
  unfold hartreeNanoBound
  norm_num

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
