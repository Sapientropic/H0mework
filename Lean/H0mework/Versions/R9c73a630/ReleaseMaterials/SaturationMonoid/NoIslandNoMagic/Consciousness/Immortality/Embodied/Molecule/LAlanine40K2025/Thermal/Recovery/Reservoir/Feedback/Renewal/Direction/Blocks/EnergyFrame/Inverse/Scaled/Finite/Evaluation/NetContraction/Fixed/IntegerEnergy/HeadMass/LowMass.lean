import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.SectorPartition
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Powered.Dynamics
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

/-! The remaining 78 ordinary addresses spend only their original rest-sector mass. -/

def headLowPairEmbedding (s : HeadRestLow × Fin 2) :
    PairSector (fun p => restCond p.1 p.2) :=
  ⟨if s.2=0 then s.1.val.val.val else s.1.val.val.val.swap, by
    split_ifs
    · exact ⟨s.1.val.property.1,s.1.val.property.2,by
        rintro ⟨h,_⟩
        exact ne_of_lt s.1.val.val.property.2 h⟩
    · refine ⟨?_,?_,?_⟩
      · intro h
        exact s.1.val.property.1 ⟨Ne.symm h.1,Or.symm h.2⟩
      · intro h
        exact s.1.val.property.2 (Or.symm h)
      · rintro ⟨h,_⟩
        exact ne_of_lt s.1.val.val.property.2 h.symm⟩

theorem head_low_pair_embedding_injective : Function.Injective headLowPairEmbedding := by
  decide +kernel

def headLowReferenceMass : ℝ :=
  ∑ p : HeadRestLow, (computedOrdinaryBody p.val.val.val.1 p.val.val.val.2).trace.re

theorem head_low_reference_mass_le_rest : headLowReferenceMass ≤ restComputedMass := by
  classical
  have sum_le : (∑ s : HeadRestLow × Fin 2,
      (Field.computedPair (headLowPairEmbedding s).val (headLowPairEmbedding s).val).re) ≤
      ∑ p : PairSector (fun p => restCond p.1 p.2), (Field.computedPair p.val p.val).re := by
    calc
      _ = ∑ p ∈ (Finset.univ : Finset (HeadRestLow × Fin 2)).image headLowPairEmbedding,
          (Field.computedPair p.val p.val).re := by
        rw [Finset.sum_image (fun _ _ _ _ h => head_low_pair_embedding_injective h)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun p _ _ => (Complex.nonneg_iff.mp (computed_pair_positive.diag_nonneg (i := p.val))).1)
  have expanded : headLowReferenceMass = ∑ s : HeadRestLow × Fin 2,
      (Field.computedPair (headLowPairEmbedding s).val (headLowPairEmbedding s).val).re := by
    simp only [headLowReferenceMass,computed_ordinary_body_trace]
    simp [computedOrdinaryPairBlock,Matrix.trace,Matrix.diag,Fintype.sum_prod_type,
      Fin.sum_univ_two,headLowPairEmbedding,pairAddress,Prod.swap]
  rw [expanded]
  convert sum_le using 1
  simp only [restComputedMass,computedSectorPair,Matrix.trace,Matrix.diag,
    Matrix.submatrix_apply,Complex.re_sum]

theorem head_low_reference_mass_upper : headLowReferenceMass < (515/100000 : ℝ) :=
  head_low_reference_mass_le_rest.trans_lt rest_computed_mass_bound

def headRestLowStagedGain : ℚ :=
  ∑ p : HeadRestLow,
    stagedOrdinaryGainIntQ p.val.val.val.1 p.val.val.val.2 p.val.val.property.2

theorem head_low_original_staged_error :
    |(headRestLowStagedGain : ℝ)-headRestLowOriginalGain| < (3/10^10 : ℝ) := by
  have point (p : HeadRestLow) := staged_ordinary_gain_error_by_mass
    p.val.val.val.1 p.val.val.val.2 p.val.val.property.2
  have bound : |(headRestLowStagedGain : ℝ)-headRestLowOriginalGain| ≤
      ∑ p : HeadRestLow,
        ((5/10^8 : ℝ)*(computedOrdinaryBody p.val.val.val.1 p.val.val.val.2).trace.re+1/10^20) := by
    simp only [headRestLowStagedGain,headRestLowOriginalGain,Rat.cast_sum,← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro p _
    rw [computed_ordinary_body_trace]
    exact point p
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,head_rest_low_card,nsmul_eq_mul] at bound
  change |(headRestLowStagedGain : ℝ)-headRestLowOriginalGain| ≤
    (5/10^8)*headLowReferenceMass+78*(1/10^20) at bound
  have mass := head_low_reference_mass_upper
  linarith only [bound,mass]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
