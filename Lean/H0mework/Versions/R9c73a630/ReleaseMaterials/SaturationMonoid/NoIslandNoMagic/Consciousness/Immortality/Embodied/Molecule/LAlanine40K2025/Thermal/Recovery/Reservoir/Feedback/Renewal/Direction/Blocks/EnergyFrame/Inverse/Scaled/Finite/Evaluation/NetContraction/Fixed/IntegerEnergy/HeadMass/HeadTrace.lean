import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.GainError
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

abbrev HeadOrdinary := {p : Basis × Basis // p.1.val < 6 ∧ p.1 < p.2}

private theorem sum_injective_le_univ {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (injective : Function.Injective f) (g : β → ℝ)
    (nonnegative : ∀ b, 0 ≤ g b) :
    (∑ a : α, g (f a)) ≤ ∑ b : β, g b := by
  classical
  calc
    _ = ∑ b ∈ (Finset.univ : Finset α).image f, g b := by
      rw [Finset.sum_image (fun _ _ _ _ h => injective h)]
    _ ≤ ∑ b : β, g b :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun b _ _ => nonnegative b)

theorem head_ordinary_pair_trace_le_full_twice :
    (∑ p : HeadOrdinary,
      (computedOrdinaryPairBlock p.val.1 p.val.2).trace.re) ≤
      2*Field.computedPair.trace.re := by
  classical
  have split (p : HeadOrdinary) :
      (computedOrdinaryPairBlock p.val.1 p.val.2).trace.re =
      (Field.computedPair p.val p.val).re+
      (Field.computedPair (Prod.swap p.val) (Prod.swap p.val)).re := by
    simp [computedOrdinaryPairBlock,Matrix.trace,Matrix.diag,
      Fin.sum_univ_two,pairAddress,Prod.swap]
  simp_rw [split,Finset.sum_add_distrib]
  have nonnegative (i : Basis × Basis) :
      (0 : ℝ) ≤ (Field.computedPair i i).re :=
    (Complex.nonneg_iff.mp (computed_pair_positive.diag_nonneg (i := i))).1
  have direct := sum_injective_le_univ
    (fun p : HeadOrdinary => p.val) Subtype.val_injective
    (fun i : Basis × Basis => (Field.computedPair i i).re) nonnegative
  have reverseInj : Function.Injective
      (fun p : HeadOrdinary => Prod.swap p.val) := by
    intro p q h
    apply Subtype.val_injective
    have := congrArg Prod.swap h
    simpa only [Prod.swap_swap] using this
  have reverse := sum_injective_le_univ
    (fun p : HeadOrdinary => Prod.swap p.val) reverseInj
    (fun i : Basis × Basis => (Field.computedPair i i).re) nonnegative
  have total : (∑ i : Basis × Basis, (Field.computedPair i i).re)=
      Field.computedPair.trace.re := by
    simp [Matrix.trace,Matrix.diag,Complex.re_sum]
  rw [total] at direct reverse
  linarith only [direct,reverse]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
