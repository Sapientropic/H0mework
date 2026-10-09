import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.FullTrace

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

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

theorem ordinary_computed_pair_mass_le_full (a b : Basis) (ordered : a < b) :
    (computedOrdinaryPairBlock a b).trace.re ≤ Field.computedPair.trace.re := by
  have nonnegative (i : Basis × Basis) :
      (0 : ℝ) ≤ (Field.computedPair i i).re :=
    (Complex.nonneg_iff.mp (computed_pair_positive.diag_nonneg (i := i))).1
  have h := sum_injective_le_univ (pairAddress a b)
    (source_ordinary_pair_address_injective a b ordered)
    (fun i : Basis × Basis => (Field.computedPair i i).re) nonnegative
  simpa [computedOrdinaryPairBlock, Matrix.trace, Matrix.diag, Complex.re_sum]
    using h

theorem ordinary_computed_pair_mass_lt_two (a b : Basis) (ordered : a < b) :
    (computedOrdinaryPairBlock a b).trace.re < 2 :=
  (ordinary_computed_pair_mass_le_full a b ordered).trans_lt
    source_field_pair_trace_lt_two

theorem staged_ordinary_gain_error_uniform (a b : Basis) (ordered : a < b) :
    |(stagedOrdinaryGainIntQ a b ordered : ℝ) -
      (smallGainQ (s(a,b)) : ℝ)| < (101/10^9 : ℝ) := by
  have source := staged_ordinary_gain_error_by_mass a b ordered
  have mass := ordinary_computed_pair_mass_lt_two a b ordered
  linarith only [source,mass]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
