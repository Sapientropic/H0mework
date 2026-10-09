import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.DominantMass.Sectors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped BigOperators
noncomputable section

theorem pair_mass_entry_source (a b : Basis) :
    ((pairQ (a,b) (a,b)).1 : ℝ) = (InputProducts.pair (a,b) (a,b)).re := by
  have h := congrFun (congrFun pairQ_value (a,b)) (a,b)
  simpa [qvalue,Scalar.value,Complex.mul_re] using congrArg Complex.re h

theorem full_pair_mass_original_source :
    (fullPairMassQ : ℝ) = InputProducts.pair.trace.re := by
  simp [fullPairMassQ,totalPairZ,Prod.fst_sum,Matrix.trace,Matrix.diag,
    Fintype.sum_prod_type,Rat.cast_sum,pair_mass_entry_source]

private theorem filtered_mass_source (P : Basis → Basis → Prop)
    [DecidableRel P] :
    ((∑ a : Basis, ∑ b : Basis,
      if P a b then (pairQ (a,b) (a,b)).1 else 0 : ℚ) : ℝ) =
      ∑ a : Basis, ∑ b : Basis,
        if P a b then (InputProducts.pair (a,b) (a,b)).re else 0 := by
  simp only [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : P a b <;> simp [h,pair_mass_entry_source]

theorem near_mass_original_source :
    (nearMassQ : ℝ) =
      ∑ a : Basis, ∑ b : Basis,
        if nearCond a b then (InputProducts.pair (a,b) (a,b)).re else 0 := by
  exact filtered_mass_source nearCond

theorem mid_mass_original_source :
    (midMassQ : ℝ) =
      ∑ a : Basis, ∑ b : Basis,
        if midCond a b then (InputProducts.pair (a,b) (a,b)).re else 0 := by
  exact filtered_mass_source midCond

theorem diag2_mass_original_source :
    (diag2MassQ : ℝ) =
      ∑ a : Basis, ∑ b : Basis,
        if diag2Cond a b then (InputProducts.pair (a,b) (a,b)).re else 0 := by
  exact filtered_mass_source diag2Cond

theorem rest_mass_original_source :
    (restMassQ : ℝ) =
      ∑ a : Basis, ∑ b : Basis,
        if restCond a b then (InputProducts.pair (a,b) (a,b)).re else 0 := by
  exact filtered_mass_source restCond

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
