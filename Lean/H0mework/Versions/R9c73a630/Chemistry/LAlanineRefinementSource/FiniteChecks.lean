import H0mework.Versions.AB.Chemistry.LAlanineRefinementSource.FiniteData
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.MatrixChecks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFiniteChecks

open SourceGaussianModel SourceFiniteData

theorem radius_nonnegative : 0 ≤ boxRadius := by decide +kernel

theorem actual_source_exponents :
    ∀ j : Basis, (sourceTerms j).all (fun term => decide (0 ≤ term.exponent)) = true := by
  decide +kernel

theorem source_exponents_nonnegative (j : Basis) :
    ∀ term ∈ sourceTerms j, 0 ≤ term.exponent := by
  simpa only [List.all_eq_true, decide_eq_true_eq] using actual_source_exponents j

theorem actual_density_matrix_envelope :
    ∀ i j : Basis, |densityMatrix i j| ≤ densityMatrixBound i j := by
  exact SharedMatrixChecks.original_matrix_envelope

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFiniteChecks
