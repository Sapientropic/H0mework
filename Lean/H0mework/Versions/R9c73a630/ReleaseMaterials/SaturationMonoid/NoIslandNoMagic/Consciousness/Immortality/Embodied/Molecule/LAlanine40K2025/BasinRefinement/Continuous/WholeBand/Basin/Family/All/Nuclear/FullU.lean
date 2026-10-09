import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Assembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionEnergy

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
open LAlanine40K2025.UnifiedOrbitals LAlanine40K2025.UnifiedAction
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- The full U spatial covariant quadratic form contracts to the fourteen-zone
    kinetic sum plus the exact AO connection correction: zone kinetic total and
    AO connection corrections join the original density matrix contraction. -/
theorem full_U_kinetic_zone_join (uTime : ℝ) :
    (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        UnifiedAction.spatialCovariantForm uTime i j) =
      (((∑ z : Option (Fin 13), OneBody.zoneKinetic z)) : ℂ) +
        ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
          ((1/2 : ℂ) * ∑ axis : Fin 3,
            ((UnifiedOrbitals.firstDerivative axis j i : ℂ) *
                connectionPair (spatialSlice uTime 0) axis.succ +
              (UnifiedOrbitals.firstDerivative axis i j : ℂ) *
                star (connectionPair (spatialSlice uTime 0) axis.succ) +
              (UnifiedOrbitals.overlap i j : ℂ) *
                connectionSquare (spatialSlice uTime 0) axis.succ)) := by
  have hsplit : ∀ (f g : Basis → Basis → ℂ),
      (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) * (f i j + g i j)) =
        (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) * f i j) +
          ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) * g i j := by
    intro f g
    simp only [mul_add,Finset.sum_add_distrib]
  have hkin : (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        (UnifiedOrbitals.kinetic i j : ℂ)) =
      (((∑ z : Option (Fin 13), OneBody.zoneKinetic z)) : ℂ) := by
    rw [← Complex.ofReal_sum,OneBody.zone_kinetic_sum,OneBody.total_kinetic_original_ao]
    push_cast
    rfl
  simp_rw [UnifiedAction.original_spatial_form_decomposition]
  rw [hsplit]
  rw [hkin]

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
