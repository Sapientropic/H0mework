import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Axis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
open MeasureTheory
noncomputable section

def spatialLow (powers : Fin 3 → ℕ) (p q a b : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  ∏ i : Fin 3, axisLowIntegrand (powers i) (p i) (q i)
    (a i) (b i) t (z.1 i,z.2 i)

def spatialLowClosed (powers : Fin 3 → ℕ) (p q a b : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∏ i : Fin 3, axisLowClosed (powers i) (p i) (q i) (a i) (b i) t

theorem spatial_low_factor (powers : Fin 3 → ℕ) (p q a b : Fin 3 → ℝ) (t : ℝ)
    (hpower : ∀ i, powers i < 3)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ), spatialLow powers p q a b t z) =
      spatialLowClosed powers p q a b t := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      e.measurableEmbedding (spatialLow powers p q a b t)
  rw [← htransport]
  change (∫ z : Fin 3 → ℝ × ℝ,
    ∏ i : Fin 3, axisLowIntegrand (powers i) (p i) (q i)
      (a i) (b i) t (z i)) = _
  rw [integral_fintype_prod_volume_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact axis_low_integral (powers i) (p i) (q i) (a i) (b i) t
    (hpower i) (hp i) (hq i) ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
