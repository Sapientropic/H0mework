import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Axis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
open MeasureTheory
noncomputable section

def spatialShift (powers : Fin 3 → ℕ) (p q a b c : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  ∏ i : Fin 3, axisShiftIntegrand (powers i) (p i) (q i)
    (a i) (b i) (c i) t (z.1 i,z.2 i)

def spatialShiftClosed (powers : Fin 3 → ℕ) (p q a b c : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∏ i : Fin 3, axisShiftClosed (powers i) (p i) (q i) (a i) (b i) (c i) t

theorem spatial_shift_factor (powers : Fin 3 → ℕ) (p q a b c : Fin 3 → ℝ) (t : ℝ)
    (hpower : ∀ i, powers i < 3)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ), spatialShift powers p q a b c t z) =
      spatialShiftClosed powers p q a b c t := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      e.measurableEmbedding (spatialShift powers p q a b c t)
  rw [← htransport]
  change (∫ z : Fin 3 → ℝ × ℝ,
    ∏ i : Fin 3, axisShiftIntegrand (powers i) (p i) (q i)
      (a i) (b i) (c i) t (z i)) = _
  rw [integral_fintype_prod_volume_eq_prod]
  unfold spatialShiftClosed
  apply Finset.prod_congr rfl
  intro i _
  exact axis_shift_integral (powers i) (p i) (q i) (a i) (b i) (c i) t
    (hpower i) (hp i) (hq i) ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
