import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Axis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
open MeasureTheory
noncomputable section

def spatialPair (powersLeft powersRight : Fin 3 → ℕ)
    (p q a b c d : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  ∏ i : Fin 3,
    axisPairIntegrand (powersLeft i) (powersRight i)
      (p i) (q i) (a i) (b i) (c i) (d i) t (z.1 i,z.2 i)

def spatialPairClosed (powersLeft powersRight : Fin 3 → ℕ)
    (p q a b c d : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∏ i : Fin 3,
    axisPairClosed (powersLeft i) (powersRight i)
      (p i) (q i) (a i) (b i) (c i) (d i) t

theorem spatial_pair_factor (powersLeft powersRight : Fin 3 → ℕ)
    (p q a b c d : Fin 3 → ℝ) (t : ℝ)
    (hleft : ∀ i, powersLeft i < 3) (hright : ∀ i, powersRight i < 3)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      spatialPair powersLeft powersRight p q a b c d t z) =
        spatialPairClosed powersLeft powersRight p q a b c d t := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      e.measurableEmbedding (spatialPair powersLeft powersRight p q a b c d t)
  rw [← htransport]
  change (∫ z : Fin 3 → ℝ × ℝ,
    ∏ i : Fin 3,
      axisPairIntegrand (powersLeft i) (powersRight i)
        (p i) (q i) (a i) (b i) (c i) (d i) t (z i)) = _
  rw [integral_fintype_prod_volume_eq_prod]
  unfold spatialPairClosed
  apply Finset.prod_congr rfl
  intro i _
  exact axis_pair_integral (powersLeft i) (powersRight i)
    (p i) (q i) (a i) (b i) (c i) (d i) t
    (hleft i) (hright i) (hp i) (hq i) ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
