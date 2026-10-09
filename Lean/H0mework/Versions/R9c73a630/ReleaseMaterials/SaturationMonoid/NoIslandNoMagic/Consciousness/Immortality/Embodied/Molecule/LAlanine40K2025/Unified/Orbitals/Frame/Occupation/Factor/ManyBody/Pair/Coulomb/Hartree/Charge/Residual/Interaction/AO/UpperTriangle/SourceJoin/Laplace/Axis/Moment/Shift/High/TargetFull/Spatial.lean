import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Axis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open MeasureTheory
noncomputable section

def spatialTargetFull
    (sourceLeft sourceRight targetLeft targetRight : Fin 3 → ℕ)
    (p q a b c d e f : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  ∏ i : Fin 3,
    targetFullAxisIntegrand
      (sourceLeft i) (sourceRight i) (targetLeft i) (targetRight i)
      (p i) (q i) (a i) (b i) (c i) (d i) (e i) (f i)
      t (z.1 i,z.2 i)

def spatialTargetFullClosed
    (sourceLeft sourceRight targetLeft targetRight : Fin 3 → ℕ)
    (p q a b c d e f : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∏ i : Fin 3,
    targetFullAxisClosed
      (sourceLeft i) (sourceRight i) (targetLeft i) (targetRight i)
      (p i) (q i) (a i) (b i) (c i) (d i) (e i) (f i) t

theorem spatial_target_full_factor
    (sourceLeft sourceRight targetLeft targetRight : Fin 3 → ℕ)
    (p q a b c d e f : Fin 3 → ℝ) (t : ℝ)
    (hsourceLeft : ∀ i, sourceLeft i < 3)
    (hsourceRight : ∀ i, sourceRight i < 3)
    (htargetLeft : ∀ i, targetLeft i < 3)
    (htargetRight : ∀ i, targetRight i < 3)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      spatialTargetFull sourceLeft sourceRight targetLeft targetRight
        p q a b c d e f t z) =
      spatialTargetFullClosed sourceLeft sourceRight targetLeft targetRight
        p q a b c d e f t := by
  let transport := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      transport.measurableEmbedding
      (spatialTargetFull sourceLeft sourceRight targetLeft targetRight
        p q a b c d e f t)
  rw [← htransport]
  change (∫ z : Fin 3 → ℝ × ℝ,
    ∏ i : Fin 3,
      targetFullAxisIntegrand
        (sourceLeft i) (sourceRight i) (targetLeft i) (targetRight i)
        (p i) (q i) (a i) (b i) (c i) (d i) (e i) (f i) t (z i)) = _
  rw [integral_fintype_prod_volume_eq_prod]
  unfold spatialTargetFullClosed
  apply Finset.prod_congr rfl
  intro i _
  exact target_full_axis_integral
    (sourceLeft i) (sourceRight i) (targetLeft i) (targetRight i)
    (p i) (q i) (a i) (b i) (c i) (d i) (e i) (f i) t
    (hsourceLeft i) (hsourceRight i) (htargetLeft i) (htargetRight i)
    (hp i) (hq i) ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
