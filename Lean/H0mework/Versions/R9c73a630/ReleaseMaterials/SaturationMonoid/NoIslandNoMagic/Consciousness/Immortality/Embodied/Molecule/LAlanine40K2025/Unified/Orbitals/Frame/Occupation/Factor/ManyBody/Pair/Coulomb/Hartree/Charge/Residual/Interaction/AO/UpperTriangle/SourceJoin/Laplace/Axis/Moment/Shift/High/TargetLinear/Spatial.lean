import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Axis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
open MeasureTheory
noncomputable section

def spatialTargetLinear
    (sourceLeft sourceRight targetLeft : Fin 3 → ℕ)
    (p q a b c d e : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  ∏ i : Fin 3,
    targetAxisIntegrand (sourceLeft i) (sourceRight i) (targetLeft i)
      (p i) (q i) (a i) (b i) (c i) (d i) (e i) t (z.1 i,z.2 i)

def spatialTargetLinearClosed
    (sourceLeft sourceRight targetLeft : Fin 3 → ℕ)
    (p q a b c d e : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∏ i : Fin 3,
    targetAxisClosed (sourceLeft i) (sourceRight i) (targetLeft i)
      (p i) (q i) (a i) (b i) (c i) (d i) (e i) t

theorem spatial_target_linear_factor
    (sourceLeft sourceRight targetLeft : Fin 3 → ℕ)
    (p q a b c d e : Fin 3 → ℝ) (t : ℝ)
    (hsourceLeft : ∀ i, sourceLeft i < 3)
    (hsourceRight : ∀ i, sourceRight i < 3)
    (htargetLeft : ∀ i, targetLeft i < 2)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      spatialTargetLinear sourceLeft sourceRight targetLeft
        p q a b c d e t z) =
      spatialTargetLinearClosed sourceLeft sourceRight targetLeft
        p q a b c d e t := by
  let transport := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      transport.measurableEmbedding
      (spatialTargetLinear sourceLeft sourceRight targetLeft p q a b c d e t)
  rw [← htransport]
  change (∫ z : Fin 3 → ℝ × ℝ,
    ∏ i : Fin 3,
      targetAxisIntegrand (sourceLeft i) (sourceRight i) (targetLeft i)
        (p i) (q i) (a i) (b i) (c i) (d i) (e i) t (z i)) = _
  rw [integral_fintype_prod_volume_eq_prod]
  unfold spatialTargetLinearClosed
  apply Finset.prod_congr rfl
  intro i _
  exact target_axis_integral
    (sourceLeft i) (sourceRight i) (targetLeft i)
    (p i) (q i) (a i) (b i) (c i) (d i) (e i) t
    (hsourceLeft i) (hsourceRight i) (htargetLeft i)
    (hp i) (hq i) ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
