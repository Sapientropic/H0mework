import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Closed
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open MeasureTheory
noncomputable section

noncomputable def spatialSCoupled
    (p q a b : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  ∏ i : Fin 3, coupledAxis (p i) (q i) (a i) (b i) t (z.1 i) (z.2 i)

theorem spatial_s_factor
    (p q a b : Fin 3 → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      spatialSCoupled p q a b t z) =
      ∏ i : Fin 3,
        (Real.pi / Real.sqrt (p i*q i+(p i+q i)*t^2)) *
          Real.exp (-(p i*q i*t^2/(p i*q i+(p i+q i)*t^2) *
            (a i-b i)^2)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      e.measurableEmbedding (spatialSCoupled p q a b t)
  rw [← htransport]
  change (∫ z : Fin 3 → ℝ × ℝ,
      ∏ i : Fin 3, coupledAxis (p i) (q i) (a i) (b i) t
        (z i).1 (z i).2) = _
  rw [integral_fintype_prod_volume_eq_prod
    (fun i : Fin 3 => fun v : ℝ × ℝ =>
      coupledAxis (p i) (q i) (a i) (b i) t v.1 v.2)]
  apply Finset.prod_congr rfl
  intro i _
  exact coupled_axis_pair_closed (p i) (q i) (a i) (b i) t (hp i) (hq i) ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
