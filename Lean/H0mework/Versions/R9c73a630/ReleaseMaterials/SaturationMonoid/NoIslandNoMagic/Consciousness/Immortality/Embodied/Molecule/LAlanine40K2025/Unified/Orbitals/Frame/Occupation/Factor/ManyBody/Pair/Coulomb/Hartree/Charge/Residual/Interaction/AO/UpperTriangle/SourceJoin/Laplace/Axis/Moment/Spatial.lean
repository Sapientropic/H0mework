import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.First
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Spatial

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open MeasureTheory
noncomputable section

def spatialP0Coupled (p q a : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  (z.1 0-a 0) * Axis.spatialSCoupled p q a a t z

theorem spatial_p0_same_centre_zero (p q a : Fin 3 → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ), spatialP0Coupled p q a t z) = 0 := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      e.measurableEmbedding (spatialP0Coupled p q a t)
  rw [← htransport]
  let f (i : Fin 3) (v : ℝ × ℝ) : ℝ :=
    if i = 0 then (v.1-a 0) * Axis.coupledAxis (p i) (q i) (a i) (a i) t v.1 v.2
    else Axis.coupledAxis (p i) (q i) (a i) (a i) t v.1 v.2
  change (∫ z : Fin 3 → ℝ × ℝ,
    ((z 0).1-a 0) *
      (∏ i : Fin 3, Axis.coupledAxis (p i) (q i) (a i) (a i) t (z i).1 (z i).2)) = 0
  have pointwise (z : Fin 3 → ℝ × ℝ) :
      ((z 0).1-a 0) *
        (∏ i : Fin 3, Axis.coupledAxis (p i) (q i) (a i) (a i) t (z i).1 (z i).2) =
      ∏ i : Fin 3, f i (z i) := by
    simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
    simp [f]
    ring
  simp_rw [pointwise]
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  simp only [f,ite_true]
  rw [coupled_axis_first_same_centre (p 0) (q 0) (a 0) t (hp 0) (hq 0) ht]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
