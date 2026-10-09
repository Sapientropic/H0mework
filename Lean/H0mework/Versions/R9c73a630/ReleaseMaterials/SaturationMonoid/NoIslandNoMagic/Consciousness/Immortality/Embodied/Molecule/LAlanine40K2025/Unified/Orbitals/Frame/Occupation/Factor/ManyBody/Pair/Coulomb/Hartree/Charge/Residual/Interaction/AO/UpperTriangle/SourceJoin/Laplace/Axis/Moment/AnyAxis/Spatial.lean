import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedSpatial

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
open MeasureTheory
noncomputable section

def spatialPMixed (axis : Fin 3) (p q a b : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  (z.1 axis-a axis) * Axis.spatialSCoupled p q a b t z

def spatialPMixedClosed (axis : Fin 3) (p q a b : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∏ i : Fin 3,
    if i = axis then Moment.firstAxisClosed (p i) (q i) (a i) (b i) t
    else Moment.sAxisClosed (p i) (q i) (a i) (b i) t

theorem spatial_p_mixed_factor (axis : Fin 3) (p q a b : Fin 3 → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ), spatialPMixed axis p q a b t z) =
      spatialPMixedClosed axis p q a b t := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      e.measurableEmbedding (spatialPMixed axis p q a b t)
  rw [← htransport]
  let f (i : Fin 3) (v : ℝ × ℝ) : ℝ :=
    if i = axis then (v.1-a axis) * Axis.coupledAxis (p i) (q i) (a i) (b i) t v.1 v.2
    else Axis.coupledAxis (p i) (q i) (a i) (b i) t v.1 v.2
  change (∫ z : Fin 3 → ℝ × ℝ,
    ((z axis).1-a axis) *
      (∏ i : Fin 3, Axis.coupledAxis (p i) (q i) (a i) (b i) t (z i).1 (z i).2)) = _
  have pointwise (z : Fin 3 → ℝ × ℝ) :
      ((z axis).1-a axis) *
        (∏ i : Fin 3, Axis.coupledAxis (p i) (q i) (a i) (b i) t (z i).1 (z i).2) =
      ∏ i : Fin 3, f i (z i) := by
    fin_cases axis <;>
      simp [f,Fin.prod_univ_succ] <;> ring
  simp_rw [pointwise]
  rw [integral_fintype_prod_volume_eq_prod]
  unfold spatialPMixedClosed
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i = axis
  · subst i
    simp only [f,ite_true,Moment.firstAxisClosed]
    exact Moment.coupled_axis_first_pair
      (p axis) (q axis) (a axis) (b axis) t (hp axis) (hq axis) ht
  · simp only [f,if_neg h,Moment.sAxisClosed]
    exact Axis.coupled_axis_pair_closed (p i) (q i) (a i) (b i) t (hp i) (hq i) ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
