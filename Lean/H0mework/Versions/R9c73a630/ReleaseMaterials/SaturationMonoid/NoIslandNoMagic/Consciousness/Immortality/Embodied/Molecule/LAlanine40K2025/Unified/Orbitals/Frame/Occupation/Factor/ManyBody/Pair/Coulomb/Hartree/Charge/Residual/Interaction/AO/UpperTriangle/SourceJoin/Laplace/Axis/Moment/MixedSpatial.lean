import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.First
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Spatial

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
noncomputable section

def spatialP0Mixed (p q a b : Fin 3 → ℝ) (t : ℝ)
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  (z.1 0-a 0) * Axis.spatialSCoupled p q a b t z

def firstAxisClosed (p q A B t : ℝ) : ℝ :=
  Real.sqrt (Real.pi/(q+t^2)) *
    Real.exp (-(p*(q*t^2/(q+t^2))/(p+q*t^2/(q+t^2))*(A-B)^2)) *
      (centre p (q*t^2/(q+t^2)) A B - A) *
        Real.sqrt (Real.pi/(p+q*t^2/(q+t^2)))

def sAxisClosed (p q A B t : ℝ) : ℝ :=
  (Real.pi / Real.sqrt (p*q+(p+q)*t^2)) *
    Real.exp (-(p*q*t^2/(p*q+(p+q)*t^2) * (A-B)^2))

def spatialP0MixedClosed (p q a b : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∏ i : Fin 3,
    if i = 0 then firstAxisClosed (p i) (q i) (a i) (b i) t
    else sAxisClosed (p i) (q i) (a i) (b i) t

theorem spatial_p0_mixed_factor (p q a b : Fin 3 → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (ht : 0 < t) :
    (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ), spatialP0Mixed p q a b t z) =
      spatialP0MixedClosed p q a b t := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)
  have htransport :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).integral_comp
      e.measurableEmbedding (spatialP0Mixed p q a b t)
  rw [← htransport]
  let f (i : Fin 3) (v : ℝ × ℝ) : ℝ :=
    if i = 0 then (v.1-a 0) * Axis.coupledAxis (p i) (q i) (a i) (b i) t v.1 v.2
    else Axis.coupledAxis (p i) (q i) (a i) (b i) t v.1 v.2
  change (∫ z : Fin 3 → ℝ × ℝ,
    ((z 0).1-a 0) *
      (∏ i : Fin 3, Axis.coupledAxis (p i) (q i) (a i) (b i) t (z i).1 (z i).2)) = _
  have pointwise (z : Fin 3 → ℝ × ℝ) :
      ((z 0).1-a 0) *
        (∏ i : Fin 3, Axis.coupledAxis (p i) (q i) (a i) (b i) t (z i).1 (z i).2) =
      ∏ i : Fin 3, f i (z i) := by
    simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
    simp [f]
    ring
  simp_rw [pointwise]
  rw [integral_fintype_prod_volume_eq_prod]
  unfold spatialP0MixedClosed
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i = 0
  · subst i
    simp only [f,ite_true,firstAxisClosed]
    exact coupled_axis_first_pair (p 0) (q 0) (a 0) (b 0) t (hp 0) (hq 0) ht
  · simp only [f,if_neg h,sAxisClosed]
    exact Axis.coupled_axis_pair_closed (p i) (q i) (a i) (b i) t (hp i) (hq i) ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
