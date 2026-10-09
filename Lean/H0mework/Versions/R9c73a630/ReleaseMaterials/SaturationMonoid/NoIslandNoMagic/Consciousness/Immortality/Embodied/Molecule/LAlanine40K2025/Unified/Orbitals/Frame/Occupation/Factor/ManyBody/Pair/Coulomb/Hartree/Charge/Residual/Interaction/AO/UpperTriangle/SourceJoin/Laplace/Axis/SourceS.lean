import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Source
import H0mework.Versions.AB.Chemistry.LAlanineBandGlobalSource.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
open BasinRefinement.GlobalSource
open BasinRefinement.SourceCoulomb
open MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open scoped BigOperators
noncomputable section

theorem original_s_length : (sourceTerms (2 : Basis)).length = 1 := by decide +kernel

def originalS : Term := (sourceTerms (2 : Basis)).head (by
  intro empty
  have h := original_s_length
  simp [empty] at h)

theorem original_s_powers : ∀ i : Fin 3, (originalS.powers i) = 0 := by decide +kernel

theorem original_s_exponent : 0 < originalS.exponent := by decide +kernel

theorem original_s_singleton : sourceTerms (2 : Basis) = [originalS] := by
  have h := original_s_length
  cases named : sourceTerms (2 : Basis) with
  | nil => simp [named] at h
  | cons first rest =>
      cases rest with
      | nil => simp [originalS,named]
      | cons second tail => simp [named] at h

theorem same_centre (alpha point : ℝ) (positive : 0 < alpha) :
    centre alpha alpha point point = point := by
  unfold centre
  have hn : alpha + alpha ≠ 0 := ne_of_gt (add_pos positive positive)
  field_simp [hn]

theorem original_s_axis (axis : Fin 3) (x : ℝ) :
    axisShape originalS originalS axis x =
      Real.exp (-(2*(originalS.exponent : ℝ)) *
        (x-(originalS.centre axis : ℝ))^2) := by
  unfold axisShape
  rw [original_s_powers axis]
  simp only [pow_zero,mul_one,sub_self,one_mul]
  rw [same_centre _ _ (by exact_mod_cast original_s_exponent)]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,neg_zero,
    Real.exp_zero,one_mul]
  congr 1
  ring

def originalAlpha : ℝ := (originalS.exponent : ℝ)
def originalWeight : ℝ := (originalS.weight : ℝ)
def originalCentre : Point := fun i => (originalS.centre i : ℝ)

theorem original_s_pair_field (x : Point) :
    pairShape originalS originalS x =
      originalWeight^2 *
        ∏ i : Fin 3, Real.exp (-(2*originalAlpha) *
          (x i-originalCentre i)^2) := by
  unfold pairShape originalWeight originalAlpha originalCentre
  rw [original_s_axis 0,original_s_axis 1,original_s_axis 2]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  ring


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
