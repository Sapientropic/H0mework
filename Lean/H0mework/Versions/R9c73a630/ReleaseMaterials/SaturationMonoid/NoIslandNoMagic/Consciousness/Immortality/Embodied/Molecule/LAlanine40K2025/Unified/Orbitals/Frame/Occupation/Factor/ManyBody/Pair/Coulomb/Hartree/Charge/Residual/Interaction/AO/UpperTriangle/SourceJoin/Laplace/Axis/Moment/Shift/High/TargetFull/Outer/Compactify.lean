import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
open MeasureTheory Set
noncomputable section

def f (u : ℝ) : ℝ := u/(1-u)

theorem f_deriv (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt f (1/(1-u)^2) u := by
  have hden : (1-u) ≠ 0 := ne_of_gt (sub_pos.mpr hu.2)
  have h := (hasDerivAt_id u).div ((hasDerivAt_id u).const_sub 1) hden
  have heq : (id / fun x : ℝ => 1-id x) = f := by
    funext x
    rfl
  rw [heq] at h
  simp only [id_eq] at h
  have hderiv : (1 * (1-u) - u * (-1))/(1-u)^2 = 1/(1-u)^2 := by
    field_simp [hden]
    ring
  rw [hderiv] at h
  exact h

theorem f_inj : InjOn f (Ioo (0 : ℝ) 1) := by
  intro x hx y hy equal
  have hxden : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have hyden : 1-y ≠ 0 := ne_of_gt (sub_pos.mpr hy.2)
  dsimp [f] at equal
  field_simp [hxden,hyden] at equal
  linarith

theorem f_image : f '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact div_pos hu.1 (sub_pos.mpr hu.2)
  · intro hy
    let u := y/(1+y)
    have hy1 : 0 < 1+y := add_pos_of_nonneg_of_pos (by norm_num) hy
    have hu0 : 0 < u := div_pos hy hy1
    have hu1 : u < 1 := by
      dsimp [u]
      rw [div_lt_one hy1]
      linarith
    refine ⟨u,⟨hu0,hu1⟩,?_⟩
    dsimp [f,u]
    field_simp [ne_of_gt hy1]
    ring

theorem compactify_integral (g : ℝ → ℝ) :
    (∫ t in Ioi (0 : ℝ), g t) =
      ∫ u in Ioo (0 : ℝ) 1, g (u/(1-u))/(1-u)^2 := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun u hu => (f_deriv u hu).hasDerivWithinAt)
    f_inj g
  rw [f_image] at h
  refine h.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hden : 0 < 1-u := sub_pos.mpr hu.2
  have hpos : 0 < (1/(1-u)^2 : ℝ) := by positivity
  simp only [f,abs_of_pos hpos,smul_eq_mul]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
