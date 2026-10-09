import Mathlib.Probability.Distributions.Gaussian.Real
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.First

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
open MeasureTheory ProbabilityTheory
open scoped NNReal
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
noncomputable section

theorem gauss_second (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

theorem pdf_second (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x : ℝ, gaussianPDFReal 0 v x * x^2) = (v : ℝ) := by
  have h := integral_gaussianReal_eq_integral_smul
    (μ := (0 : ℝ)) (v := v) (f := fun x : ℝ => x^2) hv
  rw [gauss_second] at h
  simpa only [smul_eq_mul] using h.symm

theorem gaussian_second_closed (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, x^2 * Real.exp (-b*x^2)) =
      (1/(2*b)) * Real.sqrt (2*Real.pi*(1/(2*b))) := by
  let v : ℝ≥0 := ⟨1/(2*b), by positivity⟩
  have hvpos : 0 < (v:ℝ) := by
    change 0 < 1/(2*b)
    positivity
  have hv : v ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast hvpos
  have h := pdf_second v hv
  have hpoint (x : ℝ) :
      gaussianPDFReal 0 v x * x^2 =
        (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ *
          (x^2 * Real.exp (-b*x^2)) := by
    unfold gaussianPDFReal
    have hvval : (v:ℝ)=1/(2*b) := rfl
    rw [hvval]
    have expEq : -(x-0)^2/(2*(1/(2*b))) = -b*x^2 := by
      field_simp [ne_of_gt hb]
      ring
    rw [expEq]
    ring
  simp_rw [hpoint,integral_const_mul] at h
  have hC : 0 < Real.sqrt (2*Real.pi*(v:ℝ)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hvpos
  have hvval : (v:ℝ)=1/(2*b) := rfl
  rw [hvval] at h hC
  field_simp [ne_of_gt hC] at h ⊢
  linarith

theorem gaussian_second_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x^2 * Real.exp (-b*x^2)) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)

theorem gaussian_second_simple (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, x^2 * Real.exp (-b*x^2)) =
      (1/(2*b)) * Real.sqrt (Real.pi/b) := by
  rw [gaussian_second_closed b hb]
  have h : 2*Real.pi*(1/(2*b)) = Real.pi/b := by
    field_simp [ne_of_gt hb]
  rw [h]

theorem shifted_gaussian_second (b A C : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, (x-A)^2 * Real.exp (-b*(x-C)^2)) =
      ((C-A)^2+1/(2*b))*Real.sqrt (Real.pi/b) := by
  let d : ℝ := C-A
  let g : ℝ → ℝ := fun y => (y+d)^2 * Real.exp (-b*y^2)
  have h := (measurePreserving_add_right (volume : Measure ℝ) (-C)).integral_comp
    (MeasurableEquiv.addRight (-C)).measurableEmbedding g
  have hfun (x : ℝ) : g (x-C) = (x-A)^2 * Real.exp (-b*(x-C)^2) := by
    dsimp [g,d]
    have heq : (x-C)+(C-A) = x-A := by ring
    rw [heq]
  have htranslate :
      (∫ x : ℝ, (x-A)^2 * Real.exp (-b*(x-C)^2)) = ∫ y : ℝ, g y := by
    calc
      _ = ∫ x : ℝ, g (x-C) := by congr 1; funext x; exact (hfun x).symm
      _ = _ := by simpa only [sub_eq_add_neg] using h
  rw [htranslate]
  have h2 := gaussian_second_integrable b hb
  have h1 := integrable_mul_exp_neg_mul_sq hb
  have h0 := integrable_exp_neg_mul_sq hb
  have hpoint (y : ℝ) :
      g y = y^2*Real.exp (-b*y^2) +
        ((2*d)*(y*Real.exp (-b*y^2)) + d^2*Real.exp (-b*y^2)) := by
    dsimp [g]
    ring
  simp_rw [hpoint]
  have hsum :
      (∫ y : ℝ, y^2*Real.exp (-b*y^2) +
        (2*d*(y*Real.exp (-b*y^2)) + d^2*Real.exp (-b*y^2))) =
      (∫ y : ℝ, y^2*Real.exp (-b*y^2)) +
        (∫ y : ℝ, 2*d*(y*Real.exp (-b*y^2))) +
          (∫ y : ℝ, d^2*Real.exp (-b*y^2)) := by
    calc
      _ = (∫ y : ℝ, y^2*Real.exp (-b*y^2)) +
          (∫ y : ℝ, 2*d*(y*Real.exp (-b*y^2)) + d^2*Real.exp (-b*y^2)) := by
            exact integral_add h2 ((h1.const_mul (2*d)).add (h0.const_mul (d^2)))
      _ = _ := by rw [integral_add (h1.const_mul (2*d)) (h0.const_mul (d^2))]; ring
  rw [hsum,integral_const_mul,integral_const_mul,
    gaussian_second_simple b hb,gaussian_first_zero b,integral_gaussian]
  dsimp [d]
  ring

theorem two_gaussian_second (p q A B : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∫ x : ℝ, (x-A)^2 * Real.exp (-p*(x-A)^2) *
      Real.exp (-q*(x-B)^2)) =
      Real.exp (-(p*q/(p+q)*(A-B)^2)) *
        ((centre p q A B - A)^2 + 1/(2*(p+q))) *
        Real.sqrt (Real.pi/(p+q)) := by
  let C := centre p q A B
  have hpq : p+q ≠ 0 := ne_of_gt (add_pos hp hq)
  have pointwise (x : ℝ) :
      (x-A)^2 * Real.exp (-p*(x-A)^2) * Real.exp (-q*(x-B)^2) =
        Real.exp (-(p*q/(p+q)*(A-B)^2)) *
          ((x-A)^2*Real.exp (-(p+q)*(x-C)^2)) := by
    calc
      _ = (x-A)^2 * (Real.exp (-p*(x-A)^2) * Real.exp (-q*(x-B)^2)) := by ring
      _ = _ := by
        rw [exponential_product p q A B x hpq]
        ring
  simp_rw [pointwise]
  rw [integral_const_mul, shifted_gaussian_second (p+q) A C (add_pos hp hq)]
  dsimp [C]
  ring


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
