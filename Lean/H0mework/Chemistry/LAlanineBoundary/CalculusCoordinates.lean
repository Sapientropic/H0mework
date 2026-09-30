import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary.Calculus

abbrev Space := Fin 3 → ℝ
abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ

noncomputable section

def unit (i : Fin 3) : Space := Pi.single i 1
def dcoord (f : Space → ℝ) (i : Fin 3) (p : Space) : ℝ := fderiv ℝ f p (unit i)
def jacobian (f : Space → Space) (p : Space) : Matrix3 :=
  fun i j => fderiv ℝ f p (unit j) i

theorem jacobian_contDiff (f : Space → Space) (hf : ContDiff ℝ 2 f) (i j : Fin 3) :
    ContDiff ℝ 1 (fun p => jacobian f p i j) := by
  have h : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  unfold jacobian
  fun_prop

theorem jacobian_partial (f : Space → Space) (hf : ContDiff ℝ 2 f)
    (p : Space) (i j k : Fin 3) :
    dcoord (fun x => jacobian f x i j) k p =
      fderiv ℝ (fderiv ℝ f) p (unit k) (unit j) i := by
  have h : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  unfold dcoord jacobian
  rw [fderiv_apply ((h p).clm_apply (differentiableAt_const _)) i]
  rw [fderiv_clm_apply (h p) (differentiableAt_const _)]
  simp

theorem jacobian_mixed (f : Space → Space) (hf : ContDiff ℝ 2 f)
    (p : Space) (i j k : Fin 3) :
    dcoord (fun x => jacobian f x i j) k p =
      dcoord (fun x => jacobian f x i k) j p := by
  rw [jacobian_partial f hf, jacobian_partial f hf]
  exact congrFun (hf.contDiffAt.isSymmSndFDerivAt (by simp) (unit k) (unit j)) i

theorem partial_add (f g : Space → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (p : Space) :
    dcoord (fun x => f x + g x) i p = dcoord f i p + dcoord g i p := by
  simp only [dcoord, fderiv_fun_add (hf p) (hg p), add_apply]

theorem partial_sub (f g : Space → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (p : Space) :
    dcoord (fun x => f x - g x) i p = dcoord f i p - dcoord g i p := by
  simp only [dcoord, fderiv_fun_sub (hf p) (hg p), sub_apply]

theorem partial_mul (f g : Space → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (p : Space) :
    dcoord (fun x => f x * g x) i p = dcoord f i p * g p + f p * dcoord g i p := by
  simp only [dcoord, fderiv_fun_mul (hf p) (hg p), add_apply, smul_apply, smul_eq_mul]
  ring

theorem partial_neg (f : Space → ℝ) (i : Fin 3) (p : Space) :
    dcoord (fun x => -f x) i p = -dcoord f i p := by
  simp only [dcoord, fderiv_fun_neg, neg_apply]

theorem partial_sum (f : Fin 3 → Space → ℝ) (hf : ∀ j, Differentiable ℝ (f j))
    (i : Fin 3) (p : Space) :
    dcoord (fun x => ∑ j : Fin 3, f j x) i p = ∑ j : Fin 3, dcoord (f j) i p := by
  unfold dcoord
  rw [fderiv_fun_sum (fun j _ => hf j p)]
  simp only [sum_apply]

theorem linear_apply (L : Space →L[ℝ] Space) (v : Space) (i : Fin 3) :
    L v i = ∑ j : Fin 3, L (unit j) i * v j := by
  have split : v = ∑ j : Fin 3, v j • unit j := by
    ext k
    simp [unit, Pi.single_apply]
  calc
    _ = L (∑ j : Fin 3, v j • unit j) i := congrArg (fun w => L w i) split
    _ = _ := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem jacobian_eq_dcoord (f : Space → Space) (hf : Differentiable ℝ f)
    (p : Space) (i j : Fin 3) :
    jacobian f p i j = dcoord (fun x => f x i) j p := by
  unfold jacobian dcoord
  rw [fderiv_apply (hf p) i]
  rfl

theorem partial_comp (f g : Space → Space) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (p : Space) (k i : Fin 3) :
    dcoord (fun x => g (f x) k) i p =
      ∑ j : Fin 3, jacobian g (f p) k j * jacobian f p j i := by
  unfold dcoord
  have composed : HasFDerivAt (fun x => g (f x))
      ((fderiv ℝ g (f p)).comp (fderiv ℝ f p)) p :=
    (hg (f p)).hasFDerivAt.comp p (hf p).hasFDerivAt
  have component := (hasFDerivAt_pi'.mp composed k).fderiv
  calc
    _ = fderiv ℝ g (f p) (fderiv ℝ f p (unit i)) k :=
      congrArg (fun L : Space →L[ℝ] ℝ => L (unit i)) component
    _ = _ := linear_apply (fderiv ℝ g (f p)) (fderiv ℝ f p (unit i)) k

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary.Calculus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
