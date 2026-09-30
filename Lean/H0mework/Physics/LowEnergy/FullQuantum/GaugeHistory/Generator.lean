import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Source
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Strongly continuous bounded Hamiltonian coefficients generate genuine Hilbert-space curves. -/
set_option autoImplicit false
open Set
open scoped InnerProductSpace NNReal
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def generator (H : ℝ → E →L[ℂ] E) (epsilon time : ℝ) : E →L[ℂ] E :=
  (-Complex.I*(epsilon : ℂ)) • H time

theorem generator_continuous (H : ℝ → E →L[ℂ] E)
    (continuousH : ∀ v, Continuous (fun t => H t v)) (epsilon : ℝ) (v : E) :
    Continuous (fun t => generator H epsilon t v) :=
  (continuousH v).const_smul _

theorem generator_bound (H : ℝ → E →L[ℂ] E) (epsilon time : ℝ) (v : E) :
    ‖generator H epsilon time v‖≤|epsilon| * ‖H time‖*‖v‖ := by
  change ‖(-Complex.I*(epsilon : ℂ)) • H time v‖≤_
  rw [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left ((H time).le_opNorm v) (abs_nonneg epsilon)).trans_eq (mul_assoc _ _ _).symm

variable [CompleteSpace E]

theorem generator_inner_zero (H : ℝ → E →L[ℂ] E)
    (symmetric : ∀ time, IsSelfAdjoint (H time)) (epsilon time : ℝ) (v : E) :
    (inner ℂ v (generator H epsilon time v)).re=0 := by
  have paired := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (symmetric time)) v v
  have real : star (inner ℂ v (H time v))=inner ℂ v (H time v) :=
    (inner_conj_symm _ _).trans paired
  have imaginary : (inner ℂ v (H time v)).im=0 := by
    have same := congrArg Complex.im real
    simp only [Complex.star_def,Complex.conj_im] at same
    linarith
  change (inner ℂ v ((-Complex.I*(epsilon : ℂ)) • H time v)).re=0
  rw [inner_smul_right]
  simp [Complex.mul_re,Complex.mul_im,imaginary]

theorem norm_derivative (H : ℝ → E →L[ℂ] E)
    (symmetric : ∀ time, IsSelfAdjoint (H time)) (epsilon time : ℝ) (curve : ℝ → E)
    (evolves : HasDerivAt curve (generator H epsilon time (curve time)) time) :
    HasDerivAt (fun t => ‖curve t‖^2) 0 time := by
  have right := generator_inner_zero H symmetric epsilon time (curve time)
  have left : (inner ℂ (generator H epsilon time (curve time)) (curve time)).re=0 := by
    have conjugate := congrArg Complex.re
      (inner_conj_symm (curve time) (generator H epsilon time (curve time)))
    change (inner ℂ (generator H epsilon time (curve time)) (curve time)).re=
      (inner ℂ (curve time) (generator H epsilon time (curve time))).re at conjugate
    exact conjugate.trans right
  have generated := Complex.reCLM.hasFDerivAt.comp_hasDerivAt time (evolves.inner ℂ evolves)
  change HasDerivAt (fun t => (inner ℂ (curve t) (curve t)).re)
    ((inner ℂ (curve time) (generator H epsilon time (curve time))+
      inner ℂ (generator H epsilon time (curve time)) (curve time)).re) time at generated
  have self (v : E) : (inner ℂ v v).re=‖v‖^2 := by
    change RCLike.re (inner ℂ v v)=_
    exact inner_self_eq_norm_sq v
  simpa only [self,Complex.add_re,right,left,add_zero] using generated

theorem curve_norm (H : ℝ → E →L[ℂ] E)
    (symmetric : ∀ time, IsSelfAdjoint (H time)) (epsilon delta : ℝ) (curve : ℝ → E)
    (evolves : ∀ t ∈ Ioo (-delta) delta, HasDerivAt curve (generator H epsilon t (curve t)) t)
    (first second : ℝ) (inFirst : first ∈ Ioo (-delta) delta) (inSecond : second ∈ Ioo (-delta) delta) :
    ‖curve first‖=‖curve second‖ := by
  have squared (t : ℝ) (inside : t ∈ Ioo (-delta) delta) : HasDerivAt (fun s => ‖curve s‖^2) 0 t :=
    norm_derivative H symmetric epsilon t curve (evolves t inside)
  have constant := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-delta) delta).isPreconnected
    (fun t inside => (squared t inside).differentiableAt.differentiableWithinAt)
    (fun t inside => (squared t inside).deriv) inFirst inSecond
  nlinarith [norm_nonneg (curve first),norm_nonneg (curve second)]

theorem curve_unique (H : ℝ → E →L[ℂ] E)
    (symmetric : ∀ t, IsSelfAdjoint (H t)) (epsilon delta start : ℝ)
    (located : start ∈ Ioo (-delta) delta) (first second : ℝ → E)
    (left : ∀ t ∈ Ioo (-delta) delta, HasDerivAt first (generator H epsilon t (first t)) t)
    (right : ∀ t ∈ Ioo (-delta) delta, HasDerivAt second (generator H epsilon t (second t)) t)
    (initial : first start=second start) : EqOn first second (Ioo (-delta) delta) := by
  intro t inside
  have difference (s : ℝ) (member : s ∈ Ioo (-delta) delta) :
      HasDerivAt (fun u => first u-second u) (generator H epsilon s (first s-second s)) s := by
    convert! (left s member).sub (right s member) using 1
    simp only [map_sub]
  have same := curve_norm H symmetric epsilon delta (fun s => first s-second s) difference t start inside located
  simpa only [initial,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] using same

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
