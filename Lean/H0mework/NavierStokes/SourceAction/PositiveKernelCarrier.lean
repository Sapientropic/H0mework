import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Data.Finsupp.SMul

set_option autoImplicit false
open scoped BigOperators ComplexOrder

namespace SaturationMonoid.NavierStokes.NativePositiveKernelCarrier

noncomputable section

universe u
variable {Index : Type u}

structure Kernel (Index : Type u) where
  matrix : Matrix Index Index ℂ
  positive : matrix.PosSemidef

@[nolint unusedArguments]
def PreSpace (_kernel : Kernel Index) := Index →₀ ℂ

instance (kernel : Kernel Index) : AddCommGroup (PreSpace kernel) := inferInstanceAs (AddCommGroup (Index →₀ ℂ))
instance (kernel : Kernel Index) : Module ℂ (PreSpace kernel) := inferInstanceAs (Module ℂ (Index →₀ ℂ))

def ofPreSpace (kernel : Kernel Index) : PreSpace kernel ≃ₗ[ℂ] (Index →₀ ℂ) := LinearEquiv.refl ℂ _

def pairing (kernel : Kernel Index) (left right : PreSpace kernel) : ℂ :=
  (ofPreSpace kernel left).sum fun i a => (ofPreSpace kernel right).sum fun j b => star a * kernel.matrix i j * b

abbrev core (kernel : Kernel Index) : PreInnerProductSpace.Core ℂ (PreSpace kernel) where
  inner := pairing kernel
  conj_inner_symm left right := by
    change star (pairing kernel right left) = pairing kernel left right
    unfold pairing
    simp only [Finsupp.sum, star_sum, star_mul, star_star]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have same : star (kernel.matrix j i) = kernel.matrix i j := congrFun (congrFun kernel.positive.1 i) j
    rw [same]
    ring
  re_inner_nonneg value := (RCLike.nonneg_iff.mp (kernel.positive.2 (ofPreSpace kernel value))).1
  add_left first second right := by
    unfold pairing
    rw [map_add, Finsupp.sum_add_index' (by intro i; simp) (by
      intro i a b
      simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib])]
  smul_left left right scalar := by
    unfold pairing
    rw [map_smul, Finsupp.sum_smul_index (by intro i; simp)]
    simp only [Finsupp.sum, star_mul, starRingEnd_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

instance (kernel : Kernel Index) : SeminormedAddCommGroup (PreSpace kernel) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := core kernel)

instance (kernel : Kernel Index) : InnerProductSpace ℂ (PreSpace kernel) := InnerProductSpace.ofCore (core kernel)

abbrev Space (kernel : Kernel Index) := UniformSpace.Completion (PreSpace kernel)

def vector (kernel : Kernel Index) (index : Index) : Space kernel := by
  classical
  exact UniformSpace.Completion.coe' ((ofPreSpace kernel).symm (Finsupp.single index (1 : ℂ)))

theorem vector_inner (kernel : Kernel Index) (left right : Index) :
    inner ℂ (vector kernel left) (vector kernel right) = kernel.matrix left right := by
  classical
  rw [vector, vector, UniformSpace.Completion.inner_coe]
  change (Finsupp.single left (1 : ℂ)).sum (fun i a =>
    (Finsupp.single right (1 : ℂ)).sum fun j b => star a * kernel.matrix i j * b) = _
  simp

theorem vector_norm_sq (kernel : Kernel Index) (index : Index) :
    ‖vector kernel index‖ ^ 2 = (kernel.matrix index index).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), vector_inner]
  rfl

end
end SaturationMonoid.NavierStokes.NativePositiveKernelCarrier
