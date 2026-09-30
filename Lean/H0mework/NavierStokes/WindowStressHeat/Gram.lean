import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import H0mework.NavierStokes.Fourier.CoarseFilterCore

set_option autoImplicit false
open scoped BigOperators TensorProduct
namespace SaturationMonoid.NavierStokes.NativeWindowStressHeatGram
open ThreeDimensionalPeriodicCoarseFilterCore
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def pairing (first last : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ output : Fin 3, ∑ input : Fin 3, first output input*last output input

def gram (value : Fin 3 → H) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.gram ℝ value

def cross (first last : Fin 3 → H) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun output input => inner ℝ (first output) (last input)+inner ℝ (last output) (first input)

def gradientGram (gradient : Fin 3 → Fin 3 → H) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ direction : Fin 3, gram (gradient direction)

theorem gram_positive (value : Fin 3 → H) : (gram value).PosSemidef := Matrix.posSemidef_gram _ _

theorem gradient_positive (gradient : Fin 3 → Fin 3 → H) : (gradientGram gradient).PosSemidef :=
  Matrix.posSemidef_sum _ (fun direction _ => gram_positive (gradient direction))

theorem pairing_tensor_square (first last : Fin 3 → H) :
    pairing (gram first) (gram last) = ‖∑ coordinate : Fin 3, first coordinate ⊗ₜ[ℝ] last coordinate‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,TensorProduct.inner_tmul,pairing,gram,Matrix.gram_apply]
  exact Finset.sum_comm

theorem trace_gradient_square (value : Fin 3 → H) (gradient : Fin 3 → Fin 3 → H) :
    Matrix.trace (gram value*gradientGram gradient) =
      ∑ direction : Fin 3, ‖∑ coordinate : Fin 3, value coordinate ⊗ₜ[ℝ] gradient direction coordinate‖^2 := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,gradientGram,Matrix.sum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro direction _
  rw [← pairing_tensor_square]
  unfold pairing gram
  simp only [Matrix.gram_apply]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  rw [real_inner_comm (gradient direction input) (gradient direction output)]

theorem trace_gradient_nonnegative (value : Fin 3 → H) (gradient : Fin 3 → Fin 3 → H) :
    0 ≤ Matrix.trace (gram value*gradientGram gradient) := by
  rw [trace_gradient_square]
  exact Finset.sum_nonneg fun direction _ => sq_nonneg _

theorem pairing_gradient_trace (value : Fin 3 → H) (gradient : Fin 3 → Fin 3 → H) :
    pairing (gram value) (gradientGram gradient) = Matrix.trace (gram value*gradientGram gradient) := by
  simp only [pairing,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,gradientGram,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  apply Finset.sum_congr rfl
  intro direction _
  exact real_inner_comm _ _

theorem gram_hasDerivAt {path : ℝ → Fin 3 → H} {tangent : Fin 3 → H} {time : ℝ}
    (actual : HasDerivAt path tangent time) :
    HasDerivAt (fun parameter => gram (path parameter)) (cross (path time) tangent) time := by
  apply hasDerivAt_pi.mpr
  intro output
  apply hasDerivAt_pi.mpr
  intro input
  exact (hasDerivAt_pi.mp actual output).inner ℝ (hasDerivAt_pi.mp actual input)

theorem cross_hasDerivAt {first last : ℝ → Fin 3 → H} {firstJet lastJet : Fin 3 → H} {time : ℝ}
    (firstActual : HasDerivAt first firstJet time) (lastActual : HasDerivAt last lastJet time) :
    HasDerivAt (fun parameter => cross (first parameter) (last parameter))
      (cross firstJet (last time)+cross (first time) lastJet) time := by
  apply hasDerivAt_pi.mpr
  intro output
  apply hasDerivAt_pi.mpr
  intro input
  have first := (hasDerivAt_pi.mp firstActual output).inner ℝ (hasDerivAt_pi.mp lastActual input)
  have last := (hasDerivAt_pi.mp lastActual output).inner ℝ (hasDerivAt_pi.mp firstActual input)
  convert! first.add last using 1
  simp only [cross,Matrix.add_apply]
  ring

def secondGram (value : Fin 3 → H) (gradient second : Fin 3 → Fin 3 → H) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ direction : Fin 3, (cross value (second direction)+(2 : ℝ) • gram (gradient direction))

theorem secondGram_split (value : Fin 3 → H) (gradient second : Fin 3 → Fin 3 → H) :
    secondGram value gradient second = cross value (∑ direction : Fin 3, second direction)+
      (2 : ℝ) • gradientGram gradient := by
  ext output input
  simp only [secondGram,cross,gradientGram,Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,Finset.sum_apply,
    inner_sum,sum_inner,Finset.sum_add_distrib,smul_eq_mul,Finset.mul_sum]

theorem heat_pairing (viscosity : ℝ) (value : Fin 3 → H) (gradient second : Fin 3 → Fin 3 → H) :
    pairing (-gram value) (-viscosity • cross value (∑ direction : Fin 3, second direction)) =
      viscosity*pairing (gram value) (secondGram value gradient second)-
        2*viscosity*Matrix.trace (gram value*gradientGram gradient) := by
  rw [secondGram_split,← pairing_gradient_trace]
  simp only [pairing,Matrix.neg_apply,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowStressHeatGram
