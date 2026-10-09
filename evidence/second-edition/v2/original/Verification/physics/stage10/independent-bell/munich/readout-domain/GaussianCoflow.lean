import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

set_option autoImplicit false

namespace BellGaussianCoflow

theorem right_action_transpose {n : Type*} [Fintype n] (B K : Matrix n n ℂ) :
    (B*K).transpose = K.transpose*B.transpose := Matrix.transpose_mul B K

theorem transpose_loss_identity {n : Type*} (K R : Matrix n n ℂ)
    (h : K+K.conjTranspose+R=0) :
    K.transpose+K.transpose.conjTranspose+R.transpose=0 := by
  ext i j
  have hi := congrArg (fun m : Matrix n n ℂ => m j i) h
  simpa only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.zero_apply] using hi

theorem reflected_gaussian_square (b u c : ℝ) :
    (b-u-c)^2 = (u-(b-c))^2 := by ring

theorem diagonal_frame_preserves_loss {n : Type*} [DecidableEq n]
    (K R : Matrix n n ℂ) (omega : n → ℝ) (h : K+K.conjTranspose+R=0) :
    let D := Matrix.diagonal (fun i => Complex.I*(omega i : ℂ))
    (K+D)+(K+D).conjTranspose+R=0 := by
  dsimp only
  have hd : (Matrix.diagonal (fun i => Complex.I*(omega i : ℂ))).conjTranspose =
      -Matrix.diagonal (fun i => Complex.I*(omega i : ℂ)) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.neg_apply]
    by_cases hij : i=j
    · subst j; simp
    · simp [hij, Ne.symm hij]
  rw [Matrix.conjTranspose_add, hd]
  calc
    K + Matrix.diagonal (fun i => Complex.I*(omega i : ℂ)) +
        (K.conjTranspose - Matrix.diagonal (fun i => Complex.I*(omega i : ℂ))) + R =
        K+K.conjTranspose+R := by abel
    _ = 0 := h

end BellGaussianCoflow
