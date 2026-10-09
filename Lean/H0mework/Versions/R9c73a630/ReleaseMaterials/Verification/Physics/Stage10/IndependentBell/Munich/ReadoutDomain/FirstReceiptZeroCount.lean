import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

set_option autoImplicit false

namespace BellFirstReceiptZeroCount

def hit (perp parallel : Bool) : ℝ := if perp && parallel then 1 else 0
def absent (seen : Bool) : ℝ := if seen then 0 else 1

theorem event_identity (perp parallel : Bool) :
    hit perp parallel = 1-absent perp-absent parallel+absent perp*absent parallel := by
  cases perp <;> cases parallel <;> norm_num [hit,absent]

theorem complete_mass_identity (mass : Bool → Bool → ℝ) :
    (∑ a, ∑ b, mass a b*hit a b) =
      (∑ a, ∑ b, mass a b) - (∑ a, ∑ b, mass a b*absent a) -
        (∑ a, ∑ b, mass a b*absent b) + (∑ a, ∑ b, mass a b*absent a*absent b) := by
  simp [hit,absent]
  ring

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] in
theorem same_source_tensor_left (k u : Matrix a a ℂ) (v : Matrix b b ℂ) :
    Matrix.kronecker (k*u) v = Matrix.kronecker k (1 : Matrix b b ℂ) * Matrix.kronecker u v := by
  simpa only [Matrix.kronecker,Matrix.one_mul] using
    (Matrix.mul_kronecker_mul k u (1 : Matrix b b ℂ) v)

omit [DecidableEq b] in
theorem same_source_tensor_right (u : Matrix a a ℂ) (k v : Matrix b b ℂ) :
    Matrix.kronecker u (k*v) = Matrix.kronecker (1 : Matrix a a ℂ) k * Matrix.kronecker u v := by
  simpa only [Matrix.kronecker,Matrix.one_mul] using
    (Matrix.mul_kronecker_mul (1 : Matrix a a ℂ) u k v)

omit [DecidableEq a] in
theorem physical_adjoint_readout (d e : Matrix a a ℂ) :
    (d*e*d.conjTranspose).conjTranspose = d*e.conjTranspose*d.conjTranspose := by
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]

theorem complete_readout_price (m a b c M A B C em ea eb ec : ℝ)
    (hm : |m-M| ≤ em) (ha : |a-A| ≤ ea) (hb : |b-B| ≤ eb) (hc : |c-C| ≤ ec) :
    |(m-a-b+c)-(M-A-B+C)| ≤ em+ea+eb+ec := by
  have h₁ := abs_add_le (m-M) (-(a-A))
  have h₂ := abs_add_le ((m-M)-(a-A)) (-(b-B))
  have h₃ := abs_add_le ((m-M)-(a-A)-(b-B)) (c-C)
  simp only [abs_neg,← sub_eq_add_neg] at h₁ h₂
  calc
    |(m-a-b+c)-(M-A-B+C)| = |(m-M)-(a-A)-(b-B)+(c-C)| := by congr 1;ring
    _ ≤ em+ea+eb+ec := by linarith

end BellFirstReceiptZeroCount
