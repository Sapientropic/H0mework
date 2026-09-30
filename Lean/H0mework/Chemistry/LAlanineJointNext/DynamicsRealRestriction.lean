import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.RealRestriction

open scoped Matrix
variable {ι : Type*}

def realPart (D : Matrix ι ι ℂ) : Matrix ι ι ℝ := D.map Complex.re
def complexify (A : Matrix ι ι ℝ) : Matrix ι ι ℂ := A.map Complex.ofReal

theorem realPart_symmetric (D : Matrix ι ι ℂ) (hermitian : D.IsHermitian) :
    (realPart D).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simpa [realPart] using congrArg Complex.re (hermitian.apply i j)

theorem complexify_hermitian (A : Matrix ι ι ℝ) (symmetric : A.IsSymm) :
    (complexify A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [complexify, symmetric.apply i j]

def rankOne (v : ι → ℝ) : Matrix ι ι ℝ := Matrix.vecMulVec v v
def rankOneDerivative (v dv : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.vecMulVec dv v + Matrix.vecMulVec v dv

theorem rankOne_symmetric (v : ι → ℝ) : (rankOne v).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [rankOne, Matrix.vecMulVec_apply, mul_comm]

theorem rankOneDerivative_symmetric (v dv : ι → ℝ) : (rankOneDerivative v dv).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [rankOneDerivative, Matrix.vecMulVec_apply, mul_comm, add_comm]

variable [Fintype ι]

theorem rankOne_hasDerivAt (v : ℝ → ι → ℝ) (dv : ι → ℝ) (time : ℝ)
    (derivative : ∀ i, HasDerivAt (fun t => v t i) (dv i) time) :
    HasDerivAt (fun t => rankOne (v t)) (rankOneDerivative (v time) dv) time := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  convert (derivative i).mul (derivative j) using 1 <;> rfl

theorem realPart_mul_left (A : Matrix ι ι ℝ) (D : Matrix ι ι ℂ) :
    realPart (complexify A * D) = A * realPart D := by
  ext i j
  simp [realPart, complexify, Matrix.mul_apply, Complex.re_sum, Complex.mul_re]

theorem realPart_trace (D : Matrix ι ι ℂ) : D.trace.re = (realPart D).trace := by
  simp [realPart, Matrix.trace, Complex.re_sum]

/-- Every real linear operator has this restriction; symmetry is not needed for the equality. -/
theorem scalar_trace_restriction (A : Matrix ι ι ℝ) (D : Matrix ι ι ℂ) :
    (complexify A * D).trace.re = (A * realPart D).trace := by
  rw [realPart_trace, realPart_mul_left]

theorem ao_density_restriction (v : ι → ℝ) (D : Matrix ι ι ℂ) :
    (complexify (rankOne v) * D).trace.re = (rankOne v * realPart D).trace :=
  scalar_trace_restriction _ _

theorem ao_spatial_derivative_restriction (v dv : ι → ℝ) (D : Matrix ι ι ℂ) :
    (complexify (rankOneDerivative v dv) * D).trace.re = (rankOneDerivative v dv * realPart D).trace :=
  scalar_trace_restriction _ _

theorem rankOne_density_entries (v : ι → ℝ) (D : Matrix ι ι ℝ) :
    (rankOne v * D).trace = ∑ i, ∑ j, v i * D i j * v j := by
  simp only [rankOne, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end LAlanine40K2025.JointNext.RealRestriction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
