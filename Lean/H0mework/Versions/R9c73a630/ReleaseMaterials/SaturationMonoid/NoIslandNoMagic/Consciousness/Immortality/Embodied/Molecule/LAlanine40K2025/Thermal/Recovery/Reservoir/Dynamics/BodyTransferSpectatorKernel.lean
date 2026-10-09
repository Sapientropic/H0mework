import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BodyTransferHermitianKernel
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.RetainedBodyLift
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.ExchangeComparison

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel

open Collision
open scoped Matrix
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def slice (rho : Matrix (ι × κ) (ι × κ) ℂ) (e f : κ) : SystemMatrix ι :=
  rho.submatrix (fun i => (i, e)) (fun j => (j, f))

omit [DecidableEq ι] in
theorem left_tensor_mul (A : SystemMatrix ι) (rho : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι × κ) :
    ((Matrix.kronecker A (1 : Matrix κ κ ℂ)) * rho) i j =
      ∑ a, A i.1 a * rho (a, i.2) j := by
  simp [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

omit [DecidableEq ι] in
theorem mul_left_tensor (A : SystemMatrix ι) (rho : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι × κ) :
    (rho * Matrix.kronecker A (1 : Matrix κ κ ℂ)) i j =
      ∑ a, rho i (a, j.2) * A a j.1 := by
  simp [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem slice_local_conjugation (U : Matrix.unitaryGroup ι ℂ)
    (rho : Matrix (ι × κ) (ι × κ) ℂ) (e f : κ) :
    slice (Load.Quantum.localConjugation U (1 : Matrix.unitaryGroup κ ℂ) rho) e f =
      Quantum.conjugation U (slice rho e f) := by
  ext i j
  change (((Matrix.kronecker (U : SystemMatrix ι) (1 : Matrix κ κ ℂ)) * rho *
    star (Matrix.kronecker (U : SystemMatrix ι) (1 : Matrix κ κ ℂ))) (i, e) (j, f)) =
    (((U : SystemMatrix ι) * slice rho e f * star (U : SystemMatrix ι)) i j)
  rw [Matrix.star_eq_conjTranspose]
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  change (((Matrix.kronecker (U : SystemMatrix ι) (1 : Matrix κ κ ℂ)) * rho *
    Matrix.kronecker (U : SystemMatrix ι)ᴴ (1 : Matrix κ κ ℂ)) (i, e) (j, f)) = _
  rw [mul_left_tensor]
  conv_rhs => rw [Matrix.mul_apply]
  simp only [Matrix.star_eq_conjTranspose]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact left_tensor_mul (U : SystemMatrix ι) rho (i, e) (a, f)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem received_slice (rho : Matrix (ι × κ) (ι × κ) ℂ) (tau : SystemMatrix ι) (e f : κ) :
    slice (Incidence.receivedJoint rho tau) e f = Matrix.kronecker (slice rho e f) tau := rfl

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem bodyRead_slice (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) (e f : κ) :
    slice (Incidence.bodyRead joint) e f = Collision.systemReduce (slice joint e f) := rfl

def bodyExchange (rho : Matrix (ι × κ) (ι × κ) ℂ) (tau : SystemMatrix ι) (angle : ℝ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  Incidence.bodyRead (Load.Quantum.localConjugation (Exchange.exchangeUnitary angle)
    (1 : Matrix.unitaryGroup κ ℂ) (Incidence.receivedJoint rho tau))

theorem bodyExchange_slice (rho : Matrix (ι × κ) (ι × κ) ℂ) (tau : SystemMatrix ι) (angle : ℝ) (e f : κ) :
    slice (bodyExchange rho tau angle) e f =
      systemNext (slice rho e f) tau (Real.cos angle) (Real.sin angle) := by
  rw [bodyExchange, bodyRead_slice, slice_local_conjugation, received_slice]
  rfl

theorem bodyExchange_injective (tau : SystemMatrix ι) (hermitian : tau.IsHermitian)
    (normalized : tau.trace = 1) (angle : ℝ) (nonzero : Real.cos angle ≠ 0) :
    Function.Injective (fun rho : Matrix (ι × κ) (ι × κ) ℂ => bodyExchange rho tau angle) := by
  intro left right same
  ext i j
  have read := congrArg (fun M => slice M i.2 j.2) same
  rw [bodyExchange_slice, bodyExchange_slice] at read
  have input := systemNext_hermitian_injective tau hermitian normalized (Real.cos angle) (Real.sin angle)
    (Real.cos_sq_add_sin_sq angle) nonzero read
  exact congrArg (fun M : SystemMatrix ι => M i.1 j.1) input

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
