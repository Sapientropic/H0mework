import H0mework.Physics.GaugeSpectrum.Spectral
import H0mework.Quantum.Generator.P257
import Mathlib.Analysis.Matrix.Hermitian

/-! The actual fluctuation vectors generate every finite positive Gram
kernel. The bounded generator is extracted from the original temporal
phases, not from a classical action-gradient update. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF
open scoped ComplexOrder

noncomputable section

theorem vectorEvaluation_product (vector : Source.Index → ℂ) (first second : State.Observable) :
    State.vectorEvaluation vector (star first * second) =
      star (first *ᵥ vector) ⬝ᵥ (second *ᵥ vector) := by
  change star vector ⬝ᵥ ((star first * second) *ᵥ vector) = _
  rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.star_eq_conjTranspose]

def fluctuation (point displacement : BasePoint) (axis : Fin 3) : EuclideanSpace ℂ Source.Index :=
  WithLp.toLp 2 (evolvedDualCurvature point displacement axis *ᵥ Source.vector point)

theorem fluctuation_inner (point first second : BasePoint) (axis : Fin 3) :
    inner ℂ (fluctuation point first axis) (fluctuation point second axis) =
      connected point (evolvedDualCurvature point first axis)
        (evolvedDualCurvature point second axis) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [connected, evolvedDualCurvature_mean, star_zero, mul_zero, sub_zero]
  rw [dotProduct_comm]
  exact (vectorEvaluation_product (Source.vector point)
    (evolvedDualCurvature point first axis) (evolvedDualCurvature point second axis)).symm

def correlationMatrix {ι : Type*} [Fintype ι] (point : BasePoint)
    (samples : ι → BasePoint) (axis : Fin 3) : Matrix ι ι ℂ :=
  fun first second => connected point (evolvedDualCurvature point (samples first) axis)
    (evolvedDualCurvature point (samples second) axis)

theorem correlationMatrix_posSemidef {ι : Type*} [Fintype ι] (point : BasePoint)
    (samples : ι → BasePoint) (axis : Fin 3) :
    (correlationMatrix point samples axis).PosSemidef := by
  let features : Matrix Source.Index ι ℂ := fun coordinate sample =>
    fluctuation point (samples sample) axis coordinate
  have gram : correlationMatrix point samples axis = featuresᴴ * features := by
    ext first second
    rw [correlationMatrix, ← fluctuation_inner, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm]
    rfl
  rw [gram]
  exact Matrix.posSemidef_conjTranspose_mul_self features

def phaseHamiltonian : State.Observable := diagonal (fun index => -(Dynamics.rate index : ℂ))

def phaseHamiltonianOperator :
    EuclideanSpace ℂ Source.Index →L[ℂ] EuclideanSpace ℂ Source.Index :=
  phaseHamiltonian.toEuclideanLin.toContinuousLinearMap

theorem phaseHamiltonian_hermitian : phaseHamiltonian.IsHermitian := by
  change (diagonal _)ᴴ = _
  simp [phaseHamiltonian]

theorem phaseHamiltonian_selfAdjoint : IsSelfAdjoint phaseHamiltonianOperator := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr phaseHamiltonian_hermitian

theorem phaseHamiltonian_flow :
    AffineRelaxation.BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate
      (EuclideanSpace ℂ Source.Index) phaseHamiltonianOperator :=
  AffineRelaxation.boundedSelfAdjointHamiltonianSchrodingerFlowCertificate
    phaseHamiltonianOperator phaseHamiltonian_selfAdjoint

theorem actual_vector_schrodinger (point : BasePoint) (time : ℝ) :
    HasDerivAt (fun t : ℝ => Source.vector (point + Dynamics.timeDisplacement t))
      (fun index => -Complex.I *
        (phaseHamiltonian *ᵥ Source.vector (point + Dynamics.timeDisplacement time)) index) time := by
  convert Dynamics.vector_time_hasDerivAt point time using 1
  funext index
  simp [phaseHamiltonian, Matrix.mulVec_diagonal, Dynamics.generator]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
