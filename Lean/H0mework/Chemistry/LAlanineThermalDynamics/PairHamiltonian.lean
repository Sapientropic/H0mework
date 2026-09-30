import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapEnergyPopulation
import H0mework.Quantum.Generator.P257
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # The retained pair's Hamiltonian generates its own real-time unitary flow -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Dynamics

open _root_.SaturationMonoid.AffineRelaxation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

abbrev PairSpace (ι : Type*) := EuclideanSpace ℂ (ι × ι)
abbrev PairOperator (ι : Type*) [Fintype ι] := PairSpace ι →L[ℂ] PairSpace ι

def pairMatrixOperatorEquiv : JointMatrix ι ≃⋆ₐ[ℂ] PairOperator ι :=
  Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ)

def freePairH (H : SystemMatrix ι) : JointMatrix ι := jointHamiltonian H

def pairH (H : SystemMatrix ι) (g : ℝ) : JointMatrix ι :=
  freePairH H + (g : ℂ) • swapOperator

omit [Fintype ι] in
theorem freePairH_hermitian (H : SystemMatrix ι) (hH : H.IsHermitian) :
    (freePairH H).IsHermitian := by
  change (freePairH H)ᴴ = freePairH H
  unfold freePairH jointHamiltonian
  rw [Matrix.conjTranspose_add]
  simp only [Matrix.kronecker]
  have left := Matrix.conjTranspose_kronecker H (1 : SystemMatrix ι)
  have right := Matrix.conjTranspose_kronecker (1 : SystemMatrix ι) H
  rw [left, right, hH.eq, Matrix.conjTranspose_one]

omit [Fintype ι] in
theorem pairH_hermitian (H : SystemMatrix ι) (hH : H.IsHermitian) (g : ℝ) :
    (pairH H g).IsHermitian := by
  change (pairH H g)ᴴ = pairH H g
  simp [pairH, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    (freePairH_hermitian H hH).eq, swap_adjoint]

theorem freePairH_commute_swap (H : SystemMatrix ι) :
    Commute (freePairH H) (swapOperator : JointMatrix ι) := by
  show freePairH H * swapOperator = swapOperator * freePairH H
  exact (swap_jointHamiltonian_commutes H).symm

theorem freePairH_commute_pairH (H : SystemMatrix ι) (g : ℝ) :
    Commute (freePairH H) (pairH H g) :=
  (Commute.refl _).add_right ((freePairH_commute_swap H).smul_right (g : ℂ))

theorem swap_commute_pairH (H : SystemMatrix ι) (g : ℝ) :
    Commute (swapOperator : JointMatrix ι) (pairH H g) :=
  (freePairH_commute_swap H).symm.add_right ((Commute.refl _).smul_right (g : ℂ))

theorem interaction_commute_pairH (H : SystemMatrix ι) (g : ℝ) :
    Commute ((g : ℂ) • swapOperator) (pairH H g) :=
  (swap_commute_pairH H g).smul_left (g : ℂ)

def pairHamiltonianOperator (H : SystemMatrix ι) (g : ℝ) : PairOperator ι :=
  pairMatrixOperatorEquiv (pairH H g)

theorem pairHamiltonianOperator_selfAdjoint (H : SystemMatrix ι) (hH : H.IsHermitian) (g : ℝ) :
    IsSelfAdjoint (pairHamiltonianOperator H g) :=
  (pairH_hermitian H hH g).isSelfAdjoint.map pairMatrixOperatorEquiv

/-- P257 is the producer: no unitary, trajectory or target enters this mouth. -/
theorem pairSchrodingerFlow (H : SystemMatrix ι) (hH : H.IsHermitian) (g : ℝ) :
    BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate
      (PairSpace ι) (pairHamiltonianOperator H g) :=
  boundedSelfAdjointHamiltonianSchrodingerFlowCertificate
    (pairHamiltonianOperator H g) (pairHamiltonianOperator_selfAdjoint H hH g)

def pairPropagator (H : SystemMatrix ι) (g time : ℝ) : PairOperator ι :=
  NormedSpace.exp ((time : ℂ) • (-Complex.I • pairHamiltonianOperator H g))

theorem pairPropagator_eq_realExp (H : SystemMatrix ι) (g time : ℝ) :
    pairPropagator H g time =
      NormedSpace.exp (time • (-(Complex.I • pairHamiltonianOperator H g))) := by
  unfold pairPropagator
  congr 1
  ext state i
  simp [Complex.real_smul]

@[simp] theorem pairPropagator_zero (H : SystemMatrix ι) (hH : H.IsHermitian) (g : ℝ) :
    pairPropagator H g 0 = 1 := (pairSchrodingerFlow H hH g).exponential_group.zero_slice

theorem pairPropagator_unitary (H : SystemMatrix ι) (hH : H.IsHermitian) (g time : ℝ) :
    pairPropagator H g time ∈ unitary (PairOperator ι) :=
  (pairSchrodingerFlow H hH g).exponential_group.unitarySlice time

theorem pairPropagator_add (H : SystemMatrix ι) (hH : H.IsHermitian) (g time next : ℝ) :
    pairPropagator H g (time + next) = pairPropagator H g time * pairPropagator H g next :=
  (pairSchrodingerFlow H hH g).exponential_group.addSlice time next

theorem pairPropagator_mul_neg (H : SystemMatrix ι) (hH : H.IsHermitian) (g time : ℝ) :
    pairPropagator H g time * pairPropagator H g (-time) = 1 := by
  rw [← pairPropagator_add H hH, add_neg_cancel, pairPropagator_zero H hH]

theorem pairPropagator_neg_mul (H : SystemMatrix ι) (hH : H.IsHermitian) (g time : ℝ) :
    pairPropagator H g (-time) * pairPropagator H g time = 1 := by
  rw [← pairPropagator_add H hH, neg_add_cancel, pairPropagator_zero H hH]

theorem pairPropagator_neg_eq_star (H : SystemMatrix ι) (hH : H.IsHermitian) (g time : ℝ) :
    pairPropagator H g (-time) = star (pairPropagator H g time) :=
  left_inv_eq_right_inv (pairPropagator_neg_mul H hH g time)
    (Unitary.mul_star_self_of_mem (pairPropagator_unitary H hH g time))

theorem pairPropagator_preserves_norm (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (state : PairSpace ι) :
    ‖pairPropagator H g time state‖ = ‖state‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (pairPropagator_unitary H hH g time) state

theorem pairPropagator_hasDerivAt (H : SystemMatrix ι) (hH : H.IsHermitian) (g time : ℝ) :
    HasDerivAt (pairPropagator H g)
      ((-(Complex.I • pairHamiltonianOperator H g)) * pairPropagator H g time) time := by
  change HasDerivAt (fun t : ℝ => pairPropagator H g t) _ time
  simpa only [pairPropagator_eq_realExp] using!
    (pairSchrodingerFlow H hH g).schrodinger_equation.operator_derivative time

theorem pairOrbit_hasDerivAt (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (state : PairSpace ι) :
    HasDerivAt (fun t => pairPropagator H g t state)
      ((-(Complex.I • pairHamiltonianOperator H g)) (pairPropagator H g time state)) time := by
  simpa only [pairPropagator_eq_realExp] using!
    (pairSchrodingerFlow H hH g).orbitDerivative time state

def pairPropagatorMatrix (H : SystemMatrix ι) (g time : ℝ) : JointMatrix ι :=
  pairMatrixOperatorEquiv.symm (pairPropagator H g time)

theorem pairPropagatorMatrix_unitary (H : SystemMatrix ι) (hH : H.IsHermitian) (g time : ℝ) :
    pairPropagatorMatrix H g time ∈ Matrix.unitaryGroup (ι × ι) ℂ :=
  Unitary.map_mem (pairMatrixOperatorEquiv (ι := ι)).symm (pairPropagator_unitary H hH g time)

def pairUnitary (H : SystemMatrix ι) (hH : H.IsHermitian) (g time : ℝ) :
    Matrix.unitaryGroup (ι × ι) ℂ :=
  ⟨pairPropagatorMatrix H g time, pairPropagatorMatrix_unitary H hH g time⟩

theorem pairPropagatorMatrix_neg_eq_star (H : SystemMatrix ι) (hH : H.IsHermitian) (g time : ℝ) :
    pairPropagatorMatrix H g (-time) = star (pairPropagatorMatrix H g time) := by
  unfold pairPropagatorMatrix
  rw [pairPropagator_neg_eq_star H hH]
  exact map_star (pairMatrixOperatorEquiv (ι := ι)).symm (pairPropagator H g time)

end

end LAlanine40K2025.Thermal.Dynamics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
