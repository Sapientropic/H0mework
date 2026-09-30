import H0mework.Physics.LowEnergy.FullQuantum.TriangularResolvent
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots

/-! The original exterior grading controls complete traces and determinants. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineHolonomicField
open scoped Matrix
noncomputable section
local instance : DecidableEq Quantum.Index := Classical.decEq _

def sixIndex (i : Quantum.Index) : Bool :=
  match i.2 with
  | Sum.inl _ => true
  | Sum.inr _ => false

theorem six_coordinates (v : DiracExteriorMatterCarrier) (i : Quantum.Index) :
    Quantum.coordinates (MixedSymbol.degreeSix v) i =
      if sixIndex i then Quantum.coordinates v i else 0 := by
  rcases i with ⟨spin, index⟩
  rcases index with index | index
  · simp [sixIndex, Quantum.coordinates, Quantum.wholeBasis, Quantum.internalBasis,
      Module.Basis.equivFun_apply, Pi.basis_repr, MixedSymbol.degreeSix]
  · rcases index with index | index <;>
      simp [sixIndex, Quantum.coordinates, Quantum.wholeBasis, Quantum.internalBasis,
        Module.Basis.equivFun_apply, Pi.basis_repr, MixedSymbol.degreeSix]

theorem six_matrix : Quantum.operatorMatrix MixedSymbol.degreeSix =
    Matrix.diagonal (fun i : Quantum.Index => if sixIndex i then (1 : ℂ) else 0) := by
  ext i j
  rw [Quantum.operatorMatrix, LinearMap.toMatrixAlgEquiv_apply]
  change Quantum.wholeBasis.repr (MixedSymbol.degreeSix (Quantum.wholeBasis j)) i = _
  change Quantum.coordinates (MixedSymbol.degreeSix (Quantum.wholeBasis j)) i = _
  rw [six_coordinates]
  by_cases equal : i=j
  · subst j
    simp [Quantum.coordinates]
  · simp [Quantum.coordinates, equal, Ne.symm equal]

theorem matrix_mul (A B : Mother) :
    Quantum.operatorMatrix (A*B) = Quantum.operatorMatrix A * Quantum.operatorMatrix B :=
  Quantum.matrix_composition A B

theorem source_matrix_commute (A : Mother) (preserves : Commute MixedSymbol.degreeSix A) :
    Commute (Quantum.operatorMatrix MixedSymbol.degreeSix) (Quantum.operatorMatrix A) := by
  have generated := congrArg Quantum.operatorMatrix preserves.eq
  rw [matrix_mul, matrix_mul] at generated
  exact generated

theorem source_off_diagonal (A : Mother) (preserves : Commute MixedSymbol.degreeSix A)
    (i j : Quantum.Index) (outside : sixIndex i=false) (inside : sixIndex j=true) :
    Quantum.operatorMatrix A i j = 0 := by
  have entry := congrArg (fun M : Matrix Quantum.Index Quantum.Index ℂ => M i j)
    (source_matrix_commute A preserves).eq
  rw [six_matrix] at entry
  simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, outside, inside] using entry.symm

theorem interaction_outside_row (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (i j : Quantum.Index) (outside : sixIndex i=false) :
    Quantum.operatorMatrix (interactionHamiltonian C p) i j = 0 := by
  have equality : Quantum.operatorMatrix MixedSymbol.degreeSix *
      Quantum.operatorMatrix (interactionHamiltonian C p) =
      Quantum.operatorMatrix (interactionHamiltonian C p) := by
    rw [← matrix_mul, six_interactionHamiltonian]
  have entry := congrArg (fun M : Matrix Quantum.Index Quantum.Index ℂ => M i j) equality
  rw [six_matrix] at entry
  simpa [Matrix.diagonal_mul, outside] using entry.symm

theorem interaction_inside_column (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (i j : Quantum.Index) (inside : sixIndex j=true) :
    Quantum.operatorMatrix (interactionHamiltonian C p) i j = 0 := by
  have equality : Quantum.operatorMatrix (interactionHamiltonian C p) *
      Quantum.operatorMatrix MixedSymbol.degreeSix = 0 := by
    rw [← matrix_mul, interactionHamiltonian_six]
    exact Quantum.operatorMatrix.map_zero
  have entry := congrArg (fun M : Matrix Quantum.Index Quantum.Index ℂ => M i j) equality
  rw [six_matrix] at entry
  simpa [Matrix.mul_diagonal, inside] using entry

theorem closed_source_trace (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (R : Mother) (preserves : Commute MixedSymbol.degreeSix R) :
    Matrix.trace (Quantum.operatorMatrix (interactionHamiltonian C p * R)) = 0 := by
  have output : MixedSymbol.degreeSix * (interactionHamiltonian C p * R) =
      interactionHamiltonian C p * R := by rw [← mul_assoc, six_interactionHamiltonian]
  have input : (interactionHamiltonian C p * R) * MixedSymbol.degreeSix = 0 := by
    rw [mul_assoc, ← preserves.eq, ← mul_assoc, interactionHamiltonian_six, zero_mul]
  calc
    _ = Matrix.trace (Quantum.operatorMatrix
        (MixedSymbol.degreeSix * (interactionHamiltonian C p * R))) := by rw [output]
    _ = Matrix.trace (Quantum.operatorMatrix MixedSymbol.degreeSix *
        Quantum.operatorMatrix (interactionHamiltonian C p * R)) := by rw [matrix_mul]
    _ = Matrix.trace (Quantum.operatorMatrix (interactionHamiltonian C p * R) *
        Quantum.operatorMatrix MixedSymbol.degreeSix) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Quantum.operatorMatrix ((interactionHamiltonian C p * R) *
        MixedSymbol.degreeSix)) := congrArg Matrix.trace (matrix_mul _ _).symm
    _ = 0 := by
      have zero : Quantum.operatorMatrix (0 : Mother) = 0 := Quantum.operatorMatrix.map_zero
      rw [input, zero, Matrix.trace_zero]

theorem determinant_independent_yukawa (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (A : Mother) (preserves : Commute MixedSymbol.degreeSix A) (c : ℂ) :
    Matrix.det (Quantum.operatorMatrix A + c • Quantum.operatorMatrix (interactionHamiltonian C p)) =
      Matrix.det (Quantum.operatorMatrix A) := by
  classical
  let M := Quantum.operatorMatrix A
  let N := Quantum.operatorMatrix (interactionHamiltonian C p)
  let isSix : Quantum.Index → Prop := fun i => sixIndex i=true
  have outside (i : Quantum.Index) (h : ¬isSix i) : sixIndex i=false := by
    cases e : sixIndex i <;> simp_all [isSix]
  have diagonal : ∀ i, ¬isSix i → ∀ j, isSix j → M i j=0 := by
    intro i hi j hj
    exact source_off_diagonal A preserves i j (outside i hi) hj
  have whole : ∀ i, ¬isSix i → ∀ j, isSix j → (M+c • N) i j=0 := by
    intro i hi j hj
    change M i j+c*N i j=0
    rw [diagonal i hi j hj, show N i j=0 from interaction_outside_row C p i j (outside i hi)]
    simp
  have upper : Matrix.toSquareBlockProp (M+c • N) isSix = Matrix.toSquareBlockProp M isSix := by
    ext i j
    change M i.1 j.1+c*N i.1 j.1=M i.1 j.1
    rw [show N i.1 j.1=0 from interaction_inside_column C p i.1 j.1 j.property]
    simp
  have lower : Matrix.toSquareBlockProp (M+c • N) (fun i => ¬isSix i) =
      Matrix.toSquareBlockProp M (fun i => ¬isSix i) := by
    ext i j
    change M i.1 j.1+c*N i.1 j.1=M i.1 j.1
    rw [show N i.1 j.1=0 from interaction_outside_row C p i.1 j.1 (outside i.1 i.property)]
    simp
  change Matrix.det (M+c • N)=Matrix.det M
  rw [Matrix.twoBlockTriangular_det (M+c • N) isSix whole,
    Matrix.twoBlockTriangular_det M isSix diagonal, upper, lower]

theorem characteristic_determinant (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) :
    Matrix.det (Quantum.operatorMatrix (fullKernel C p k z)) =
      Matrix.det (Quantum.operatorMatrix (freeKernel C p k z)) := by
  have generated := determinant_independent_yukawa C p (freeKernel C p k z)
    (grade_freeKernel 0 C p k z) (-1)
  have equality : Quantum.operatorMatrix (fullKernel C p k z) =
      Quantum.operatorMatrix (freeKernel C p k z) +
        (-1 : ℂ) • Quantum.operatorMatrix (interactionHamiltonian C p) := by
    rw [kernel_split]
    have sub : Quantum.operatorMatrix (freeKernel C p k z-interactionHamiltonian C p) =
        Quantum.operatorMatrix (freeKernel C p k z)-Quantum.operatorMatrix (interactionHamiltonian C p) :=
      Quantum.operatorMatrix.map_sub (freeKernel C p k z) (interactionHamiltonian C p)
    rw [sub, neg_one_smul, sub_eq_add_neg]
  rw [equality]
  exact generated

theorem closed_resolvent_trace (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) (regular : IsUnit (freeKernel C p k z)) :
    Matrix.trace (Quantum.operatorMatrix
      (interactionHamiltonian C p * freeResolvent C p k z)) = 0 :=
  closed_source_trace C p _ (grade_freeResolvent 0 C p k z regular)

theorem matrix_shift (A : Mother) (z : ℂ) :
    Quantum.operatorMatrix (z • 1-A) =
      Matrix.scalar Quantum.Index z-Quantum.operatorMatrix A := by
  have subtract : Quantum.operatorMatrix (z • 1-A) =
      Quantum.operatorMatrix (z • 1)-Quantum.operatorMatrix A := Quantum.operatorMatrix.map_sub (z • 1) A
  have scale : Quantum.operatorMatrix (z • (1 : Mother)) =
      z • Quantum.operatorMatrix (1 : Mother) := Quantum.operatorMatrix.toLinearEquiv.map_smul z 1
  have one : Quantum.operatorMatrix (1 : Mother) = 1 := Quantum.operatorMatrix.map_one
  rw [subtract, scale, one]
  congr 1
  ext i j
  by_cases same : i=j <;> simp [Matrix.scalar_apply, same]

theorem characteristic_polynomial (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) :
    (Quantum.operatorMatrix (hamiltonian C p k)).charpoly =
      (Quantum.operatorMatrix (freeHamiltonian C p k)).charpoly := by
  apply Polynomial.funext
  intro z
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, ← matrix_shift, ← matrix_shift]
  exact characteristic_determinant C p k z

theorem free_regular_energy_exists (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : ∃ z : ℂ, IsUnit (freeKernel C p k z) := by
  classical
  by_contra! absent
  have allRoots (z : ℂ) : (Quantum.operatorMatrix (freeHamiltonian C p k)).charpoly.eval z=0 := by
    by_contra nonzero
    have determinant : (Quantum.operatorMatrix (freeKernel C p k z)).det ≠ 0 := by
      simpa only [freeKernel, matrix_shift, ← Matrix.eval_charpoly] using nonzero
    have matrixUnit : IsUnit (Quantum.operatorMatrix (freeKernel C p k z)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr determinant)
    have sourceUnit := matrixUnit.map Quantum.operatorMatrix.symm.toMonoidHom
    apply absent z
    change IsUnit (Quantum.operatorMatrix.symm (Quantum.operatorMatrix (freeKernel C p k z))) at sourceUnit
    rwa [AlgEquiv.symm_apply_apply] at sourceUnit
  have vanished : (Quantum.operatorMatrix (freeHamiltonian C p k)).charpoly=0 :=
    Polynomial.funext (fun z => by simpa using allRoots z)
  exact (Matrix.charpoly_monic _).ne_zero vanished

theorem matrix_isUnit_iff (A : Mother) : IsUnit (Quantum.operatorMatrix A) ↔ IsUnit A := by
  constructor
  · intro matrixUnit
    have sourceUnit := matrixUnit.map Quantum.operatorMatrix.symm.toMonoidHom
    change IsUnit (Quantum.operatorMatrix.symm (Quantum.operatorMatrix A)) at sourceUnit
    rwa [AlgEquiv.symm_apply_apply] at sourceUnit
  · intro sourceUnit
    exact sourceUnit.map Quantum.operatorMatrix.toMonoidHom

theorem full_regular_iff_free (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) :
    IsUnit (fullKernel C p k z) ↔ IsUnit (freeKernel C p k z) := by
  rw [← matrix_isUnit_iff, ← matrix_isUnit_iff, Matrix.isUnit_iff_isUnit_det,
    Matrix.isUnit_iff_isUnit_det, characteristic_determinant]

theorem full_resolvent_trace (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) (regular : IsUnit (freeKernel C p k z)) :
    Matrix.trace (Quantum.operatorMatrix (fullResolvent C p k z)) =
      Matrix.trace (Quantum.operatorMatrix (freeResolvent C p k z)) := by
  let R := freeResolvent C p k z
  let N := interactionHamiltonian C p
  have add : Quantum.operatorMatrix (fullResolvent C p k z) =
      Quantum.operatorMatrix R+Quantum.operatorMatrix (R*N*R) :=
    Quantum.operatorMatrix.map_add R (R*N*R)
  have cyclic : Matrix.trace (Quantum.operatorMatrix (R*N*R)) =
      Matrix.trace (Quantum.operatorMatrix (N*(R*R))) := by
    have value := Matrix.trace_mul_comm (Quantum.operatorMatrix R) (Quantum.operatorMatrix (N*R))
    rw [← matrix_mul, ← matrix_mul] at value
    simpa only [mul_assoc] using value
  have preserves := grade_freeResolvent 0 C p k z regular
  have closed := closed_source_trace C p (R*R) (preserves.mul_right preserves)
  rw [add, Matrix.trace_add, cyclic, closed, add_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
