import H0mework.Physics.Dirac.DiracKineticSpinJurisdiction

/-!
# Local Spin covariance of the generated Dirac connection lift

This module starts from the finite Stage-7 Spin action and the actual
homogeneous part of the primitive local connection write.  It proves that
Lorentz skewness is preserved and identifies the transformed Dirac lift with
conjugation by the same generated Dirac matrix.

No transformed connection, derivative, Maurer matrix, lift, or covariance
certificate is accepted as an independent input.  The inhomogeneous
derivative-generated leg and the complete covariant derivative are kept for
the next checkpoint.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracKineticLocalSpinLiftCovariance

open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineDiracKineticSpinJurisdiction
open StageNineGlobalBundle
open StageNineLorentzCoverAndSpinDescent
open StageNinePhysicalBivectorSpinRepresentation
open StageNineSpinMatterBundle

open scoped MatrixGroups

noncomputable section

set_option autoImplicit false

/-- Homogeneous part of the existing Weyl-dual Lorentz connection action,
stated on the dependency-light pointwise carrier. -/
def spinWeylDualHomogeneousLorentzConnection
    (groupElement : SpinPlus13)
    (connection : PointwiseLorentzSpinConnection) :
    PointwiseLorentzSpinConnection :=
  fun direction internalOut internalIn =>
    let lorentz := spinLorentzMatrix (spinWeylDual groupElement)
    (lorentz * spinConnectionMatrix connection direction * lorentz⁻¹)
      internalOut internalIn

@[simp] theorem spinConnectionMatrix_spinWeylDualHomogeneous
    (groupElement : SpinPlus13)
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) :
    spinConnectionMatrix
        (spinWeylDualHomogeneousLorentzConnection groupElement connection)
        direction =
      spinLorentzMatrix (spinWeylDual groupElement) *
          spinConnectionMatrix connection direction *
        (spinLorentzMatrix (spinWeylDual groupElement))⁻¹ :=
  rfl

private theorem minkowskiInternalMetric_sq :
    minkowskiInternalMetric * minkowskiInternalMetric =
      (1 : LorentzianMetric) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [minkowskiInternalMetric]

private theorem minkowskiInternalMetric_transpose :
    minkowskiInternalMetric.transpose = minkowskiInternalMetric := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.transpose_apply, minkowskiInternalMetric]

/-- The inverse of the Weyl-dual Lorentz matrix is the transpose of the
original Lorentz matrix. -/
theorem spinLorentzMatrix_spinWeylDual_nonsingInv
    (groupElement : SpinPlus13) :
    (spinLorentzMatrix (spinWeylDual groupElement))⁻¹ =
      (spinLorentzMatrix groupElement).transpose := by
  rw [spinLorentzMatrix_nonsingInv]
  simpa using spinLorentzMatrix_spinWeylDual groupElement⁻¹

/-- Lowering the output index of the Weyl-dual matrix gives the original
Lorentz matrix on the lowered index.  This is the finite variance seam used
by the connection lift. -/
theorem minkowskiInternalMetric_mul_spinLorentzMatrix_spinWeylDual
    (groupElement : SpinPlus13) :
    minkowskiInternalMetric *
        spinLorentzMatrix (spinWeylDual groupElement) =
      spinLorentzMatrix groupElement * minkowskiInternalMetric := by
  let dualLorentz := spinLorentzMatrix (spinWeylDual groupElement)
  have inverseFormula :=
    spinLorentzMatrix_nonsingInv_minkowski (spinWeylDual groupElement)
  have inverseTranspose :
      dualLorentz⁻¹.transpose =
        minkowskiInternalMetric * dualLorentz *
          minkowskiInternalMetric := by
    change
      (spinLorentzMatrix (spinWeylDual groupElement))⁻¹.transpose = _
    rw [inverseFormula, Matrix.transpose_mul, Matrix.transpose_mul,
      minkowskiInternalMetric_transpose]
    simp [dualLorentz, Matrix.mul_assoc]
  have inverseTransposeOriginal :
      dualLorentz⁻¹.transpose = spinLorentzMatrix groupElement := by
    rw [show dualLorentz⁻¹ =
        (spinLorentzMatrix groupElement).transpose by
      exact spinLorentzMatrix_spinWeylDual_nonsingInv groupElement]
    simp
  rw [inverseTranspose] at inverseTransposeOriginal
  calc
    minkowskiInternalMetric * dualLorentz =
        (minkowskiInternalMetric * dualLorentz *
          minkowskiInternalMetric) * minkowskiInternalMetric := by
      rw [Matrix.mul_assoc, minkowskiInternalMetric_sq]
      simp
    _ = spinLorentzMatrix groupElement * minkowskiInternalMetric := by
      rw [inverseTransposeOriginal]

/-- The lowered connection matrix follows the actual exterior-square action
of the original Lorentz matrix. -/
theorem spinWeylDualHomogeneous_loweredConnectionMatrix
    (groupElement : SpinPlus13)
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) :
    minkowskiInternalMetric *
        spinConnectionMatrix
          (spinWeylDualHomogeneousLorentzConnection groupElement connection)
          direction =
      spinLorentzMatrix groupElement *
          (minkowskiInternalMetric *
            spinConnectionMatrix connection direction) *
        (spinLorentzMatrix groupElement).transpose := by
  rw [spinConnectionMatrix_spinWeylDualHomogeneous]
  calc
    minkowskiInternalMetric *
          (spinLorentzMatrix (spinWeylDual groupElement) *
              spinConnectionMatrix connection direction *
            (spinLorentzMatrix (spinWeylDual groupElement))⁻¹) =
        (minkowskiInternalMetric *
            spinLorentzMatrix (spinWeylDual groupElement)) *
          spinConnectionMatrix connection direction *
            (spinLorentzMatrix (spinWeylDual groupElement))⁻¹ := by
      noncomm_ring
    _ = (spinLorentzMatrix groupElement * minkowskiInternalMetric) *
          spinConnectionMatrix connection direction *
            (spinLorentzMatrix groupElement).transpose := by
      rw [minkowskiInternalMetric_mul_spinLorentzMatrix_spinWeylDual,
        spinLorentzMatrix_spinWeylDual_nonsingInv]
    _ = _ := by noncomm_ring

/-- Homogeneous Weyl-dual transport preserves the actual `so(1,3)` domain.
The premise is necessary because the raw connection carrier itself does not
store Lorentz skewness. -/
theorem spinWeylDualHomogeneousLorentzConnection_lorentzSkew
    (groupElement : SpinPlus13)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection) :
    LorentzSkew
      (spinWeylDualHomogeneousLorentzConnection groupElement connection) := by
  intro direction
  let lorentz := spinLorentzMatrix groupElement
  let connectionMatrix := spinConnectionMatrix connection direction
  let transformedMatrix := spinConnectionMatrix
    (spinWeylDualHomogeneousLorentzConnection groupElement connection)
    direction
  have loweredSkew :
      (minkowskiInternalMetric * connectionMatrix).transpose +
          minkowskiInternalMetric * connectionMatrix = 0 := by
    rw [Matrix.transpose_mul, minkowskiInternalMetric_transpose]
    exact connectionSkew direction
  have loweredTransport :
      minkowskiInternalMetric * transformedMatrix =
        lorentz * (minkowskiInternalMetric * connectionMatrix) *
          lorentz.transpose := by
    exact spinWeylDualHomogeneous_loweredConnectionMatrix
      groupElement connection direction
  have transformedLoweredSkew :
      (minkowskiInternalMetric * transformedMatrix).transpose +
          minkowskiInternalMetric * transformedMatrix = 0 := by
    rw [loweredTransport, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    calc
      lorentz *
            ((minkowskiInternalMetric * connectionMatrix).transpose *
              lorentz.transpose) +
          lorentz * (minkowskiInternalMetric * connectionMatrix) *
            lorentz.transpose =
        lorentz *
            ((minkowskiInternalMetric * connectionMatrix).transpose +
              minkowskiInternalMetric * connectionMatrix) *
          lorentz.transpose := by noncomm_ring
      _ = 0 := by rw [loweredSkew]; simp
  simpa [transformedMatrix, Matrix.transpose_mul,
    minkowskiInternalMetric_transpose] using transformedLoweredSkew

/-! ## Ordered Clifford lift -/

/-- Dependency-light ordered Clifford lift of a lowered internal two-tensor.
The Lorentz-skew connection producer supplies the antisymmetric instances
used below. -/
def diracOrderedBivectorLift (lowered : LorentzianMetric) : DiracMatrix :=
  ∑ first : LorentzianIndex, ∑ second : LorentzianIndex,
    ((4 : ℂ)⁻¹ * (lowered first second : ℂ)) •
      (diracGamma first * diracGamma second)

theorem minkowskiInternalMetric_mul_spinConnectionMatrix_apply
    (connection : PointwiseLorentzSpinConnection)
    (direction first second : LorentzianIndex) :
    (minkowskiInternalMetric * spinConnectionMatrix connection direction)
        first second =
      minkowskiInternalSign first *
        connection direction first second := by
  fin_cases first <;>
    simp [Matrix.mul_apply, minkowskiInternalMetric, Fin.sum_univ_four,
      spinConnectionMatrix]

/-- On the actual Lorentz-skew domain, the six-coordinate lift is exactly
the ordered Clifford lift of the lowered connection matrix. -/
theorem diracSpinConnectionLift_eq_diracOrderedBivectorLift
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection)
    (direction : LorentzianIndex) :
    diracSpinConnectionLift connection direction =
      diracOrderedBivectorLift
        (minkowskiInternalMetric *
          spinConnectionMatrix connection direction) := by
  rw [diracSpinConnectionLift_eq_ordered_sum
    connection connectionSkew direction]
  unfold diracOrderedBivectorLift
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [minkowskiInternalMetric_mul_spinConnectionMatrix_apply]

/-- Conjugating a Clifford product by the actual finite Dirac matrix applies
the generated Lorentz matrix to both internal indices. -/
theorem spinDiracMatrix_diracGamma_mul_covariant
    (groupElement : SpinPlus13)
    (first second : LorentzianIndex) :
    spinDiracMatrix groupElement *
          (diracGamma first * diracGamma second) *
        spinDiracMatrix groupElement⁻¹ =
      ∑ outputFirst : LorentzianIndex,
        ∑ outputSecond : LorentzianIndex,
          ((spinLorentzMatrix groupElement outputFirst first : ℂ) *
              (spinLorentzMatrix groupElement outputSecond second : ℂ)) •
            (diracGamma outputFirst * diracGamma outputSecond) := by
  have inverseProduct :
      spinDiracMatrix groupElement⁻¹ * spinDiracMatrix groupElement =
        (1 : DiracMatrix) := by
    rw [← spinDiracMatrix_mul]
    simp
  calc
    spinDiracMatrix groupElement *
          (diracGamma first * diracGamma second) *
        spinDiracMatrix groupElement⁻¹ =
      (spinDiracMatrix groupElement * diracGamma first *
          spinDiracMatrix groupElement⁻¹) *
        (spinDiracMatrix groupElement * diracGamma second *
          spinDiracMatrix groupElement⁻¹) := by
      calc
        spinDiracMatrix groupElement *
              (diracGamma first * diracGamma second) *
            spinDiracMatrix groupElement⁻¹ =
          spinDiracMatrix groupElement * diracGamma first *
              (1 : DiracMatrix) * diracGamma second *
            spinDiracMatrix groupElement⁻¹ := by
          simp
          noncomm_ring
        _ = spinDiracMatrix groupElement * diracGamma first *
              (spinDiracMatrix groupElement⁻¹ *
                spinDiracMatrix groupElement) *
              diracGamma second * spinDiracMatrix groupElement⁻¹ := by
          rw [inverseProduct]
        _ = _ := by noncomm_ring
    _ = (∑ outputFirst : LorentzianIndex,
          (spinLorentzMatrix groupElement outputFirst first : ℂ) •
            diracGamma outputFirst) *
        (∑ outputSecond : LorentzianIndex,
          (spinLorentzMatrix groupElement outputSecond second : ℂ) •
            diracGamma outputSecond) := by
      rw [spinDiracMatrix_diracGamma_covariant,
        spinDiracMatrix_diracGamma_covariant]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro outputFirst _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro outputSecond _
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      exact mul_comm _ _

/-- The ordered Clifford lift intertwines the actual finite Lorentz and Dirac
representations.  The lowered tensor is transformed on both indices; no
equivariance receipt is supplied. -/
theorem diracOrderedBivectorLift_spin_covariant
    (groupElement : SpinPlus13) (lowered : LorentzianMetric) :
    diracOrderedBivectorLift
        (spinLorentzMatrix groupElement * lowered *
          (spinLorentzMatrix groupElement).transpose) =
      spinDiracMatrix groupElement * diracOrderedBivectorLift lowered *
        spinDiracMatrix groupElement⁻¹ := by
  symm
  calc
    spinDiracMatrix groupElement * diracOrderedBivectorLift lowered *
          spinDiracMatrix groupElement⁻¹ =
      ∑ first : LorentzianIndex, ∑ second : LorentzianIndex,
        ((4 : ℂ)⁻¹ * (lowered first second : ℂ)) •
          (spinDiracMatrix groupElement *
              (diracGamma first * diracGamma second) *
            spinDiracMatrix groupElement⁻¹) := by
      unfold diracOrderedBivectorLift
      simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
        Matrix.smul_mul]
    _ = ∑ first : LorentzianIndex, ∑ second : LorentzianIndex,
        ((4 : ℂ)⁻¹ * (lowered first second : ℂ)) •
          (∑ outputFirst : LorentzianIndex,
            ∑ outputSecond : LorentzianIndex,
              ((spinLorentzMatrix groupElement outputFirst first : ℂ) *
                  (spinLorentzMatrix groupElement outputSecond second : ℂ)) •
                (diracGamma outputFirst *
                  diracGamma outputSecond)) := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      rw [spinDiracMatrix_diracGamma_mul_covariant]
    _ = diracOrderedBivectorLift
        (spinLorentzMatrix groupElement * lowered *
          (spinLorentzMatrix groupElement).transpose) := by
      ext row column
      simp [diracOrderedBivectorLift, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_four]
      ring

/-- Finite homogeneous local-Spin covariance of the actual generated Dirac
connection lift.  The same `groupElement` determines the Weyl-dual Lorentz
write and the Dirac conjugation. -/
theorem diracSpinConnectionLift_spinWeylDualHomogeneous_covariant
    (groupElement : SpinPlus13)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection)
    (direction : LorentzianIndex) :
    diracSpinConnectionLift
        (spinWeylDualHomogeneousLorentzConnection groupElement connection)
        direction =
      spinDiracMatrix groupElement *
          diracSpinConnectionLift connection direction *
        spinDiracMatrix groupElement⁻¹ := by
  rw [diracSpinConnectionLift_eq_diracOrderedBivectorLift connection
      connectionSkew direction,
    diracSpinConnectionLift_eq_diracOrderedBivectorLift
      (spinWeylDualHomogeneousLorentzConnection groupElement connection)
      (spinWeylDualHomogeneousLorentzConnection_lorentzSkew
        groupElement connection connectionSkew) direction,
    spinWeylDualHomogeneous_loweredConnectionMatrix,
    diracOrderedBivectorLift_spin_covariant]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracKineticLocalSpinLiftCovariance
