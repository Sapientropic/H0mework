import H0mework.Physics.Dirac.DiracMatterHermitianEnergy
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Local energy identity for the Stage-9 Dirac matter system

This module proves the finite-carrier Green symmetry of every Hermitian Dirac
coefficient and the exact derivative of the corresponding variable energy.
The latter separates the doubled field-derivative term from the coefficient
derivative term, which is the local algebra consumed by symmetric-hyperbolic
energy estimates.

No spatial integral, residual, candidate solution, or existence certificate is
accepted or generated here.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracMatterHermitianEnergyIdentity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageNineDiracMatterHermitianEnergy
open SU7ExteriorMatterRepresentation
open scoped ComplexOrder Matrix

noncomputable section

theorem diracExteriorMatterCoordinatePairing_action_general
    (matrix : DiracMatrix)
    (first second : DiracExteriorMatterCarrier) :
    diracExteriorMatterCoordinatePairing first
        (diracMatrixMatterAction matrix second) =
      ∑ internal : InternalMatterCoordinateIndex,
        star (fun spin => internalMatterCoordinate internal (first spin)) ⬝ᵥ
          (matrix *ᵥ
            (fun spin => internalMatterCoordinate internal (second spin))) := by
  unfold diracExteriorMatterCoordinatePairing
  apply Finset.sum_congr rfl
  intro internal _
  congr 1
  funext row
  exact internalMatterCoordinate_diracMatrixMatterAction
    matrix second row internal

private theorem star_dotProduct_mulVec_eq
    (matrix : DiracMatrix)
    (hermitian : Matrix.IsHermitian matrix)
    (first second : DiracSpinorIndex → ℂ) :
    star (star first ⬝ᵥ (matrix *ᵥ second)) =
      star second ⬝ᵥ (matrix *ᵥ first) := by
  rw [Matrix.star_dotProduct]
  simp only [star_star, Matrix.star_mulVec, hermitian.eq]
  rw [Matrix.dotProduct_mulVec]

/-- Green symmetry of a Hermitian Dirac coefficient on the full carrier. -/
theorem diracExteriorMatterCoordinatePairing_action_star
    (matrix : DiracMatrix)
    (hermitian : Matrix.IsHermitian matrix)
    (first second : DiracExteriorMatterCarrier) :
    star (diracExteriorMatterCoordinatePairing first
      (diracMatrixMatterAction matrix second)) =
      diracExteriorMatterCoordinatePairing second
        (diracMatrixMatterAction matrix first) := by
  rw [diracExteriorMatterCoordinatePairing_action_general,
    diracExteriorMatterCoordinatePairing_action_general]
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro internal _
  exact star_dotProduct_mulVec_eq matrix hermitian _ _

private def diracMatrixEuclideanCLM
    (matrix : DiracMatrix) :
    EuclideanSpace ℂ DiracSpinorIndex →L[ℂ]
      EuclideanSpace ℂ DiracSpinorIndex :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin matrix)

@[simp] private theorem diracMatrixEuclideanCLM_apply
    (matrix : DiracMatrix)
    (field : DiracSpinorIndex → ℂ) :
    diracMatrixEuclideanCLM matrix (WithLp.toLp 2 field) =
      WithLp.toLp 2 (matrix *ᵥ field) :=
  rfl

private def internalMatterDiracCoordinate
    (internal : InternalMatterCoordinateIndex)
    (field : DiracExteriorMatterCarrier) :
    EuclideanSpace ℂ DiracSpinorIndex :=
  WithLp.toLp 2
    (fun spin => internalMatterCoordinate internal (field spin))

private theorem internalMatterDiracCoordinate_hasDerivAt
    (internal : InternalMatterCoordinateIndex)
    (field : ℝ → DiracExteriorMatterCarrier)
    (fieldDerivative : DiracExteriorMatterCarrier)
    (time : ℝ)
    (coordinateDerivative :
      ∀ spin : DiracSpinorIndex,
        HasDerivAt
          (fun candidateTime =>
            internalMatterCoordinate internal (field candidateTime spin))
          (internalMatterCoordinate internal (fieldDerivative spin))
          time) :
    HasDerivAt
      (fun candidateTime =>
        internalMatterDiracCoordinate internal (field candidateTime))
      (internalMatterDiracCoordinate internal fieldDerivative)
      time := by
  have rawDerivative :
      HasDerivAt
        (fun candidateTime spin =>
          internalMatterCoordinate internal (field candidateTime spin))
        (fun spin =>
          internalMatterCoordinate internal (fieldDerivative spin))
        time :=
    hasDerivAt_pi.mpr coordinateDerivative
  let toLpCLM :
      (DiracSpinorIndex → ℂ) →L[ℝ]
        EuclideanSpace ℂ DiracSpinorIndex :=
    (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : DiracSpinorIndex => ℂ)).symm.toContinuousLinearMap.restrictScalars ℝ
  exact toLpCLM.hasFDerivAt.comp_hasDerivAt time rawDerivative

private theorem diracSpinorHermitianVariableEnergy_hasDerivAt
    (matrix : DiracMatrix)
    (hermitian : Matrix.IsHermitian matrix)
    (field actedField : ℝ → EuclideanSpace ℂ DiracSpinorIndex)
    (fieldDerivative coefficientDerivative :
      EuclideanSpace ℂ DiracSpinorIndex)
    (time : ℝ)
    (actedAt :
      actedField time = diracMatrixEuclideanCLM matrix (field time))
    (fieldHasDerivAt : HasDerivAt field fieldDerivative time)
    (actedFieldHasDerivAt :
      HasDerivAt actedField
        (diracMatrixEuclideanCLM matrix fieldDerivative +
          coefficientDerivative)
        time) :
    HasDerivAt
      (fun candidateTime =>
        Complex.re (inner ℂ (field candidateTime)
          (actedField candidateTime)))
      (2 * Complex.re
          (inner ℂ (field time)
            (diracMatrixEuclideanCLM matrix fieldDerivative)) +
        Complex.re (inner ℂ (field time) coefficientDerivative))
      time := by
  let action := diracMatrixEuclideanCLM matrix
  have pairingDerivative :=
    fieldHasDerivAt.inner ℂ actedFieldHasDerivAt
  have realDerivative :
      HasDerivAt
        (fun candidateTime =>
          Complex.re (inner ℂ (field candidateTime)
            (actedField candidateTime)))
        (Complex.re
          (inner ℂ (field time)
              (action fieldDerivative + coefficientDerivative) +
            inner ℂ fieldDerivative (actedField time)))
        time := by
    have result :=
      (hasDerivAt_const (x := time) Complex.reCLM).clm_apply
        pairingDerivative
    simpa only [zero_apply, zero_add, Complex.reCLM_apply] using result
  have symmetric :
      (Matrix.toEuclideanLin matrix).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hermitian
  have symmetricAction :
      (action : EuclideanSpace ℂ DiracSpinorIndex →ₗ[ℂ]
        EuclideanSpace ℂ DiracSpinorIndex).IsSymmetric := by
    exact symmetric
  have crossTerm :
      Complex.re (inner ℂ fieldDerivative (actedField time)) =
        Complex.re (inner ℂ (field time) (action fieldDerivative)) := by
    rw [actedAt]
    change
      Complex.re (inner ℂ fieldDerivative (action (field time))) =
        Complex.re (inner ℂ (field time) (action fieldDerivative))
    calc
      Complex.re (inner ℂ fieldDerivative (action (field time))) =
          Complex.re (inner ℂ (action fieldDerivative) (field time)) := by
        exact congrArg Complex.re
          (symmetricAction fieldDerivative (field time)).symm
      _ = Complex.re (inner ℂ (field time) (action fieldDerivative)) :=
        by simpa using
          (inner_re_symm (𝕜 := ℂ)
            (action fieldDerivative) (field time))
  have derivativeEq :
      Complex.re
          (inner ℂ (field time)
              (action fieldDerivative + coefficientDerivative) +
            inner ℂ fieldDerivative (actedField time)) =
        2 * Complex.re (inner ℂ (field time) (action fieldDerivative)) +
          Complex.re (inner ℂ (field time) coefficientDerivative) := by
    rw [inner_add_right, Complex.add_re, Complex.add_re, crossTerm]
    ring
  rw [derivativeEq] at realDerivative
  simpa [action] using realDerivative

/-- Exact local energy identity for a time-varying Hermitian coefficient.

`actedField` is the coefficient applied to `field`.  Its derivative is split
as the same coefficient applied to `fieldDerivative`, plus the supplied
`coefficientDerivative` contribution.  Both derivative receipts are stated
coordinatewise on the original finite matter carrier. -/
theorem diracExteriorMatterHermitianVariableEnergy_hasDerivAt
    (matrix : DiracMatrix)
    (hermitian : Matrix.IsHermitian matrix)
    (field actedField : ℝ → DiracExteriorMatterCarrier)
    (fieldDerivative coefficientDerivative : DiracExteriorMatterCarrier)
    (time : ℝ)
    (actedAt :
      actedField time = diracMatrixMatterAction matrix (field time))
    (fieldCoordinateDerivative :
      ∀ (internal : InternalMatterCoordinateIndex)
        (spin : DiracSpinorIndex),
        HasDerivAt
          (fun candidateTime =>
            internalMatterCoordinate internal (field candidateTime spin))
          (internalMatterCoordinate internal (fieldDerivative spin))
          time)
    (actedFieldCoordinateDerivative :
      ∀ (internal : InternalMatterCoordinateIndex)
        (spin : DiracSpinorIndex),
        HasDerivAt
          (fun candidateTime =>
            internalMatterCoordinate internal
              (actedField candidateTime spin))
          (internalMatterCoordinate internal
            ((diracMatrixMatterAction matrix fieldDerivative +
              coefficientDerivative) spin))
          time) :
    HasDerivAt
      (fun candidateTime =>
        Complex.re
          (diracExteriorMatterCoordinatePairing
            (field candidateTime) (actedField candidateTime)))
      (2 * Complex.re
          (diracExteriorMatterCoordinatePairing (field time)
            (diracMatrixMatterAction matrix fieldDerivative)) +
        Complex.re
          (diracExteriorMatterCoordinatePairing
            (field time) coefficientDerivative))
      time := by
  have actedCoordinateAt
      (internal : InternalMatterCoordinateIndex) :
      internalMatterDiracCoordinate internal (actedField time) =
        diracMatrixEuclideanCLM matrix
          (internalMatterDiracCoordinate internal (field time)) := by
    rw [actedAt]
    unfold internalMatterDiracCoordinate
    rw [diracMatrixEuclideanCLM_apply]
    apply WithLp.ofLp_injective
    funext spin
    exact internalMatterCoordinate_diracMatrixMatterAction
      matrix (field time) spin internal
  have actedDerivativeCoordinate
      (internal : InternalMatterCoordinateIndex) :
      internalMatterDiracCoordinate internal
          (diracMatrixMatterAction matrix fieldDerivative +
            coefficientDerivative) =
        diracMatrixEuclideanCLM matrix
            (internalMatterDiracCoordinate internal fieldDerivative) +
          internalMatterDiracCoordinate internal coefficientDerivative := by
    unfold internalMatterDiracCoordinate
    rw [diracMatrixEuclideanCLM_apply]
    apply WithLp.ofLp_injective
    funext spin
    simp [internalMatterCoordinate_diracMatrixMatterAction,
      Matrix.mulVec, dotProduct]
  have coordinateDerivative :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun internal candidateTime =>
        Complex.re
          (inner ℂ
            (internalMatterDiracCoordinate internal (field candidateTime))
            (internalMatterDiracCoordinate internal
              (actedField candidateTime))))
      (A' := fun internal =>
        2 * Complex.re
            (inner ℂ
              (internalMatterDiracCoordinate internal (field time))
              (diracMatrixEuclideanCLM matrix
                (internalMatterDiracCoordinate internal fieldDerivative))) +
          Complex.re
            (inner ℂ
              (internalMatterDiracCoordinate internal (field time))
              (internalMatterDiracCoordinate internal
                coefficientDerivative)))
      (x := time)
      (fun internal _ =>
        diracSpinorHermitianVariableEnergy_hasDerivAt
          matrix hermitian
          (fun candidateTime =>
            internalMatterDiracCoordinate internal (field candidateTime))
          (fun candidateTime =>
            internalMatterDiracCoordinate internal
              (actedField candidateTime))
          (internalMatterDiracCoordinate internal fieldDerivative)
          (internalMatterDiracCoordinate internal coefficientDerivative)
          time (actedCoordinateAt internal)
          (internalMatterDiracCoordinate_hasDerivAt internal field
            fieldDerivative time (fieldCoordinateDerivative internal))
          (by
            have derivative :=
              internalMatterDiracCoordinate_hasDerivAt internal actedField
                (diracMatrixMatterAction matrix fieldDerivative +
                  coefficientDerivative)
                time (actedFieldCoordinateDerivative internal)
            rw [actedDerivativeCoordinate internal] at derivative
            exact derivative))
  have functionEq :
      (fun candidateTime =>
        Complex.re
          (diracExteriorMatterCoordinatePairing
            (field candidateTime) (actedField candidateTime))) =
        fun candidateTime =>
          ∑ internal : InternalMatterCoordinateIndex,
            Complex.re
              (inner ℂ
                (internalMatterDiracCoordinate internal
                  (field candidateTime))
                (internalMatterDiracCoordinate internal
                  (actedField candidateTime))) := by
    funext candidateTime
    rw [diracExteriorMatterCoordinatePairing, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro internal _
    simp [internalMatterDiracCoordinate,
      EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [functionEq]
  have derivativeValueEq :
      (∑ internal : InternalMatterCoordinateIndex,
        (2 * Complex.re
            (inner ℂ
              (internalMatterDiracCoordinate internal (field time))
              (diracMatrixEuclideanCLM matrix
                (internalMatterDiracCoordinate internal fieldDerivative))) +
          Complex.re
            (inner ℂ
              (internalMatterDiracCoordinate internal (field time))
              (internalMatterDiracCoordinate internal
                coefficientDerivative)))) =
        2 * Complex.re
            (diracExteriorMatterCoordinatePairing (field time)
              (diracMatrixMatterAction matrix fieldDerivative)) +
          Complex.re
            (diracExteriorMatterCoordinatePairing
              (field time) coefficientDerivative) := by
    rw [Finset.sum_add_distrib,
      diracExteriorMatterCoordinatePairing_action_general,
      diracExteriorMatterCoordinatePairing,
      Complex.re_sum, Complex.re_sum, Finset.mul_sum]
    congr 1 <;>
      apply Finset.sum_congr rfl <;>
      intro internal _ <;>
      simp [internalMatterDiracCoordinate,
        EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [← derivativeValueEq]
  exact coordinateDerivative

/-- Product rule for the real part of the finite matter pairing.  This is the
bilinear calculus mouth used by Green transport: the first field and the
already acted second field may vary independently. -/
theorem diracExteriorMatterCoordinatePairing_re_hasDerivAt
    (first second : ℝ → DiracExteriorMatterCarrier)
    (firstDerivative secondDerivative : DiracExteriorMatterCarrier)
    (time : ℝ)
    (firstCoordinateDerivative :
      ∀ (internal : InternalMatterCoordinateIndex)
        (spin : DiracSpinorIndex),
        HasDerivAt
          (fun candidateTime ↦
            internalMatterCoordinate internal (first candidateTime spin))
          (internalMatterCoordinate internal (firstDerivative spin))
          time)
    (secondCoordinateDerivative :
      ∀ (internal : InternalMatterCoordinateIndex)
        (spin : DiracSpinorIndex),
        HasDerivAt
          (fun candidateTime ↦
            internalMatterCoordinate internal (second candidateTime spin))
          (internalMatterCoordinate internal (secondDerivative spin))
          time) :
    HasDerivAt
      (fun candidateTime ↦
        Complex.re
          (diracExteriorMatterCoordinatePairing
            (first candidateTime) (second candidateTime)))
      (Complex.re
          (diracExteriorMatterCoordinatePairing
            firstDerivative (second time)) +
        Complex.re
          (diracExteriorMatterCoordinatePairing
            (first time) secondDerivative))
      time := by
  have coordinateDerivative :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun internal candidateTime ↦
        Complex.re
          (inner ℂ
            (internalMatterDiracCoordinate internal (first candidateTime))
            (internalMatterDiracCoordinate internal (second candidateTime))))
      (A' := fun internal ↦
        Complex.re
          (inner ℂ
              (internalMatterDiracCoordinate internal (first time))
              (internalMatterDiracCoordinate internal secondDerivative) +
            inner ℂ
              (internalMatterDiracCoordinate internal firstDerivative)
              (internalMatterDiracCoordinate internal (second time))))
      (x := time)
      (fun internal _ ↦ by
        have pairingDerivative :=
          (internalMatterDiracCoordinate_hasDerivAt internal first
              firstDerivative time (firstCoordinateDerivative internal)).inner ℂ
            (internalMatterDiracCoordinate_hasDerivAt internal second
              secondDerivative time (secondCoordinateDerivative internal))
        have realDerivative :=
          (hasDerivAt_const (x := time) Complex.reCLM).clm_apply
            pairingDerivative
        simpa only [zero_apply, zero_add, Complex.reCLM_apply] using
          realDerivative)
  have functionEq :
      (fun candidateTime ↦
        Complex.re
          (diracExteriorMatterCoordinatePairing
            (first candidateTime) (second candidateTime))) =
        fun candidateTime ↦
          ∑ internal : InternalMatterCoordinateIndex,
            Complex.re
              (inner ℂ
                (internalMatterDiracCoordinate internal
                  (first candidateTime))
                (internalMatterDiracCoordinate internal
                  (second candidateTime))) := by
    funext candidateTime
    rw [diracExteriorMatterCoordinatePairing, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro internal _
    simp [internalMatterDiracCoordinate,
      EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [functionEq]
  have derivativeValueEq :
      (∑ internal : InternalMatterCoordinateIndex,
        Complex.re
          (inner ℂ
              (internalMatterDiracCoordinate internal (first time))
              (internalMatterDiracCoordinate internal secondDerivative) +
            inner ℂ
              (internalMatterDiracCoordinate internal firstDerivative)
              (internalMatterDiracCoordinate internal (second time)))) =
        Complex.re
            (diracExteriorMatterCoordinatePairing
              firstDerivative (second time)) +
          Complex.re
            (diracExteriorMatterCoordinatePairing
              (first time) secondDerivative) := by
    have firstSum :
        (∑ internal : InternalMatterCoordinateIndex,
          Complex.re
            (inner ℂ
              (internalMatterDiracCoordinate internal (first time))
              (internalMatterDiracCoordinate internal secondDerivative))) =
          Complex.re
            (diracExteriorMatterCoordinatePairing
              (first time) secondDerivative) := by
      rw [diracExteriorMatterCoordinatePairing, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro internal _
      simp [internalMatterDiracCoordinate,
        EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    have secondSum :
        (∑ internal : InternalMatterCoordinateIndex,
          Complex.re
            (inner ℂ
              (internalMatterDiracCoordinate internal firstDerivative)
              (internalMatterDiracCoordinate internal (second time)))) =
          Complex.re
            (diracExteriorMatterCoordinatePairing
              firstDerivative (second time)) := by
      rw [diracExteriorMatterCoordinatePairing, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro internal _
      simp [internalMatterDiracCoordinate,
        EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    simp_rw [Complex.add_re]
    rw [Finset.sum_add_distrib, firstSum, secondSum]
    ring
  rw [← derivativeValueEq]
  exact coordinateDerivative

end

end SaturationMonoid.PhysicsCore.StageNineDiracMatterHermitianEnergyIdentity
