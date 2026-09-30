import H0mework.Physics.Dirac.DiracMatterCoordinateCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# First-order Dirac matter coordinate commutator

Differentiating an actual finite-dimensional first-order operator preserves
its principal action on the differentiated field and exposes exactly the
coefficient changed-read.  No solution, residual, or target is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineMatterCoordinateFirstOrderCommutator

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-! ## First-order coordinate commutator -/

abbrev MatterRealEnd :=
  MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier

/-- A fixed-current first-order matter operator written entirely on the
finite coordinate carrier. -/
def matterCoordinateFirstOrderOperator
    (principal : LorentzianIndex → BasePoint → MatterRealEnd)
    (lower : BasePoint → MatterRealEnd)
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : MatterCoordinateCarrier :=
  (∑ direction : LorentzianIndex,
      principal direction point
        (fieldDirectionalDerivative field point direction)) +
    lower point (field point)

private theorem directionalDerivativeField_contDiff_one
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ 2 field)
    (direction : LorentzianIndex) :
    ContDiff ℝ 1
      (fun point => fieldDirectionalDerivative field point direction) := by
  unfold fieldDirectionalDerivative
  exact
    (fieldSmooth.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const

private theorem directionalDerivativeField_commute
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ 2 field)
    (point : BasePoint)
    (first second : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          fieldDirectionalDerivative field candidate first)
        point second =
      fieldDirectionalDerivative
        (fun candidate =>
          fieldDirectionalDerivative field candidate second)
        point first := by
  unfold fieldDirectionalDerivative
  have derivativeDifferentiable : DifferentiableAt ℝ (fderiv ℝ field) point :=
    ((fieldSmooth.fderiv_right (m := 1) (by norm_num)).differentiable
      one_ne_zero).differentiableAt
  rw [fderiv_clm_apply derivativeDifferentiable
      (differentiableAt_const (c := coordinateDirection first)),
    fderiv_clm_apply derivativeDifferentiable
      (differentiableAt_const (c := coordinateDirection second))]
  simp only [fderiv_const_apply, zero_apply, map_zero, zero_add,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact (fieldSmooth.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
    (coordinateDirection second) (coordinateDirection first)

private theorem directionalDerivative_clm_apply
    (coefficient : BasePoint → MatterRealEnd)
    (field : BasePoint → MatterCoordinateCarrier)
    (coefficientSmooth : ContDiff ℝ 1 coefficient)
    (fieldSmooth : ContDiff ℝ 1 field)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => coefficient candidate (field candidate))
        point direction =
      (fieldDirectionalDerivative coefficient point direction) (field point) +
        coefficient point
          (fieldDirectionalDerivative field point direction) := by
  unfold fieldDirectionalDerivative
  rw [fderiv_clm_apply
    ((coefficientSmooth.differentiable one_ne_zero).differentiableAt)
    ((fieldSmooth.differentiable one_ne_zero).differentiableAt)]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

private theorem directionalDerivative_add
    (first second : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (firstDifferentiable : DifferentiableAt ℝ first point)
    (secondDifferentiable : DifferentiableAt ℝ second point)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate =>
        first candidate + second candidate) point direction =
      fieldDirectionalDerivative first point direction +
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  simp only [add_apply]

private theorem directionalDerivative_univ_sum
    (terms : LorentzianIndex → BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (termsDifferentiable : ∀ index, DifferentiableAt ℝ (terms index) point)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => ∑ index : LorentzianIndex, terms index candidate)
        point direction =
      ∑ index : LorentzianIndex,
        fieldDirectionalDerivative (terms index) point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sum (u := Finset.univ)
    (fun index _ => termsDifferentiable index)]
  rfl

/-- Differentiating the principal part commutes the field derivative and
exposes exactly the coefficient changed-read. -/
theorem matterCoordinatePrincipalSum_directionalDerivative
    (principal : LorentzianIndex → BasePoint → MatterRealEnd)
    (field : BasePoint → MatterCoordinateCarrier)
    (principalSmooth : ∀ direction, ContDiff ℝ 1 (principal direction))
    (fieldSmooth : ContDiff ℝ 2 field)
    (point : BasePoint)
    (commutedDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => ∑ direction : LorentzianIndex,
          principal direction candidate
            (fieldDirectionalDerivative field candidate direction))
        point commutedDirection =
      (∑ direction : LorentzianIndex,
        principal direction point
          (fieldDirectionalDerivative
            (fun candidate =>
              fieldDirectionalDerivative field candidate commutedDirection)
            point direction)) +
        ∑ direction : LorentzianIndex,
          (fieldDirectionalDerivative (principal direction) point
              commutedDirection)
            (fieldDirectionalDerivative field point direction) := by
  have derivativeFieldSmooth (direction : LorentzianIndex) :
      ContDiff ℝ 1
        (fun candidate =>
          fieldDirectionalDerivative field candidate direction) :=
    directionalDerivativeField_contDiff_one field fieldSmooth direction
  have termDifferentiable (direction : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun candidate => principal direction candidate
          (fieldDirectionalDerivative field candidate direction)) point :=
    (((principalSmooth direction).differentiable one_ne_zero).differentiableAt
      ).clm_apply
      (((derivativeFieldSmooth direction).differentiable one_ne_zero
        ).differentiableAt)
  have termDerivative (direction : LorentzianIndex) :=
    directionalDerivative_clm_apply
      (principal direction)
      (fun candidate =>
        fieldDirectionalDerivative field candidate direction)
      (principalSmooth direction) (derivativeFieldSmooth direction)
      point commutedDirection
  calc
    _ = ∑ direction : LorentzianIndex,
        fieldDirectionalDerivative
          (fun candidate => principal direction candidate
            (fieldDirectionalDerivative field candidate direction))
          point commutedDirection :=
      directionalDerivative_univ_sum
        (fun direction candidate => principal direction candidate
          (fieldDirectionalDerivative field candidate direction))
        point termDifferentiable commutedDirection
    _ = ∑ direction : LorentzianIndex,
        ((fieldDirectionalDerivative (principal direction) point
            commutedDirection)
          (fieldDirectionalDerivative field point direction) +
        principal direction point
          (fieldDirectionalDerivative
            (fun candidate =>
              fieldDirectionalDerivative field candidate commutedDirection)
            point direction)) := by
      apply Finset.sum_congr rfl
      intro direction _
      rw [termDerivative direction]
      rw [directionalDerivativeField_commute field fieldSmooth point
        direction commutedDirection]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      abel

/-- Differentiating a fixed-current first-order matter operator gives the
same principal operator on the differentiated field plus exactly the
source-owned coefficient changed-read. -/
theorem matterCoordinateFirstOrderOperator_directionalDerivative
    (principal : LorentzianIndex → BasePoint → MatterRealEnd)
    (lower : BasePoint → MatterRealEnd)
    (field : BasePoint → MatterCoordinateCarrier)
    (principalSmooth : ∀ direction, ContDiff ℝ 1 (principal direction))
    (lowerSmooth : ContDiff ℝ 1 lower)
    (fieldSmooth : ContDiff ℝ 2 field)
    (point : BasePoint)
    (commutedDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterCoordinateFirstOrderOperator principal lower field)
        point commutedDirection =
      matterCoordinateFirstOrderOperator principal lower
          (fun candidate =>
            fieldDirectionalDerivative field candidate commutedDirection)
          point +
        (∑ direction : LorentzianIndex,
          (fieldDirectionalDerivative (principal direction) point
              commutedDirection)
            (fieldDirectionalDerivative field point direction)) +
        (fieldDirectionalDerivative lower point commutedDirection)
          (field point) := by
  let principalPart : BasePoint → MatterCoordinateCarrier := fun candidate =>
    ∑ direction : LorentzianIndex,
      principal direction candidate
        (fieldDirectionalDerivative field candidate direction)
  let lowerPart : BasePoint → MatterCoordinateCarrier := fun candidate =>
    lower candidate (field candidate)
  have principalPartDifferentiable : DifferentiableAt ℝ principalPart point := by
    apply DifferentiableAt.fun_sum
    intro direction _
    exact
      (((principalSmooth direction).differentiable one_ne_zero
        ).differentiableAt).clm_apply
        (((directionalDerivativeField_contDiff_one field fieldSmooth direction
          ).differentiable one_ne_zero).differentiableAt)
  have lowerPartDifferentiable : DifferentiableAt ℝ lowerPart point :=
    ((lowerSmooth.differentiable one_ne_zero).differentiableAt).clm_apply
      ((fieldSmooth.differentiable (by norm_num)).differentiableAt)
  change fieldDirectionalDerivative
      (fun candidate => principalPart candidate + lowerPart candidate)
      point commutedDirection = _
  rw [directionalDerivative_add principalPart lowerPart point
    principalPartDifferentiable lowerPartDifferentiable]
  change
    fieldDirectionalDerivative
        (fun candidate => ∑ direction : LorentzianIndex,
          principal direction candidate
            (fieldDirectionalDerivative field candidate direction))
        point commutedDirection +
      fieldDirectionalDerivative
        (fun candidate => lower candidate (field candidate))
        point commutedDirection = _
  rw [matterCoordinatePrincipalSum_directionalDerivative principal field
      principalSmooth fieldSmooth point commutedDirection,
    directionalDerivative_clm_apply lower field lowerSmooth
      (fieldSmooth.of_le (by norm_num))]
  unfold matterCoordinateFirstOrderOperator
  abel

end

end
  SaturationMonoid.PhysicsCore.StageNineMatterCoordinateFirstOrderCommutator
