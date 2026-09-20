import Mathlib.Analysis.Calculus.FDeriv.Mul
import H0mework.Physics.Coframe.CurrentCoframeMatterTemporalPrincipal
import H0mework.Physics.MatterPreparation.ContorsionSpatialProfileActualLift

/-!
# S9-C3h200w: noncharacteristic temporal principal on the spatial skew profile

This module specializes the branch-free current-coframe temporal principal to
the already source/action-generated C3h200i spatial skew profile.  It proves
the matrix inverse derivative from the actual inverse map at the identity,
then derives:

* `q = 1` at the canonical origin;
* `q' = 0` along each generated spatial skew axis;
* a canonical neighborhood of the origin lies in `q ≠ 0`.

The neighborhood is obtained from continuity of the generated formula.  No
radius, inverse witness, branch selector, target solution, or
noncharacteristic receipt is stored in the source.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSpatialSkewCoframeTemporalPrincipal

open ProofFreeRicherAnholonomicSource
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCoframeVariation
open StageNineEinsteinCartanSkewCoframeActualResponseOperator
open StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open scoped ContDiff Matrix Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- The generated affine skew axis is a smooth actual coframe path. -/
private theorem skewCoframeAxis_contDiff
    (coordinates : Fin 6 → ℝ) :
    ContDiff ℝ ∞ (skewCoframeAxis coordinates) := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  simpa [skewCoframeAxis] using
    (contDiff_const.add
      (contDiff_id.mul
        (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ =>
          loweredLorentzBivectorMatrix coordinates internal coordinate)))

/-- Entrywise matrix inversion differentiates to `-K` at the identity.  The
derivative is solved from the actual identity `(1+tK)(1+tK)⁻¹=1`; it is not
accepted as an inverse witness. -/
theorem skewCoframeAxis_inv_entry_hasDerivAt_zero
    (coordinates : Fin 6 → ℝ)
    (row column : LorentzianIndex) :
    HasDerivAt
      (fun parameter =>
        (skewCoframeAxis coordinates parameter)⁻¹ row column)
      (-loweredLorentzBivectorMatrix coordinates row column)
      0 := by
  have inverseMatrixSmooth :
      ContDiffAt ℝ ∞
        (fun parameter =>
          (skewCoframeAxis coordinates parameter)⁻¹)
        0 := by
    have nondegenerateAtOrigin :
        Matrix.det (skewCoframeAxis coordinates 0) ≠ 0 :=
      ne_of_gt (skewCoframeAxis_det_pos coordinates 0)
    simpa [Function.comp_def] using
      (coframe_inv_contDiffAt
        (skewCoframeAxis coordinates 0)
        nondegenerateAtOrigin).comp 0
        (skewCoframeAxis_contDiff coordinates).contDiffAt
  have inverseEntryHasDeriv
      (candidateRow candidateColumn : LorentzianIndex) :
      HasDerivAt
        (fun parameter =>
          (skewCoframeAxis coordinates parameter)⁻¹
            candidateRow candidateColumn)
        (deriv
          (fun parameter =>
            (skewCoframeAxis coordinates parameter)⁻¹
              candidateRow candidateColumn)
          0)
        0 := by
    exact
      ((contDiffAt_pi.mp
        (contDiffAt_pi.mp inverseMatrixSmooth candidateRow)
        candidateColumn).differentiableAt (by simp)).hasDerivAt
  have productDerivative :
      HasDerivAt
        (fun parameter =>
          ∑ middle : LorentzianIndex,
            skewCoframeAxis coordinates parameter row middle *
              (skewCoframeAxis coordinates parameter)⁻¹ middle column)
        (∑ middle : LorentzianIndex,
          (loweredLorentzBivectorMatrix coordinates row middle *
              (skewCoframeAxis coordinates 0)⁻¹ middle column +
            skewCoframeAxis coordinates 0 row middle *
              deriv
                (fun parameter =>
                  (skewCoframeAxis coordinates parameter)⁻¹
                    middle column)
                0))
        0 := by
    exact HasDerivAt.fun_sum (u := Finset.univ) fun middle _ =>
      (skewCoframeAxis_entry_hasDerivAt coordinates row middle).mul
        (inverseEntryHasDeriv middle column)
  have productConstant :
      (fun parameter =>
        ∑ middle : LorentzianIndex,
          skewCoframeAxis coordinates parameter row middle *
            (skewCoframeAxis coordinates parameter)⁻¹ middle column) =
        fun _ : ℝ => (1 : LorentzianCoframe) row column := by
    funext parameter
    change
      ((skewCoframeAxis coordinates parameter) *
          (skewCoframeAxis coordinates parameter)⁻¹) row column =
        (1 : LorentzianCoframe) row column
    rw [Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr
        (ne_of_gt
          (skewCoframeAxis_det_pos coordinates parameter)))]
  have coefficientZero := productDerivative.deriv
  rw [productConstant] at coefficientZero
  simp only [deriv_const'] at coefficientZero
  have derivativeValue :
      deriv
          (fun parameter =>
            (skewCoframeAxis coordinates parameter)⁻¹ row column)
          0 =
        -loweredLorentzBivectorMatrix coordinates row column := by
    fin_cases row <;> fin_cases column <;>
      simp [skewCoframeAxis_zero, Matrix.one_apply,
        Fin.sum_univ_four] at coefficientZero ⊢ <;>
      linarith
  simpa [derivativeValue] using inverseEntryHasDeriv row column

/-- The scalar square of the temporal principal has no linear drift along a
spatial skew axis.  The inverse gamma itself can have a nonzero first
derivative; only its Lorentzian norm has zero first derivative. -/
theorem skewCoframeAxis_temporalPrincipalScalar_hasDerivAt_zero
    (coordinates : Fin 6 → ℝ) :
    HasDerivAt
      (fun parameter =>
        coframeTemporalPrincipalScalar
          (skewCoframeAxis coordinates parameter))
      0 0 := by
  unfold coframeTemporalPrincipalScalar
  have eachDerivative (internal : LorentzianIndex) :
      HasDerivAt
        (fun parameter =>
          minkowskiInternalSign internal *
            (skewCoframeAxis coordinates parameter)⁻¹
              (0 : LorentzianIndex) internal ^ 2)
        0 0 := by
    have inverseEntry :=
      skewCoframeAxis_inv_entry_hasDerivAt_zero coordinates
        (0 : LorentzianIndex) internal
    fin_cases internal
    · simpa [skewCoframeAxis_zero, Matrix.one_apply,
        loweredLorentzBivectorMatrix,
        orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
        Fin.sum_univ_six, minkowskiInternalSign] using
        (inverseEntry.fun_pow 2).const_mul (-1 : ℝ)
    all_goals
      simpa [skewCoframeAxis_zero, Matrix.one_apply,
        loweredLorentzBivectorMatrix,
        orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
        Fin.sum_univ_six, minkowskiInternalSign] using
        inverseEntry.fun_pow 2
  have sumDerivative :
      HasDerivAt
        (fun parameter =>
          ∑ internal : LorentzianIndex,
            minkowskiInternalSign internal *
              (skewCoframeAxis coordinates parameter)⁻¹
                (0 : LorentzianIndex) internal ^ 2)
        0 0 := by
    simpa only [Finset.sum_const_zero] using
      HasDerivAt.fun_sum (u := Finset.univ)
        (fun internal _ => eachDerivative internal)
  change HasDerivAt
    (fun parameter : ℝ =>
      -(∑ internal : LorentzianIndex,
        minkowskiInternalSign internal *
          (skewCoframeAxis coordinates parameter)⁻¹
            (0 : LorentzianIndex) internal ^ 2))
    0 0
  simpa only [neg_one_mul, neg_zero] using
    sumDerivative.const_mul (-1 : ℝ)

/-- Canonical local noncharacteristic domain along every generated skew
axis.  No radius is selected. -/
theorem skewCoframeAxis_eventually_temporal_noncharacteristic
    (coordinates : Fin 6 → ℝ) :
    ∀ᶠ parameter in nhds (0 : ℝ),
      coframeTemporalPrincipalScalar
          (skewCoframeAxis coordinates parameter) ≠
        0 := by
  have valueAtOrigin :
      coframeTemporalPrincipalScalar
          (skewCoframeAxis coordinates 0) =
        1 := by
    rw [skewCoframeAxis_zero]
    exact coframeTemporalPrincipalScalar_one
  exact
    (skewCoframeAxis_temporalPrincipalScalar_hasDerivAt_zero
      coordinates).continuousAt.eventually_ne
      (valueAtOrigin.trans_ne one_ne_zero)

/-! ## Source/action-generated profile specialization -/

theorem preContorsionSpatialProfileActual_coframe_spatialAxis
    (axis : Fin 3) (parameter : ℝ) :
    preContorsionSpatialProfileActual.coframe
        (parameter • coordinateDirection axis.succ) =
      skewCoframeAxis (generatedSpatialSkewCoframeJet axis) parameter := by
  change
    (skewCoframeActual
      (spatialSkewCoframeJetLift generatedSpatialSkewCoframeJet)).coframe
        (parameter • coordinateDirection axis.succ) =
      _
  rw [skewCoframeActual_axis_eq,
    spatialSkewCoframeJetLift_spatial]

@[simp] theorem
    preContorsionSpatialProfileActual_temporalPrincipalScalar_origin :
    coframeTemporalPrincipalScalar
        (preContorsionSpatialProfileActual.coframe 0) =
      1 := by
  rw [preContorsionSpatialProfileActual_coframe_origin]
  exact coframeTemporalPrincipalScalar_one

theorem
    preContorsionSpatialProfileActual_temporalPrincipalScalar_spatialAxis_hasDerivAt_zero
    (axis : Fin 3) :
    HasDerivAt
      (fun parameter : ℝ =>
        coframeTemporalPrincipalScalar
          (preContorsionSpatialProfileActual.coframe
            (parameter • coordinateDirection axis.succ)))
      0 0 := by
  have profileAxis :
      (fun parameter : ℝ =>
        coframeTemporalPrincipalScalar
          (preContorsionSpatialProfileActual.coframe
            (parameter • coordinateDirection axis.succ))) =
        fun parameter : ℝ =>
          coframeTemporalPrincipalScalar
            (skewCoframeAxis
              (generatedSpatialSkewCoframeJet axis)
              parameter) := by
    funext parameter
    rw [preContorsionSpatialProfileActual_coframe_spatialAxis]
  rw [profileAxis]
  exact
    skewCoframeAxis_temporalPrincipalScalar_hasDerivAt_zero
      (generatedSpatialSkewCoframeJet axis)

theorem
    preContorsionSpatialProfileActual_eventually_temporal_noncharacteristic_spatialAxis
    (axis : Fin 3) :
    ∀ᶠ parameter in nhds (0 : ℝ),
      coframeTemporalPrincipalScalar
          (preContorsionSpatialProfileActual.coframe
            (parameter • coordinateDirection axis.succ)) ≠
        0 := by
  filter_upwards [
    skewCoframeAxis_eventually_temporal_noncharacteristic
      (generatedSpatialSkewCoframeJet axis)] with parameter
      noncharacteristic
  rw [preContorsionSpatialProfileActual_coframe_spatialAxis]
  exact noncharacteristic

end

end
  SaturationMonoid.PhysicsCore.StageNineSpatialSkewCoframeTemporalPrincipal
