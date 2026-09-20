import H0mework.Physics.YukawaSources.P426

/-!
# Proposition 427: affine relaxation commutes with the 19-slot decomposition

P426 proves that a Standard-Model parameter vector is exactly a pair:

`3 x 3 Yukawa matrix subvector × ten-slot non-Yukawa complement`.

This file puts the unified affine relaxation formula on that whole carrier.
The pointwise Standard-Model parameter update

`x(slot) -> x(slot) + sigma(slot) * (target(slot) - x(slot))`

commutes strictly with the P426 coordinate decomposition.  Same-target
composition remains noisy-OR pointwise.  Thus the formula is not merely a
slotwise slogan: it is stable under the 19-slot ↔ matrix/complement coordinate
change.

Boundary: this is algebra of the parameter carrier.  It still does not
construct the physical RG/threshold producer that chooses the target/rate
vectors.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Pointwise relaxation on parameter-vector coordinates -/

/-- Pointwise noisy-OR rate composition on a 19-slot parameter vector. -/
def parameterVectorSatOr {K : Type*} [Field K]
    (sigma1 sigma2 : ParameterVector K) : ParameterVector K :=
  fun slot => satOrField (sigma1 slot) (sigma2 slot)

/-- Pointwise unified affine relaxation on the 19-slot parameter vector. -/
def parameterVectorRelax {K : Type*} [Field K]
    (target sigma x : ParameterVector K) : ParameterVector K :=
  fun slot =>
    AffineRelaxation.relaxModule (target slot) (sigma slot) (x slot)

/-- THEOREM 1: uniform-rate pointwise relaxation is the ordinary module-valued
relaxation on the whole `ParameterVector K` carrier. -/
theorem parameterVectorRelax_constRate_eq_relaxModule
    {K : Type*} [Field K]
    (target x : ParameterVector K) (sigma : K) :
    parameterVectorRelax target (fun _ => sigma) x =
      AffineRelaxation.relaxModule target sigma x := by
  funext slot
  rfl

/-- THEOREM 2: same-target pointwise relaxations compose by pointwise
noisy-OR. -/
theorem parameterVectorRelax_compose
    {K : Type*} [Field K]
    (target x sigma1 sigma2 : ParameterVector K) :
    parameterVectorRelax target sigma2
        (parameterVectorRelax target sigma1 x) =
      parameterVectorRelax target (parameterVectorSatOr sigma1 sigma2) x := by
  funext slot
  exact AffineRelaxation.relaxModule_compose
    (target slot) (x slot) (sigma1 slot) (sigma2 slot)

/-- THEOREM 3: same-target pointwise relaxations commute. -/
theorem parameterVectorRelax_comm
    {K : Type*} [Field K]
    (target x sigma1 sigma2 : ParameterVector K) :
    parameterVectorRelax target sigma2
        (parameterVectorRelax target sigma1 x) =
      parameterVectorRelax target sigma1
        (parameterVectorRelax target sigma2 x) := by
  funext slot
  exact AffineRelaxation.relaxModule_compose_comm
    (target slot) (x slot) (sigma1 slot) (sigma2 slot)

/-- THEOREM 4: zero rate is a pointwise no-op. -/
theorem parameterVectorRelax_zero
    {K : Type*} [Field K]
    (target x : ParameterVector K) :
    parameterVectorRelax target (fun _ => (0 : K)) x = x := by
  funext slot
  exact AffineRelaxation.relaxModule_zero (target slot) (x slot)

/-- THEOREM 5: unit rate jumps pointwise to the target vector. -/
theorem parameterVectorRelax_one
    {K : Type*} [Field K]
    (target x : ParameterVector K) :
    parameterVectorRelax target (fun _ => (1 : K)) x = target := by
  funext slot
  exact AffineRelaxation.relaxModule_one (target slot) (x slot)

/-- THEOREM 6: the target vector is pointwise absorbing for every rate vector. -/
theorem parameterVectorRelax_target_absorbing
    {K : Type*} [Field K]
    (target sigma : ParameterVector K) :
    parameterVectorRelax target sigma target = target := by
  funext slot
  exact AffineRelaxation.relaxModule_target_absorbing
    (target slot) (sigma slot)

/-! ## Componentwise relaxation on the P426 decomposition -/

/-- Pointwise noisy-OR on a `3 x 3` Yukawa matrix subvector. -/
def yukawaMatrixSubvectorSatOr {K : Type*} [Field K]
    (sigma1 sigma2 : YukawaMatrixSubvector K) : YukawaMatrixSubvector K :=
  fun g s => satOrField (sigma1 g s) (sigma2 g s)

/-- Pointwise affine relaxation on a `3 x 3` Yukawa matrix subvector. -/
def yukawaMatrixSubvectorRelax {K : Type*} [Field K]
    (target sigma x : YukawaMatrixSubvector K) : YukawaMatrixSubvector K :=
  fun g s =>
    AffineRelaxation.relaxModule (target g s) (sigma g s) (x g s)

/-- Pointwise noisy-OR on the ten-slot complement. -/
def nonYukawaSubvectorSatOr {K : Type*} [Field K]
    (sigma1 sigma2 : NonYukawaSubvector K) : NonYukawaSubvector K :=
  fun n => satOrField (sigma1 n) (sigma2 n)

/-- Pointwise affine relaxation on the ten-slot complement. -/
def nonYukawaSubvectorRelax {K : Type*} [Field K]
    (target sigma x : NonYukawaSubvector K) : NonYukawaSubvector K :=
  fun n =>
    AffineRelaxation.relaxModule (target n) (sigma n) (x n)

/-- THEOREM 7: projecting a relaxed parameter vector to the Yukawa matrix is
the same as relaxing the projected matrix subvectors. -/
theorem parameterVectorToYukawaMatrix_relax
    {K : Type*} [Field K]
    (target sigma x : ParameterVector K) :
    parameterVectorToYukawaMatrix
        (parameterVectorRelax target sigma x) =
      yukawaMatrixSubvectorRelax
        (parameterVectorToYukawaMatrix target)
        (parameterVectorToYukawaMatrix sigma)
        (parameterVectorToYukawaMatrix x) := by
  rfl

/-- THEOREM 8: projecting a relaxed parameter vector to the non-Yukawa
complement is the same as relaxing the projected complement subvectors. -/
theorem parameterVectorToNonYukawaComplement_relax
    {K : Type*} [Field K]
    (target sigma x : ParameterVector K) :
    parameterVectorToNonYukawaComplement
        (parameterVectorRelax target sigma x) =
      nonYukawaSubvectorRelax
        (parameterVectorToNonYukawaComplement target)
        (parameterVectorToNonYukawaComplement sigma)
        (parameterVectorToNonYukawaComplement x) := by
  rfl

/-- THEOREM 9: reconstructing after componentwise relaxation is the same as
relaxing after reconstructing. -/
theorem parameterVectorFromComponents_relax
    {K : Type*} [Field K]
    (targetY sigmaY xY : YukawaMatrixSubvector K)
    (targetN sigmaN xN : NonYukawaSubvector K) :
    parameterVectorFromComponents
        (yukawaMatrixSubvectorRelax targetY sigmaY xY)
        (nonYukawaSubvectorRelax targetN sigmaN xN) =
      parameterVectorRelax
        (parameterVectorFromComponents targetY targetN)
        (parameterVectorFromComponents sigmaY sigmaN)
        (parameterVectorFromComponents xY xN) := by
  funext slot
  cases slot <;> rfl

/-- THEOREM 10: under P426's component equivalence, pointwise relaxation is
exactly product relaxation on the Yukawa matrix and non-Yukawa complement. -/
theorem parameterVectorComponentsEquiv_relax
    {K : Type*} [Field K]
    (target sigma x : ParameterVector K) :
    parameterVectorComponentsEquiv K
        (parameterVectorRelax target sigma x) =
      (yukawaMatrixSubvectorRelax
          (parameterVectorToYukawaMatrix target)
          (parameterVectorToYukawaMatrix sigma)
          (parameterVectorToYukawaMatrix x),
        nonYukawaSubvectorRelax
          (parameterVectorToNonYukawaComplement target)
          (parameterVectorToNonYukawaComplement sigma)
          (parameterVectorToNonYukawaComplement x)) := by
  rfl

/-- THEOREM 11: same-target composition on Yukawa matrix subvectors is
pointwise noisy-OR. -/
theorem yukawaMatrixSubvectorRelax_compose
    {K : Type*} [Field K]
    (target x sigma1 sigma2 : YukawaMatrixSubvector K) :
    yukawaMatrixSubvectorRelax target sigma2
        (yukawaMatrixSubvectorRelax target sigma1 x) =
      yukawaMatrixSubvectorRelax target
        (yukawaMatrixSubvectorSatOr sigma1 sigma2) x := by
  funext g s
  exact AffineRelaxation.relaxModule_compose
    (target g s) (x g s) (sigma1 g s) (sigma2 g s)

/-- THEOREM 12: same-target composition on the non-Yukawa complement is
pointwise noisy-OR. -/
theorem nonYukawaSubvectorRelax_compose
    {K : Type*} [Field K]
    (target x sigma1 sigma2 : NonYukawaSubvector K) :
    nonYukawaSubvectorRelax target sigma2
        (nonYukawaSubvectorRelax target sigma1 x) =
      nonYukawaSubvectorRelax target
        (nonYukawaSubvectorSatOr sigma1 sigma2) x := by
  funext n
  exact AffineRelaxation.relaxModule_compose
    (target n) (x n) (sigma1 n) (sigma2 n)

end StandardModelConstraint
end SaturationMonoid
