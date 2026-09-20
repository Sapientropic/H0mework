import H0mework.Physics.Dirac.P286DiracAdjointCoefficientMaterial

/-!
# Full exterior-matter Dirac-adjoint material

The full `Lambda^6 V x (Lambda^2 V x Lambda^4 V)` carrier has a canonical
Hermitian coordinate pairing and Dirac adjoint.  The P286 coefficient
material is its exact restriction, rather than a separate law.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore
namespace StageNineFullDiracAdjointMaterial

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorMatterGaugeCovariantJet
open StageNineP286DiracAdjointCoefficientMaterial

noncomputable section

/-- Coordinate Hermitian pairing on one explicit exterior-power basis. -/
def exteriorCoordinatePair (degree : Nat)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) : ℂ :=
  ∑ index : ExteriorBasisIndex degree,
    starRingEnd ℂ ((su7ExteriorBasis degree).repr left index) *
      (su7ExteriorBasis degree).repr right index

/-- Hermitian pairing on the complete physical internal matter carrier. -/
def fullInternalPair
    (left right : SU7ExteriorSpinorMatterCarrier) : ℂ :=
  exteriorCoordinatePair 6 left.1 right.1 +
    exteriorCoordinatePair 2 left.2.1 right.2.1 +
    exteriorCoordinatePair 4 left.2.2 right.2.2

private theorem exteriorCoordinatePair_add_right (degree : Nat)
    (left first second : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left (first + second) =
      exteriorCoordinatePair degree left first +
        exteriorCoordinatePair degree left second := by
  simp [exteriorCoordinatePair, Finset.sum_add_distrib, mul_add]

private theorem exteriorCoordinatePair_add_left (degree : Nat)
    (first second right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree (first + second) right =
      exteriorCoordinatePair degree first right +
        exteriorCoordinatePair degree second right := by
  simp [exteriorCoordinatePair, Finset.sum_add_distrib, add_mul]

private theorem exteriorCoordinatePair_smul_right (degree : Nat)
    (scalar : ℂ)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left (scalar • right) =
      scalar * exteriorCoordinatePair degree left right := by
  unfold exteriorCoordinatePair
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

private theorem exteriorCoordinatePair_smul_left (degree : Nat)
    (scalar : ℂ)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree (scalar • left) right =
      starRingEnd ℂ scalar * exteriorCoordinatePair degree left right := by
  unfold exteriorCoordinatePair
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [mul_assoc]

private theorem exteriorCoordinatePair_conj_symm (degree : Nat)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    starRingEnd ℂ (exteriorCoordinatePair degree left right) =
      exteriorCoordinatePair degree right left := by
  unfold exteriorCoordinatePair
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [map_mul]
  change
    star (star ((su7ExteriorBasis degree).repr left index)) *
        star ((su7ExteriorBasis degree).repr right index) =
      star ((su7ExteriorBasis degree).repr right index) *
        (su7ExteriorBasis degree).repr left index
  rw [star_star]
  ring

private theorem fullInternalPair_add_right
    (left first second : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair left (first + second) =
      fullInternalPair left first + fullInternalPair left second := by
  simp [fullInternalPair, exteriorCoordinatePair_add_right]
  ring

private theorem fullInternalPair_add_left
    (first second right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (first + second) right =
      fullInternalPair first right + fullInternalPair second right := by
  simp [fullInternalPair, exteriorCoordinatePair_add_left]
  ring

private theorem fullInternalPair_smul_right
    (scalar : ℂ)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair left (scalar • right) =
      scalar * fullInternalPair left right := by
  simp [fullInternalPair, exteriorCoordinatePair_smul_right]
  ring

private theorem fullInternalPair_smul_left
    (scalar : ℂ)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (scalar • left) right =
      starRingEnd ℂ scalar * fullInternalPair left right := by
  simp [fullInternalPair, exteriorCoordinatePair_smul_left]
  ring

private theorem fullInternalPair_conj_symm
    (left right : SU7ExteriorSpinorMatterCarrier) :
    starRingEnd ℂ (fullInternalPair left right) =
      fullInternalPair right left := by
  simp only [fullInternalPair, map_add, exteriorCoordinatePair_conj_symm]

private theorem fullInternalPair_self_im
    (matter : SU7ExteriorSpinorMatterCarrier) :
    (fullInternalPair matter matter).im = 0 := by
  have hconj :
      starRingEnd ℂ (fullInternalPair matter matter) =
        fullInternalPair matter matter :=
    fullInternalPair_conj_symm matter matter
  have him := congrArg Complex.im hconj
  simp only [Complex.conj_im] at him
  linarith

/-- Hermitizing spin swap. -/
def diracAdjointSpinSwap : DiracMatrix :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

private def diracAdjointSpinSwapAction
    (matter : DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  diracMatrixMatterAction diracAdjointSpinSwap matter

/-- Canonical Dirac adjoint of arbitrary full exterior matter. -/
def fullCanonicalDiracAdjoint
    (matter : DiracExteriorMatterCarrier) :
    Module.Dual ℂ DiracExteriorMatterCarrier where
  toFun candidate :=
    ∑ spin : DiracSpinorIndex,
      fullInternalPair (diracAdjointSpinSwapAction matter spin)
        (candidate spin)
  map_add' first second := by
    simp [fullInternalPair_add_right, Finset.sum_add_distrib]
  map_smul' scalar candidate := by
    simp [fullInternalPair_smul_right, Finset.mul_sum]

theorem fullCanonicalDiracAdjoint_add
    (first second : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (first + second) =
      fullCanonicalDiracAdjoint first + fullCanonicalDiracAdjoint second := by
  apply LinearMap.ext
  intro candidate
  simp [fullCanonicalDiracAdjoint, diracAdjointSpinSwapAction,
    map_add, fullInternalPair_add_left, Finset.sum_add_distrib]

theorem fullCanonicalDiracAdjoint_smul
    (scalar : ℂ) (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (scalar • matter) =
      (starRingEnd ℂ scalar) • fullCanonicalDiracAdjoint matter := by
  apply LinearMap.ext
  intro candidate
  simp [fullCanonicalDiracAdjoint, diracAdjointSpinSwapAction,
    map_smul, fullInternalPair_smul_left, Finset.mul_sum]

@[simp] theorem fullCanonicalDiracAdjoint_zero :
    fullCanonicalDiracAdjoint
        (0 : DiracExteriorMatterCarrier) = 0 := by
  have zeroScaled := fullCanonicalDiracAdjoint_smul
    (0 : ℂ) (0 : DiracExteriorMatterCarrier)
  simpa using zeroScaled

private theorem diracAdjointSpinSwapAction_zero
    (matter : DiracExteriorMatterCarrier) :
    diracAdjointSpinSwapAction matter 0 = matter 2 := by
  simp [diracAdjointSpinSwapAction, diracMatrixMatterAction,
    diracAdjointSpinSwap, Fin.sum_univ_four]

private theorem diracAdjointSpinSwapAction_one
    (matter : DiracExteriorMatterCarrier) :
    diracAdjointSpinSwapAction matter 1 = matter 3 := by
  simp [diracAdjointSpinSwapAction, diracMatrixMatterAction,
    diracAdjointSpinSwap, Fin.sum_univ_four]

private theorem diracAdjointSpinSwapAction_two
    (matter : DiracExteriorMatterCarrier) :
    diracAdjointSpinSwapAction matter 2 = matter 0 := by
  simp [diracAdjointSpinSwapAction, diracMatrixMatterAction,
    diracAdjointSpinSwap, Fin.sum_univ_four]

private theorem diracAdjointSpinSwapAction_three
    (matter : DiracExteriorMatterCarrier) :
    diracAdjointSpinSwapAction matter 3 = matter 1 := by
  simp [diracAdjointSpinSwapAction, diracMatrixMatterAction,
    diracAdjointSpinSwap, Fin.sum_univ_four]

private theorem fullCanonicalDiracAdjoint_apply
    (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint matter candidate =
      fullInternalPair (matter 2) (candidate 0) +
      fullInternalPair (matter 3) (candidate 1) +
      fullInternalPair (matter 0) (candidate 2) +
      fullInternalPair (matter 1) (candidate 3) := by
  simp [fullCanonicalDiracAdjoint, Fin.sum_univ_four,
    diracAdjointSpinSwapAction_zero, diracAdjointSpinSwapAction_one,
    diracAdjointSpinSwapAction_two, diracAdjointSpinSwapAction_three]

/-- Complete spin-slot evaluation, reusable by source-owned matter lifts. -/
theorem fullCanonicalDiracAdjoint_evaluate
    (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint matter candidate =
      fullInternalPair (matter 2) (candidate 0) +
      fullInternalPair (matter 3) (candidate 1) +
      fullInternalPair (matter 0) (candidate 2) +
      fullInternalPair (matter 1) (candidate 3) :=
  fullCanonicalDiracAdjoint_apply matter candidate

private theorem fullInternalPair_symmetric_sum_im
    (first second : SU7ExteriorSpinorMatterCarrier) :
    (fullInternalPair first second +
      fullInternalPair second first).im = 0 := by
  rw [← fullInternalPair_conj_symm first second]
  simp

private theorem fullInternalPair_swap_re
    (first second : SU7ExteriorSpinorMatterCarrier) :
    (fullInternalPair second first).re =
      (fullInternalPair first second).re := by
  rw [← fullInternalPair_conj_symm first second]
  simp

/-- Every full matter spinor generates real `J gamma^mu` currents. -/
theorem fullCanonicalDiracAdjoint_diracCurrent_real
    (matter : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    (fullCanonicalDiracAdjoint matter
      (diracMatrixMatterAction (diracGamma direction) matter)).im = 0 := by
  fin_cases direction
  · rw [fullCanonicalDiracAdjoint_apply]
    simp [diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, fullInternalPair_smul_right,
      fullInternalPair_self_im]
  · rw [fullCanonicalDiracAdjoint_apply]
    simp [diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree, Fin.sum_univ_four]
    have h23 := fullInternalPair_symmetric_sum_im (matter 2) (matter 3)
    have h01 := fullInternalPair_symmetric_sum_im (matter 0) (matter 1)
    simp only [Complex.add_im] at h23 h01
    linarith
  · rw [fullCanonicalDiracAdjoint_apply]
    simp [diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, fullInternalPair_smul_right]
    rw [fullInternalPair_swap_re (matter 2) (matter 3),
      fullInternalPair_swap_re (matter 0) (matter 1)]
    ring
  · rw [fullCanonicalDiracAdjoint_apply]
    simp [diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, fullInternalPair_smul_right,
      fullInternalPair_self_im]

/-- A primal field and its dual are restrictions of one full material. -/
def FullDiracAdjointPaired
    (matter : DiracExteriorMatterCarrier)
    (adjoint : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  adjoint = fullCanonicalDiracAdjoint matter

/-- Exact mismatch between an actual dual field and the canonical adjoint. -/
def fullDiracAdjointResidual
    (matter : DiracExteriorMatterCarrier)
    (adjoint : Module.Dual ℂ DiracExteriorMatterCarrier) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  adjoint - fullCanonicalDiracAdjoint matter

theorem fullDiracAdjointPaired_iff_residual_zero
    (matter : DiracExteriorMatterCarrier)
    (adjoint : Module.Dual ℂ DiracExteriorMatterCarrier) :
    FullDiracAdjointPaired matter adjoint ↔
      fullDiracAdjointResidual matter adjoint = 0 := by
  simp [FullDiracAdjointPaired, fullDiracAdjointResidual, sub_eq_zero]

theorem FullDiracAdjointPaired.add
    {firstMatter secondMatter : DiracExteriorMatterCarrier}
    {firstAdjoint secondAdjoint : Module.Dual ℂ DiracExteriorMatterCarrier}
    (first : FullDiracAdjointPaired firstMatter firstAdjoint)
    (second : FullDiracAdjointPaired secondMatter secondAdjoint) :
    FullDiracAdjointPaired
      (firstMatter + secondMatter) (firstAdjoint + secondAdjoint) := by
  unfold FullDiracAdjointPaired at first second ⊢
  rw [first, second, fullCanonicalDiracAdjoint_add]

theorem FullDiracAdjointPaired.smul
    {matter : DiracExteriorMatterCarrier}
    {adjoint : Module.Dual ℂ DiracExteriorMatterCarrier}
    (paired : FullDiracAdjointPaired matter adjoint)
    (scalar : ℂ) :
    FullDiracAdjointPaired
      (scalar • matter) ((starRingEnd ℂ scalar) • adjoint) := by
  unfold FullDiracAdjointPaired at paired ⊢
  rw [paired, fullCanonicalDiracAdjoint_smul]

theorem FullDiracAdjointPaired.diracCurrent_real
    {matter : DiracExteriorMatterCarrier}
    {adjoint : Module.Dual ℂ DiracExteriorMatterCarrier}
    (paired : FullDiracAdjointPaired matter adjoint)
    (direction : LorentzianIndex) :
    (adjoint
      (diracMatrixMatterAction (diracGamma direction) matter)).im = 0 := by
  rw [paired]
  exact fullCanonicalDiracAdjoint_diracCurrent_real matter direction

private theorem fullInternalPair_p286HyperchargeMatterProbe
    (matter : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair p286HyperchargeMatterProbe matter =
      hyperchargeDegreeTwoMatterCoordinate matter := by
  classical
  simp [fullInternalPair, exteriorCoordinatePair,
    p286HyperchargeMatterProbe, hyperchargeDegreeTwoMatterCoordinate]
  rw [Finset.sum_eq_single hyperchargeDegreeTwoIndex]
  · simp
  · intro index _ hne
    simp [hne]
  · simp

/-- Kill test: the full adjoint restricts exactly to the P286 adjoint. -/
theorem fullCanonicalDiracAdjoint_p286SpinMatter
    (coefficient : Fin 4 → ℂ) :
    fullCanonicalDiracAdjoint (p286SpinMatter coefficient) =
      p286SpinAdjoint coefficient := by
  apply LinearMap.ext
  intro candidate
  rw [fullCanonicalDiracAdjoint_apply]
  simp [p286SpinMatter, fullInternalPair_smul_left,
    fullInternalPair_p286HyperchargeMatterProbe,
    p286SpinAdjoint, p286SpinCoordinate]

private def spinTwoCoefficient : Fin 4 → ℂ :=
  fun spin => if spin = 2 then 1 else 0

/-- The original source probe is already one full Dirac material. -/
theorem fullCanonicalDiracAdjoint_diracSpinTwoMatterProbe :
    fullCanonicalDiracAdjoint diracSpinTwoMatterProbe =
      diracSpinZeroMatterCoordinate := by
  rw [← show p286SpinMatter spinTwoCoefficient = diracSpinTwoMatterProbe by
    funext spin
    fin_cases spin <;>
      simp [p286SpinMatter, spinTwoCoefficient, diracSpinTwoMatterProbe]]
  rw [fullCanonicalDiracAdjoint_p286SpinMatter]
  apply LinearMap.ext
  intro matter
  simp [p286SpinAdjoint, p286SpinCoordinate, spinTwoCoefficient,
    diracSpinZeroMatterCoordinate]

end
end StageNineFullDiracAdjointMaterial
end SaturationMonoid.PhysicsCore
