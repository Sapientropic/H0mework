import H0mework.Physics.Dirac.FullDiracAdjointMaterial
import H0mework.Physics.Matter.SU7ExteriorBreakingYukawa

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

namespace SaturationMonoid.PhysicsCore
namespace StageNineExteriorYukawaHermitianCompletion

open DiracExteriorMatterAction
open StageNineFullDiracAdjointMaterial
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra

noncomputable section

local instance su7MotherIndexLinearOrder : LinearOrder SU7MotherIndex :=
  SU7ExteriorMatterRestriction.instLinearOrderSU7MotherIndex

private theorem exteriorCoordinatePair_add_left
    (degree : Nat)
    (first second right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree (first + second) right =
      exteriorCoordinatePair degree first right +
        exteriorCoordinatePair degree second right := by
  simp [exteriorCoordinatePair, Finset.sum_add_distrib, add_mul]

private theorem exteriorCoordinatePair_add_right
    (degree : Nat)
    (left first second : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left (first + second) =
      exteriorCoordinatePair degree left first +
        exteriorCoordinatePair degree left second := by
  simp [exteriorCoordinatePair, Finset.sum_add_distrib, mul_add]

private theorem exteriorCoordinatePair_smul_left
    (degree : Nat) (scalar : ℂ)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree (scalar • left) right =
      starRingEnd ℂ scalar * exteriorCoordinatePair degree left right := by
  unfold exteriorCoordinatePair
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [mul_assoc]

private theorem exteriorCoordinatePair_smul_right
    (degree : Nat) (scalar : ℂ)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left (scalar • right) =
      scalar * exteriorCoordinatePair degree left right := by
  unfold exteriorCoordinatePair
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

private theorem exteriorCoordinatePair_sum_left
    {Index : Type} [Fintype Index]
    (degree : Nat)
    (left : Index → ⋀[ℂ]^degree SU7FundamentalCarrier)
    (right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree (∑ index, left index) right =
      ∑ index, exteriorCoordinatePair degree (left index) right := by
  classical
  induction (Finset.univ : Finset Index) using Finset.induction_on with
  | empty => simp [exteriorCoordinatePair]
  | @insert index indices hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem,
        exteriorCoordinatePair_add_left, ih]

private theorem exteriorCoordinatePair_sum_right
    {Index : Type} [Fintype Index]
    (degree : Nat)
    (left : ⋀[ℂ]^degree SU7FundamentalCarrier)
    (right : Index → ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left (∑ index, right index) =
      ∑ index, exteriorCoordinatePair degree left (right index) := by
  classical
  induction (Finset.univ : Finset Index) using Finset.induction_on with
  | empty => simp [exteriorCoordinatePair]
  | @insert index indices hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem,
        exteriorCoordinatePair_add_right, ih]

private theorem exteriorCoordinatePair_conj_symm
    (degree : Nat)
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

@[simp] private theorem exteriorCoordinatePair_zero_left
    (degree : Nat)
    (right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree 0 right = 0 := by
  simp [exteriorCoordinatePair]

@[simp] private theorem exteriorCoordinatePair_zero_right
    (degree : Nat)
    (left : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left 0 = 0 := by
  simp [exteriorCoordinatePair]

/-- The Hermitian adjoint is generated coordinatewise from the finite matrix
of the exterior-product Yukawa map. -/
def exteriorYukawaMassAdjoint
    (scalar : ExteriorBreakingScalarCarrier) :
    ExteriorDegreeSixMatterCarrier →ₗ[ℂ] ExteriorDegreeTwoMatterCarrier :=
  (su7ExteriorBasis 6).constr ℂ fun target =>
    ∑ input : ExteriorBasisIndex 2,
      star ((su7ExteriorBasis 6).repr
        (exteriorYukawaMassMap scalar
          (su7ExteriorBasis 2 input)) target) •
        su7ExteriorBasis 2 input

private theorem exteriorYukawaMassAdjoint_basisPair
    (scalar : ExteriorBreakingScalarCarrier)
    (input : ExteriorBasisIndex 2)
    (target : ExteriorBasisIndex 6) :
    exteriorCoordinatePair 6
        (exteriorYukawaMassMap scalar (su7ExteriorBasis 2 input))
        (su7ExteriorBasis 6 target) =
      exteriorCoordinatePair 2 (su7ExteriorBasis 2 input)
        (exteriorYukawaMassAdjoint scalar
          (su7ExteriorBasis 6 target)) := by
  unfold exteriorCoordinatePair exteriorYukawaMassAdjoint
  rw [Finset.sum_eq_single target]
  · rw [Finset.sum_eq_single input]
    · rw [Module.Basis.constr_basis, map_sum, Finset.sum_apply',
        Finset.sum_eq_single input]
      · simp
      · intro candidate _ notEqual
        simp [notEqual]
      · simp
    · intro candidate _ notEqual
      simp [notEqual]
    · simp
  · intro candidate _ notEqual
    simp [notEqual]
  · simp

/-- The explicit finite-basis map is the Hermitian adjoint of the generated
exterior Yukawa mass map. -/
theorem exteriorYukawaMassAdjoint_spec
    (scalar : ExteriorBreakingScalarCarrier)
    (input : ExteriorDegreeTwoMatterCarrier)
    (output : ExteriorDegreeSixMatterCarrier) :
    exteriorCoordinatePair 6
        (exteriorYukawaMassMap scalar input) output =
      exteriorCoordinatePair 2 input
        (exteriorYukawaMassAdjoint scalar output) := by
  classical
  rw [← (su7ExteriorBasis 2).sum_repr input,
    ← (su7ExteriorBasis 6).sum_repr output]
  simp only [map_sum, map_smul]
  rw [exteriorCoordinatePair_sum_left,
    exteriorCoordinatePair_sum_right]
  simp_rw [exteriorCoordinatePair_sum_right,
    exteriorCoordinatePair_sum_left,
    exteriorCoordinatePair_smul_left,
    exteriorCoordinatePair_smul_right]
  conv_rhs =>
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro inputIndex _
  apply Finset.sum_congr rfl
  intro targetIndex _
  rw [exteriorYukawaMassAdjoint_basisPair]

/-- Hermitian completion of the one-way Yukawa arrow on the full internal
carrier.  The degree-four summand remains dynamically untouched. -/
def fullInternalYukawaHermitianCompletion
    (scalar : ExteriorBreakingScalarCarrier) :
    Module.End ℂ SU7ExteriorSpinorMatterCarrier where
  toFun matter :=
    (exteriorYukawaMassMap scalar matter.2.1,
      (exteriorYukawaMassAdjoint scalar matter.1, 0))
  map_add' first second := by simp
  map_smul' coefficient matter := by simp

/-- The generated forward-plus-adjoint completion is self-adjoint for the
canonical full internal Hermitian pairing. -/
theorem fullInternalYukawaHermitianCompletion_selfAdjoint
    (scalar : ExteriorBreakingScalarCarrier)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair
        (fullInternalYukawaHermitianCompletion scalar left) right =
      fullInternalPair left
        (fullInternalYukawaHermitianCompletion scalar right) := by
  rcases left with ⟨leftSix, leftTwo, leftFour⟩
  rcases right with ⟨rightSix, rightTwo, rightFour⟩
  have reverseAdjoint :
      exteriorCoordinatePair 2
          (exteriorYukawaMassAdjoint scalar leftSix) rightTwo =
        exteriorCoordinatePair 6 leftSix
          (exteriorYukawaMassMap scalar rightTwo) := by
    calc
      exteriorCoordinatePair 2
          (exteriorYukawaMassAdjoint scalar leftSix) rightTwo =
          starRingEnd ℂ (exteriorCoordinatePair 2 rightTwo
            (exteriorYukawaMassAdjoint scalar leftSix)) :=
        (exteriorCoordinatePair_conj_symm 2 rightTwo
          (exteriorYukawaMassAdjoint scalar leftSix)).symm
      _ = starRingEnd ℂ (exteriorCoordinatePair 6
            (exteriorYukawaMassMap scalar rightTwo) leftSix) := by
        rw [exteriorYukawaMassAdjoint_spec]
      _ = exteriorCoordinatePair 6 leftSix
          (exteriorYukawaMassMap scalar rightTwo) :=
        exteriorCoordinatePair_conj_symm 6
          (exteriorYukawaMassMap scalar rightTwo) leftSix
  change
    exteriorCoordinatePair 6
          (exteriorYukawaMassMap scalar leftTwo) rightSix +
        exteriorCoordinatePair 2
          (exteriorYukawaMassAdjoint scalar leftSix) rightTwo +
        exteriorCoordinatePair 4 0 rightFour =
      exteriorCoordinatePair 6 leftSix
          (exteriorYukawaMassMap scalar rightTwo) +
        exteriorCoordinatePair 2 leftTwo
          (exteriorYukawaMassAdjoint scalar rightSix) +
        exteriorCoordinatePair 4 leftFour 0
  rw [exteriorYukawaMassAdjoint_spec, reverseAdjoint]
  simp
  ring

end
end StageNineExteriorYukawaHermitianCompletion
end SaturationMonoid.PhysicsCore
