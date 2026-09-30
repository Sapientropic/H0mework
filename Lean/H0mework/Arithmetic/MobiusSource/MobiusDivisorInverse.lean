import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusFourierFamily
/-!
# Centred Möbius inversion of the actual compact co-Poisson source

Local finiteness comes from the generated annular gap.  Multiplicative divisor
reindexing then consumes Mathlib's Möbius-zeta inverse to recover the same source.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators
noncomputable section

def burnolCompactCenteredCoPoissonSum (source : burnolCompactAnnulusSource)
    (t : ℝ) : ℂ :=
  burnolCompactAdditiveCoSum source t -
    burnolCompactAdditiveCoSum source 0

def burnolCompactScaledSourceTerm
    (source : burnolCompactAnnulusSource) (t : ℝ) (n : ℕ+) : ℂ :=
  (((n : ℕ) : ℂ)⁻¹) *
    burnolCompactAdditiveSource source (t / (n : ℕ))

theorem burnolCompactScaledSourceTerm_finiteSupport
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    Function.HasFiniteSupport (burnolCompactScaledSourceTerm source t) := by
  obtain ⟨bound, boundLarge⟩ := exists_nat_gt (4 * |t|)
  have boundedFinite : ({n : ℕ+ | (n : ℕ) < bound} : Set ℕ+).Finite := by
    apply (Set.finite_lt_nat bound).preimage
    exact Set.injOn_of_injective PNat.coe_injective
  apply boundedFinite.subset
  intro n termNe
  by_contra notLt
  have boundLe : bound ≤ (n : ℕ) := Nat.le_of_not_gt notLt
  have nPositive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.property
  have nLarge : 4 * |t| < ((n : ℕ) : ℝ) :=
    boundLarge.trans_le (by exact_mod_cast boundLe)
  have inside : |t / ((n : ℕ) : ℝ)| ≤ (1 / 4 : ℝ) := by
    rw [abs_div, abs_of_pos nPositive]
    apply (div_le_iff₀ nPositive).2
    nlinarith
  have sourceZero :=
    burnolCompactAdditiveSource_zero_of_abs_le_quarter source inside
  exact termNe (by simp [burnolCompactScaledSourceTerm, sourceZero])

theorem burnolCompactCenteredCoPoissonSum_eq_tsum
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCompactCenteredCoPoissonSum source t =
      ∑' n : ℕ+, burnolCompactScaledSourceTerm source t n := by
  rw [burnolCompactCenteredCoPoissonSum,
    burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source
      (t := 0) (by norm_num), burnolCompactAdditiveCoSum]
  simp only [sub_neg_eq_add, sub_add_cancel]
  simp only [burnolCompactScaledSourceTerm]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
    ((n : ℂ)⁻¹) * burnolCompactAdditiveSource source (t / n))]

def burnolCompactMobiusJointTerm
    (source : burnolCompactAnnulusSource) (t : ℝ)
    (index : ℕ+ × ℕ+) : ℂ :=
  (ArithmeticFunction.moebius (index.1 : ℕ) : ℂ) *
    (((index.1 : ℕ) : ℂ)⁻¹ *
      burnolCompactScaledSourceTerm source
        (t / (index.1 : ℕ)) index.2)

theorem burnolCompactMobiusJointTerm_finiteSupport
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    Function.HasFiniteSupport (burnolCompactMobiusJointTerm source t) := by
  obtain ⟨bound, boundLarge⟩ := exists_nat_gt (4 * |t|)
  let bounded : Set ℕ+ := {n | (n : ℕ) < bound}
  have boundedFinite : bounded.Finite := by
    apply (Set.finite_lt_nat bound).preimage
    exact Set.injOn_of_injective PNat.coe_injective
  apply (boundedFinite.prod boundedFinite).subset
  rintro ⟨left, right⟩ termNe
  have productLt : (left : ℕ) * (right : ℕ) < bound := by
    by_contra notLt
    have boundLe : bound ≤ (left : ℕ) * (right : ℕ) :=
      Nat.le_of_not_gt notLt
    have productLarge : 4 * |t| <
        (((left : ℕ) * (right : ℕ) : ℕ) : ℝ) :=
      boundLarge.trans_le (by exact_mod_cast boundLe)
    have inside :
        |(t / ((left : ℕ) : ℝ)) / ((right : ℕ) : ℝ)| ≤
          (1 / 4 : ℝ) := by
      rw [div_div, abs_div]
      have denominatorPositive :
          (0 : ℝ) < ((left : ℕ) : ℝ) * ((right : ℕ) : ℝ) :=
        mul_pos (by exact_mod_cast left.property)
          (by exact_mod_cast right.property)
      have denominatorAbs :
          |((left : ℕ) : ℝ) * ((right : ℕ) : ℝ)| =
            ((left : ℕ) : ℝ) * ((right : ℕ) : ℝ) :=
        abs_of_pos denominatorPositive
      rw [denominatorAbs]
      norm_num only [Nat.cast_mul] at productLarge
      apply (div_le_iff₀ denominatorPositive).2
      nlinarith
    have sourceZero :=
      burnolCompactAdditiveSource_zero_of_abs_le_quarter source inside
    exact termNe (by simp [burnolCompactMobiusJointTerm,
      burnolCompactScaledSourceTerm, sourceZero])
  constructor
  · exact lt_of_le_of_lt
      (Nat.le_mul_of_pos_right (left : ℕ) right.property) productLt
  · exact lt_of_le_of_lt
      (Nat.le_mul_of_pos_left (right : ℕ) left.property) productLt

def burnolCenteredMobiusInverse (raw : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' m : ℕ+,
    (ArithmeticFunction.moebius (m : ℕ) : ℂ) * (((m : ℕ) : ℂ)⁻¹ *
      (raw (t / (m : ℕ)) - raw 0))

theorem burnolCompactCenteredMobiusInverse_eq_joint
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCenteredMobiusInverse (burnolCompactAdditiveCoSum source) t =
      ∑' index : ℕ+ × ℕ+,
        burnolCompactMobiusJointTerm source t index := by
  have jointSummable : Summable (burnolCompactMobiusJointTerm source t) :=
    summable_of_hasFiniteSupport
      (burnolCompactMobiusJointTerm_finiteSupport source t)
  rw [jointSummable.tsum_prod]
  unfold burnolCenteredMobiusInverse
  apply tsum_congr
  intro m
  change (ArithmeticFunction.moebius (m : ℕ) : ℂ) *
      (((m : ℕ) : ℂ)⁻¹ * burnolCompactCenteredCoPoissonSum source
        (t / (m : ℕ))) = _
  rw [burnolCompactCenteredCoPoissonSum_eq_tsum]
  have innerSummable : Summable
      (burnolCompactScaledSourceTerm source (t / (m : ℕ))) :=
    summable_of_hasFiniteSupport
      (burnolCompactScaledSourceTerm_finiteSupport source (t / (m : ℕ)))
  rw [← innerSummable.tsum_mul_left (((m : ℕ) : ℂ)⁻¹),
    ← (innerSummable.mul_left (((m : ℕ) : ℂ)⁻¹)).tsum_mul_left
      (ArithmeticFunction.moebius (m : ℕ) : ℂ)]
  exact tsum_congr fun n ↦ rfl
private theorem complex_moebius_divisor_sum
    (value : ℕ+) :
    (∑ divisor ∈ (value : ℕ).divisors,
      (ArithmeticFunction.moebius divisor : ℂ)) =
      if (value : ℕ) = 1 then 1 else 0 := by
  have identity := congrArg (fun f : ArithmeticFunction ℂ ↦ f (value : ℕ))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at identity
  simpa [ArithmeticFunction.one_apply, value.ne_zero] using identity

theorem burnolCompactMobiusJointTerm_fibre
    (source : burnolCompactAnnulusSource) (t : ℝ) (value : ℕ+) :
    (∑ factor : (value : ℕ).divisorsAntidiagonal,
      burnolCompactMobiusJointTerm source t
        (divisorsAntidiagonalFactors value factor)) =
      if (value : ℕ) = 1 then
        burnolCompactAdditiveSource source t else 0 := by
  classical
  let common : ℂ := (((value : ℕ) : ℂ)⁻¹) *
    burnolCompactAdditiveSource source (t / ((value : ℕ) : ℝ))
  calc
    _ = ∑ factor : (value : ℕ).divisorsAntidiagonal,
        (ArithmeticFunction.moebius factor.1.1 : ℂ) * common := by
      apply Finset.sum_congr rfl
      intro factor _factorMem
      have productEq := (Nat.mem_divisorsAntidiagonal.mp factor.2).1
      have productEqReal :
          ((factor.1.1 : ℕ) : ℝ) * ((factor.1.2 : ℕ) : ℝ) =
            ((value : ℕ) : ℝ) := by exact_mod_cast productEq
      have productEqComplex :
          ((factor.1.1 : ℕ) : ℂ) * ((factor.1.2 : ℕ) : ℂ) =
            ((value : ℕ) : ℂ) := by exact_mod_cast productEq
      have inverseEq :
          (((factor.1.1 : ℕ) : ℂ)⁻¹) *
              (((factor.1.2 : ℕ) : ℂ)⁻¹) =
            (((value : ℕ) : ℂ)⁻¹) := by
        rw [← mul_inv, productEqComplex]
      change (ArithmeticFunction.moebius factor.1.1 : ℂ) *
          (((factor.1.1 : ℕ) : ℂ)⁻¹ *
            (((factor.1.2 : ℕ) : ℂ)⁻¹ *
              burnolCompactAdditiveSource source
                ((t / (factor.1.1 : ℕ)) / (factor.1.2 : ℕ)))) = _
      rw [div_div, productEqReal]
      unfold common
      calc
        _ = (ArithmeticFunction.moebius factor.1.1 : ℂ) *
            (((((factor.1.1 : ℕ) : ℂ)⁻¹) *
              (((factor.1.2 : ℕ) : ℂ)⁻¹)) *
                burnolCompactAdditiveSource source
                  (t / ((value : ℕ) : ℝ))) := by ring
        _ = _ := by rw [inverseEq]
    _ = ∑ factor ∈ (value : ℕ).divisorsAntidiagonal,
        (ArithmeticFunction.moebius factor.1 : ℂ) * common := by
      exact (Finset.sum_subtype _ (fun _ ↦ Iff.rfl)
        (fun factor : ℕ × ℕ ↦
          (ArithmeticFunction.moebius factor.1 : ℂ) * common)).symm
    _ = ∑ divisor ∈ (value : ℕ).divisors,
        (ArithmeticFunction.moebius divisor : ℂ) * common := by
      simpa using Nat.sum_divisorsAntidiagonal
        (n := (value : ℕ)) (fun divisor _complement ↦
          (ArithmeticFunction.moebius divisor : ℂ) * common)
    _ = (∑ divisor ∈ (value : ℕ).divisors,
          (ArithmeticFunction.moebius divisor : ℂ)) * common := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [complex_moebius_divisor_sum]
      split_ifs with valueOne
      · unfold common
        simp [valueOne]
      · simp

theorem burnolCompactMobiusJointTerm_tsum
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    (∑' index : ℕ+ × ℕ+,
      burnolCompactMobiusJointTerm source t index) =
      burnolCompactAdditiveSource source t := by
  let reindexed := fun entry : (value : ℕ+) ×
      (value : ℕ).divisorsAntidiagonal ↦
    burnolCompactMobiusJointTerm source t
      (sigmaAntidiagonalEquivProd entry)
  have jointSummable : Summable (burnolCompactMobiusJointTerm source t) :=
    summable_of_hasFiniteSupport
      (burnolCompactMobiusJointTerm_finiteSupport source t)
  have reindexedSummable : Summable reindexed :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr jointSummable
  calc
    _ = ∑' entry : (value : ℕ+) ×
        (value : ℕ).divisorsAntidiagonal, reindexed entry := by
      exact (sigmaAntidiagonalEquivProd.tsum_eq
        (burnolCompactMobiusJointTerm source t)).symm
    _ = ∑' value : ℕ+,
        ∑' factor : (value : ℕ).divisorsAntidiagonal,
          reindexed ⟨value, factor⟩ := reindexedSummable.tsum_sigma
    _ = ∑' value : ℕ+,
        if (value : ℕ) = 1 then
          burnolCompactAdditiveSource source t else 0 := by
      apply tsum_congr
      intro value
      rw [tsum_fintype]
      exact burnolCompactMobiusJointTerm_fibre source t value
    _ = burnolCompactAdditiveSource source t := by simp

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
