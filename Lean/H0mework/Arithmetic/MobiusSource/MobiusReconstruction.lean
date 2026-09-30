import H0mework.Arithmetic.MobiusSource.MobiusFiniteCutoff

/-!
# Forward reconstruction from the centred Möbius source

The locally finite inverse generates a quarter-gap source for any exact raw
with that gap.  Reapplying the weighted divisor sum recovers the original raw
minus its constant mode; no compact preimage is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Set
open scoped ArithmeticFunction BigOperators

noncomputable section

theorem burnolCenteredMobiusInverse_eq_zero_of_quarterGap
    (raw : ℝ → ℂ)
    (quarterGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = raw 0)
    {t : ℝ} (inside : |t| ≤ (1 / 4 : ℝ)) :
    burnolCenteredMobiusInverse raw t = 0 := by
  rw [burnolCenteredMobiusInverse_eq_cutoffSum raw quarterGap]
  apply Finset.sum_eq_zero
  intro m _
  have mOne : (1 : ℝ) ≤ (m : ℕ) := by exact_mod_cast m.property
  have scaledInside : |t / ((m : ℕ) : ℝ)| ≤ (1 / 4 : ℝ) := by
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℕ))]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℕ))).2
      (inside.trans (by nlinarith))
  rw [burnolCenteredMobiusSummand, quarterGap scaledInside, sub_self, mul_zero,
    mul_zero]

def burnolCenteredMobiusReconstructionJointTerm
    (raw : ℝ → ℂ) (t : ℝ) (index : ℕ+ × ℕ+) : ℂ :=
  (((index.1 : ℕ) : ℂ)⁻¹) *
    burnolCenteredMobiusSummand raw (t / (index.1 : ℕ)) index.2

theorem burnolCenteredMobiusReconstructionJointTerm_finiteSupport
    (raw : ℝ → ℂ)
    (quarterGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = raw 0)
    (t : ℝ) :
    Function.HasFiniteSupport (burnolCenteredMobiusReconstructionJointTerm raw t) := by
  let bounded : Set ℕ+ := {n | (n : ℕ) < burnolCenteredMobiusCutoff t}
  have boundedFinite : bounded.Finite := by
    apply (Set.finite_lt_nat (burnolCenteredMobiusCutoff t)).preimage
    exact Set.injOn_of_injective PNat.coe_injective
  apply (boundedFinite.prod boundedFinite).subset
  rintro ⟨left, right⟩ termNe
  have productLt : (left : ℕ) * (right : ℕ) < burnolCenteredMobiusCutoff t := by
    by_contra notLt
    have cutoffLe : burnolCenteredMobiusCutoff t ≤ (left : ℕ) * (right : ℕ) :=
      Nat.le_of_not_gt notLt
    have denominatorPositive :
        (0 : ℝ) < ((left : ℕ) : ℝ) * ((right : ℕ) : ℝ) := by positivity
    have scaledInside :
        |(t / ((left : ℕ) : ℝ)) / ((right : ℕ) : ℝ)| ≤
          (1 / 4 : ℝ) := by
      rw [div_div, abs_div, abs_of_pos denominatorPositive]
      apply (div_le_iff₀ denominatorPositive).2
      have cutoffLeReal : 4 * |t| ≤
          ((left : ℕ) : ℝ) * ((right : ℕ) : ℝ) :=
        (Nat.le_ceil (4 * |t|)).trans (by exact_mod_cast cutoffLe)
      nlinarith
    exact termNe (by simp [burnolCenteredMobiusReconstructionJointTerm,
      burnolCenteredMobiusSummand, quarterGap scaledInside])
  constructor
  · exact lt_of_le_of_lt
      (Nat.le_mul_of_pos_right (left : ℕ) right.property) productLt
  · exact lt_of_le_of_lt
      (Nat.le_mul_of_pos_left (right : ℕ) left.property) productLt

theorem burnolCenteredMobiusForwardSum_eq_joint
    (raw : ℝ → ℂ)
    (quarterGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = raw 0)
    (t : ℝ) :
    (∑' n : ℕ+, (((n : ℕ) : ℂ)⁻¹) *
      burnolCenteredMobiusInverse raw (t / (n : ℕ))) =
      ∑' index : ℕ+ × ℕ+,
        burnolCenteredMobiusReconstructionJointTerm raw t index := by
  have jointSummable : Summable
      (burnolCenteredMobiusReconstructionJointTerm raw t) :=
    summable_of_hasFiniteSupport
    (burnolCenteredMobiusReconstructionJointTerm_finiteSupport raw quarterGap t)
  rw [jointSummable.tsum_prod]
  apply tsum_congr
  intro n
  unfold burnolCenteredMobiusInverse
  change (((n : ℕ) : ℂ)⁻¹) *
      (∑' m : ℕ+, burnolCenteredMobiusSummand raw (t / (n : ℕ)) m) = _
  have innerSummable : Summable
      (burnolCenteredMobiusSummand raw (t / (n : ℕ))) :=
    summable_of_hasFiniteSupport
    (burnolCenteredMobiusSummand_finiteSupport raw quarterGap (t / (n : ℕ)))
  rw [← innerSummable.tsum_mul_left (((n : ℕ) : ℂ)⁻¹)]
  exact tsum_congr fun m ↦ rfl

theorem burnolCenteredMobiusReconstructionJointTerm_fibre
    (raw : ℝ → ℂ) (t : ℝ) (value : ℕ+) :
    (∑ factor : (value : ℕ).divisorsAntidiagonal,
      burnolCenteredMobiusReconstructionJointTerm raw t
        (divisorsAntidiagonalFactors value factor)) =
      if (value : ℕ) = 1 then raw t - raw 0 else 0 := by
  classical
  let common : ℂ := (((value : ℕ) : ℂ)⁻¹) *
    (raw (t / ((value : ℕ) : ℝ)) - raw 0)
  calc
    _ = ∑ factor : (value : ℕ).divisorsAntidiagonal,
        ((ArithmeticFunction.zeta factor.1.1 : ℂ) *
          (ArithmeticFunction.moebius factor.1.2 : ℂ)) * common := by
      apply Finset.sum_congr rfl
      intro factor _
      have productEq := (Nat.mem_divisorsAntidiagonal.mp factor.2).1
      have productEqReal : ((factor.1.1 : ℕ) : ℝ) *
          ((factor.1.2 : ℕ) : ℝ) = ((value : ℕ) : ℝ) := by
        exact_mod_cast productEq
      have productEqComplex : ((factor.1.1 : ℕ) : ℂ) *
          ((factor.1.2 : ℕ) : ℂ) = ((value : ℕ) : ℂ) := by
        exact_mod_cast productEq
      have inverseEq : (((factor.1.1 : ℕ) : ℂ)⁻¹) *
          (((factor.1.2 : ℕ) : ℂ)⁻¹) = (((value : ℕ) : ℂ)⁻¹) := by
        rw [← mul_inv, productEqComplex]
      rw [ArithmeticFunction.zeta_apply_ne
        (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal factor.2)).ne']
      change (((factor.1.1 : ℕ) : ℂ)⁻¹) *
          ((ArithmeticFunction.moebius factor.1.2 : ℂ) *
            ((((factor.1.2 : ℕ) : ℂ)⁻¹) *
              (raw ((t / (factor.1.1 : ℕ)) / (factor.1.2 : ℕ)) - raw 0))) = _
      rw [div_div, productEqReal]
      unfold common
      calc
        _ = (ArithmeticFunction.moebius factor.1.2 : ℂ) *
            (((((factor.1.1 : ℕ) : ℂ)⁻¹) *
              (((factor.1.2 : ℕ) : ℂ)⁻¹)) *
                (raw (t / ((value : ℕ) : ℝ)) - raw 0)) := by ring
        _ = _ := by rw [inverseEq]; ring
    _ = ∑ factor ∈ (value : ℕ).divisorsAntidiagonal,
        ((ArithmeticFunction.zeta factor.1 : ℂ) *
          (ArithmeticFunction.moebius factor.2 : ℂ)) * common := by
      exact (Finset.sum_subtype _ (fun _ ↦ Iff.rfl)
        (fun factor : ℕ × ℕ ↦ ((ArithmeticFunction.zeta factor.1 : ℂ) *
          (ArithmeticFunction.moebius factor.2 : ℂ)) * common)).symm
    _ = (∑ factor ∈ (value : ℕ).divisorsAntidiagonal,
        (ArithmeticFunction.zeta factor.1 : ℂ) *
          (ArithmeticFunction.moebius factor.2 : ℂ)) * common := by
      rw [Finset.sum_mul]
    _ = (if (value : ℕ) = 1 then 1 else 0) * common := by
      congr 1
      have identity := congrArg (fun f : ArithmeticFunction ℂ ↦ f (value : ℕ))
        (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ))
      rw [ArithmeticFunction.mul_apply] at identity
      simpa [ArithmeticFunction.one_apply, value.ne_zero] using identity
    _ = _ := by
      split_ifs with valueOne
      · simp [valueOne, common]
      · simp

theorem burnolCenteredMobiusInverse_exactReconstruction
    (raw : ℝ → ℂ)
    (quarterGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = raw 0)
    (t : ℝ) :
    (∑' n : ℕ+, (((n : ℕ) : ℂ)⁻¹) *
      burnolCenteredMobiusInverse raw (t / (n : ℕ))) = raw t - raw 0 := by
  rw [burnolCenteredMobiusForwardSum_eq_joint raw quarterGap]
  let reindexed := fun entry : (value : ℕ+) ×
      (value : ℕ).divisorsAntidiagonal ↦
    burnolCenteredMobiusReconstructionJointTerm raw t
      (sigmaAntidiagonalEquivProd entry)
  have jointSummable : Summable
      (burnolCenteredMobiusReconstructionJointTerm raw t) :=
    summable_of_hasFiniteSupport
    (burnolCenteredMobiusReconstructionJointTerm_finiteSupport raw quarterGap t)
  have reindexedSummable : Summable reindexed :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr jointSummable
  calc
    _ = ∑' entry : (value : ℕ+) × (value : ℕ).divisorsAntidiagonal,
        reindexed entry := (sigmaAntidiagonalEquivProd.tsum_eq _).symm
    _ = ∑' value : ℕ+, ∑' factor : (value : ℕ).divisorsAntidiagonal,
        reindexed ⟨value, factor⟩ := reindexedSummable.tsum_sigma
    _ = ∑' value : ℕ+,
        if (value : ℕ) = 1 then raw t - raw 0 else 0 := by
      apply tsum_congr
      intro value
      rw [tsum_fintype]
      exact burnolCenteredMobiusReconstructionJointTerm_fibre raw t value
    _ = raw t - raw 0 := by simp


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
