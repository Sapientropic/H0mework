import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.JointSourceArrayPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceMixed289ResponseOwn
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open PreparationVacuumGradedTransport PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open PreparationVacuumSpatialDensityTransport PreparationVacuumJointFieldResponse
open scoped BigOperators
attribute [local irreducible] uncutOperator sourceResolvent jointResolvent sourceYJet compression transportedCompression originalCompactYPrice Ring.inverse

private theorem original_diagonal_inverse (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) :
    Ring.inverse (movingDiagonal 0 p F z 0) = CanonicalPhysicalResolvent.finiteResolvent p F z := by
  exact congrArg (fun A : H →L[ℂ] H => Ring.inverse (A - z • 1))
    (transportedCompression_zero 0 p F)

-- The 57 terms are exactly the original source grade-nilpotent resolvent series.
def originalJointResolventPrice (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) : ℝ :=
  (∑ n ∈ Finset.range 57, ((1 / |z.im|) * originalCompactYPrice 0 p F 0) ^ n) * (1 / |z.im|)

private theorem original_joint_series (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im ≠ 0) : jointResolvent p F z 0 = sourceSeries 0 p F none z 0 :=
  (jointResolvent_zero 0 p F z).trans (sourceResolvent_series 0 p F none z 0
    ((movingDiagonal_units 0 p F z hz).self_of_nhds))

private theorem original_sourceStep_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖sourceStep 0 p F none z 0‖ ≤ (1 / |z.im|) * originalCompactYPrice 0 p F 0 := by
  unfold sourceStep
  rw [norm_neg, original_diagonal_inverse p F z]
  simp only [sourceYJet, uncutJetOperator]
  exact (norm_mul_le (CanonicalPhysicalResolvent.finiteResolvent p F z) (uncutOperator 0 (finiteRetainer p F) 0)).trans
    (mul_le_mul (CanonicalPhysicalResolvent.finite_bound p F z hz)
      (originalCompactY_price 0 p F 0) (norm_nonneg _) (by positivity))

private theorem geometric_series_price {A : Type*} [NormedRing A]
    (step inverse : A) (t u : ℝ) (ht : ‖step‖ ≤ t) (hu : ‖inverse‖ ≤ u) (onePrice : ‖(1 : A)‖ ≤ 1) :
    ‖(∑ n ∈ Finset.range 57, step^n) * inverse‖ ≤ (∑ n ∈ Finset.range 57, t^n) * u := by
  have t0 : 0 ≤ t := (norm_nonneg step).trans ht
  have total : 0 ≤ ∑ n ∈ Finset.range 57, t^n := by positivity
  apply (norm_mul_le (∑ n ∈ Finset.range 57, step^n) inverse).trans
  apply mul_le_mul _ hu (norm_nonneg inverse) total
  apply (norm_sum_le (Finset.range 57) (fun n => step^n)).trans
  apply Finset.sum_le_sum
  intro n _
  have powers : ‖step^n‖ ≤ ‖step‖^n := by
    cases n with
    | zero => simpa only [pow_zero] using onePrice
    | succ n => exact norm_pow_le' step (Nat.succ_pos n)
  exact powers.trans (pow_le_pow_left₀ (norm_nonneg step) ht n)

theorem originalJointResolvent_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im ≠ 0) : ‖jointResolvent p F z 0‖ ≤ originalJointResolventPrice p F z := by
  rw [original_joint_series p F z hz]
  unfold sourceSeries originalJointResolventPrice
  rw [original_diagonal_inverse p F z]
  exact geometric_series_price (sourceStep 0 p F none z 0)
    (CanonicalPhysicalResolvent.finiteResolvent p F z)
    ((1 / |z.im|) * originalCompactYPrice 0 p F 0) (1 / |z.im|)
    (original_sourceStep_price p F z hz) (CanonicalPhysicalResolvent.finite_bound p F z hz)
    ContinuousLinearMap.norm_id_le

end LowEnergy.ActualSourceMixed289ResponseOwn
