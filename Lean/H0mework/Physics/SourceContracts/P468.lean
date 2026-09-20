/-
  Proposition 468: rate bumps are sampled zero-target keep flows.

  P467 proves the one-step coordinate identity

      1 - bumpSatField h sigma = relaxModule 0 sigma (1 - h).

  P292/P293 prove that finite sampled-rate relaxation and the continuous
  exponential envelope are the same affine flow.

  This file composes the two facts.  A salience/rate coordinate may look like
  it targets `1`, but the whole finite trajectory is exactly the complementary
  keep/headroom coordinate targeting `0`.  With

      sigma_step = realDecayRate lambda step,

  `n` discrete bumps become the zero-target continuous keep flow at sampled
  time `n * step`.

  Boundary: this is still a fixed-rate/fixed-clock sampled-flow theorem.  It
  does not derive the physical clock, `lambda`, or the RG scale map.
-/

import H0mework.Physics.SourceContracts.P467
import H0mework.Realization.RelaxationFlow.P293

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

/-! ## Iterating the complement coordinate -/

/-- THEOREM 1: the complement of `n` salience/rate bumps is the `n`-fold
zero-target relaxation of the initial keep/headroom coordinate. -/
theorem complement_bumpSatField_iterate_eq_zeroTarget_iterate
    {K : Type*} [Field K] (h sigma : K) (n : Nat) :
    (1 : K) - (fun z : K => bumpSatField z sigma)^[n] h =
      (fun k : K => AffineRelaxation.relaxModule (0 : K) sigma k)^[n]
        ((1 : K) - h) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [complement_bumpSatField_eq_zeroTarget_relaxModule_keep]
      rw [ih]
      exact (Function.iterate_succ_apply'
        (fun k : K => AffineRelaxation.relaxModule (0 : K) sigma k)
        n ((1 : K) - h)).symm

/-- THEOREM 2: repeated salience/rate bumps are recovered by taking the
complement of the zero-target keep trajectory. -/
theorem bumpSatField_iterate_eq_one_sub_zeroTarget_iterate
    {K : Type*} [Field K] (h sigma : K) (n : Nat) :
    (fun z : K => bumpSatField z sigma)^[n] h =
      (1 : K) -
        (fun k : K => AffineRelaxation.relaxModule (0 : K) sigma k)^[n]
          ((1 : K) - h) := by
  rw [← complement_bumpSatField_iterate_eq_zeroTarget_iterate h sigma n]
  ring

/-! ## Continuous sampled-flow form -/

/-- THEOREM 3: one continuous-envelope bump at time `t` is the complement of
the zero-target continuous keep flow at the same time. -/
theorem complement_bumpSatField_realDecayRate_eq_zeroTarget_flow_keep
    (h lambda t : ℝ) :
    (1 : ℝ) - bumpSatField h (AffineRelaxation.realDecayRate lambda t) =
      AffineRelaxation.realDecayRelaxFlow
        (0 : ℝ) lambda t ((1 : ℝ) - h) := by
  rw [complement_bumpSatField_eq_zeroTarget_relaxModule_keep]
  rfl

/-- THEOREM 4: equivalently, the apparent `Target=1` continuous-envelope bump
is the complement of a zero-target keep flow. -/
theorem bumpSatField_realDecayRate_eq_one_sub_zeroTarget_flow_keep
    (h lambda t : ℝ) :
    bumpSatField h (AffineRelaxation.realDecayRate lambda t) =
      (1 : ℝ) -
        AffineRelaxation.realDecayRelaxFlow
          (0 : ℝ) lambda t ((1 : ℝ) - h) := by
  rw [← complement_bumpSatField_realDecayRate_eq_zeroTarget_flow_keep h lambda t]
  ring

/-- THEOREM 5: `n` sampled salience/rate bumps have a complement equal to the
zero-target continuous keep flow at total sampled time `n * step`. -/
theorem complement_bumpSatField_iterate_realDecayRate_eq_zeroTarget_flow_keep
    (h lambda step : ℝ) (n : Nat) :
    (1 : ℝ) -
        (fun z : ℝ =>
          bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
      AffineRelaxation.realDecayRelaxFlow
        (0 : ℝ) lambda ((n : ℝ) * step) ((1 : ℝ) - h) := by
  rw [complement_bumpSatField_iterate_eq_zeroTarget_iterate]
  rw [AffineRelaxation.relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow]

/-- THEOREM 6: the sampled salience/rate trajectory itself is the complement of
the zero-target continuous keep flow at total sampled time. -/
theorem bumpSatField_iterate_realDecayRate_eq_one_sub_zeroTarget_flow_keep
    (h lambda step : ℝ) (n : Nat) :
    (fun z : ℝ =>
        bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
      (1 : ℝ) -
        AffineRelaxation.realDecayRelaxFlow
          (0 : ℝ) lambda ((n : ℝ) * step) ((1 : ℝ) - h) := by
  rw [← complement_bumpSatField_iterate_realDecayRate_eq_zeroTarget_flow_keep
    h lambda step n]
  ring

/-- THEOREM 7: the closed sampled keep residual is the initial keep multiplied
by the continuous exponential residual at total sampled time. -/
theorem complement_bumpSatField_iterate_realDecayRate_eq_closed_keep
    (h lambda step : ℝ) (n : Nat) :
    (1 : ℝ) -
        (fun z : ℝ =>
          bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
      ((1 : ℝ) - h) *
        AffineRelaxation.realDecayResidual lambda ((n : ℝ) * step) := by
  rw [complement_bumpSatField_iterate_realDecayRate_eq_zeroTarget_flow_keep]
  rw [AffineRelaxation.realDecayRelaxFlow_eq_closed]
  ring

/-- THEOREM 8: repeated sampled salience/rate bumps have the closed form
`1 - keep₀ * exp(-lambda * n * step)`. -/
theorem bumpSatField_iterate_realDecayRate_eq_closed_rate
    (h lambda step : ℝ) (n : Nat) :
    (fun z : ℝ =>
        bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
      (1 : ℝ) -
        ((1 : ℝ) - h) *
          AffineRelaxation.realDecayResidual lambda ((n : ℝ) * step) := by
  rw [← complement_bumpSatField_iterate_realDecayRate_eq_closed_keep
    h lambda step n]
  ring

/-! ## Bundled receipt -/

/-- A reusable receipt: the full salience/rate sampled trajectory is a
zero-target keep trajectory in complementary coordinates. -/
structure RateComplementSampledZeroTargetFlowReceipt : Prop where
  complement_iterate :
    ∀ h sigma : ℝ, ∀ n : Nat,
      (1 : ℝ) - (fun z : ℝ => bumpSatField z sigma)^[n] h =
        (fun k : ℝ => AffineRelaxation.relaxModule (0 : ℝ) sigma k)^[n]
          ((1 : ℝ) - h)
  one_bump_flow :
    ∀ h lambda t : ℝ,
      (1 : ℝ) - bumpSatField h (AffineRelaxation.realDecayRate lambda t) =
        AffineRelaxation.realDecayRelaxFlow
          (0 : ℝ) lambda t ((1 : ℝ) - h)
  sampled_flow :
    ∀ h lambda step : ℝ, ∀ n : Nat,
      (1 : ℝ) -
          (fun z : ℝ =>
            bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
        AffineRelaxation.realDecayRelaxFlow
          (0 : ℝ) lambda ((n : ℝ) * step) ((1 : ℝ) - h)
  closed_keep :
    ∀ h lambda step : ℝ, ∀ n : Nat,
      (1 : ℝ) -
          (fun z : ℝ =>
            bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
        ((1 : ℝ) - h) *
          AffineRelaxation.realDecayResidual lambda ((n : ℝ) * step)
  closed_rate :
    ∀ h lambda step : ℝ, ∀ n : Nat,
      (fun z : ℝ =>
          bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
        (1 : ℝ) -
          ((1 : ℝ) - h) *
            AffineRelaxation.realDecayResidual lambda ((n : ℝ) * step)

/-- THEOREM 9: the sampled rate/bump surface has the zero-target complement
flow receipt. -/
theorem rateComplementSampledZeroTargetFlowReceipt :
    RateComplementSampledZeroTargetFlowReceipt where
  complement_iterate :=
    complement_bumpSatField_iterate_eq_zeroTarget_iterate
  one_bump_flow :=
    complement_bumpSatField_realDecayRate_eq_zeroTarget_flow_keep
  sampled_flow :=
    complement_bumpSatField_iterate_realDecayRate_eq_zeroTarget_flow_keep
  closed_keep :=
    complement_bumpSatField_iterate_realDecayRate_eq_closed_keep
  closed_rate :=
    bumpSatField_iterate_realDecayRate_eq_closed_rate

end

end StandardModelConstraint
end SaturationMonoid
