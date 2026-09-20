import Mathlib.Analysis.SpecialFunctions.Log.Basic
import H0mework.Physics.SourceForms.P378

/-!
# Proposition 379: sampled Yukawa clocks are exactly nonabsorbing sigma

P377/P378 left the real sampled Yukawa clocks as explicit producer fields:
`lambda`, `step`, and

`sigma(yukawa y) = 1 - exp(-lambda_y * step_y)`.

This file removes that apparent freedom.  The exponential sampled-rate law has
exactly the finite nonabsorbing image:

* every sampled rate is `< 1`;
* every rate `sigma < 1` is sampled by the canonical clock
  `lambda = 1`, `step = -log(1 - sigma)`.

Therefore the current grand-unification producer normal form no longer needs
independent Yukawa clock fields.  It is equivalent to a zero-free 19-slot
certificate whose selected Yukawa sigmas are nonabsorbing.

Boundary: this still does not construct the zero-free certificate, the physical
running-sigma map, RG beta functions, or the selected discrete seed.  It only
proves that once those producers give finite nonabsorbing Yukawa sigmas, the
continuous sampled clocks are canonical.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## The image of the sampled exponential-rate law -/

/-- THEOREM 1: every real sampled decay rate is nonabsorbing: it is strictly
below `1`. -/
theorem realDecayRate_lt_one (lambda step : ℝ) :
    realDecayRate lambda step < 1 := by
  unfold realDecayRate realDecayResidual
  exact sub_lt_self (1 : ℝ) (Real.exp_pos _)

/-- THEOREM 2: every finite nonabsorbing rate `sigma < 1` is sampled by the
canonical clock `lambda=1`, `step=-log(1-sigma)`. -/
theorem realDecayRate_one_neg_log_one_sub_eq
    (sigma : ℝ) (hsigma : sigma < 1) :
    realDecayRate 1 (-(Real.log (1 - sigma))) = sigma := by
  unfold realDecayRate realDecayResidual
  have hpos : 0 < 1 - sigma := sub_pos.mpr hsigma
  have hexp :
      Real.exp ((-(1 : ℝ)) * (-(Real.log (1 - sigma)))) =
        1 - sigma := by
    have harg :
        (-(1 : ℝ)) * (-(Real.log (1 - sigma))) =
          Real.log (1 - sigma) := by
      ring
    rw [harg, Real.exp_log hpos]
  rw [hexp]
  ring

/-- THEOREM 3: sampled-rate existence is equivalent to `sigma < 1`. -/
theorem exists_realDecayRate_eq_iff_lt_one (sigma : ℝ) :
    (∃ lambda step : ℝ, realDecayRate lambda step = sigma) ↔ sigma < 1 := by
  constructor
  · rintro ⟨lambda, step, hsample⟩
    rw [← hsample]
    exact realDecayRate_lt_one lambda step
  · intro hsigma
    exact ⟨1, -(Real.log (1 - sigma)),
      realDecayRate_one_neg_log_one_sub_eq sigma hsigma⟩

end

end AffineRelaxation

namespace StandardModelConstraint

noncomputable section

/-! ## Grand-unification producer consequence -/

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- The zero-free certificate's selected Yukawa sigmas are finite
nonabsorbing rates. -/
def YukawaSigmaNonabsorbing
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) :
    Prop :=
  ∀ y : YukawaParameter,
    Z.running.sigma (StandardModelScaleCode.yukawa y) < 1

/-- The opened producer obligation with sampled clocks erased: a zero-free
certificate whose selected Yukawa rates are all nonabsorbing. -/
def ExistsZeroFreeNonabsorbingYukawaSigma
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    YukawaSigmaNonabsorbing Z

/-- THEOREM 4: nonabsorbing Yukawa sigmas canonically produce sampled clocks. -/
theorem existsSampledYukawaClocks_of_nonabsorbing
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (hZ : YukawaSigmaNonabsorbing Z) :
    ∃ yukawaLambda : YukawaParameter -> ℝ,
      ∃ yukawaStep : YukawaParameter -> ℝ,
        ∀ y : YukawaParameter,
          Z.running.sigma (StandardModelScaleCode.yukawa y) =
            AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y) := by
  refine ⟨(fun _ => 1),
    (fun y => -(Real.log (1 -
      Z.running.sigma (StandardModelScaleCode.yukawa y)))), ?_⟩
  intro y
  exact (AffineRelaxation.realDecayRate_one_neg_log_one_sub_eq
    (Z.running.sigma (StandardModelScaleCode.yukawa y)) (hZ y)).symm

/-- THEOREM 5: sampled clocks force exactly the nonabsorbing condition. -/
theorem nonabsorbing_of_sampledYukawaClocks
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (yukawaLambda : YukawaParameter -> ℝ)
    (yukawaStep : YukawaParameter -> ℝ)
    (hsampled :
      ∀ y : YukawaParameter,
        Z.running.sigma (StandardModelScaleCode.yukawa y) =
          AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)) :
    YukawaSigmaNonabsorbing Z := by
  intro y
  rw [hsampled y]
  exact AffineRelaxation.realDecayRate_lt_one
    (yukawaLambda y) (yukawaStep y)

/-- THEOREM 6: P376's minimal producer kernel is equivalent to a zero-free
certificate with nonabsorbing selected Yukawa sigmas.  The independent
`lambda/step` fields are therefore not an extra producer obligation. -/
theorem minimalProducerKernel_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma :
    Nonempty (MinimalGrandUnificationProducerKernel Index A CKMCarrier) ↔
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  constructor
  · intro h
    rcases h with ⟨M⟩
    refine ⟨M.zeroFree, ?_⟩
    exact nonabsorbing_of_sampledYukawaClocks
      M.zeroFree M.yukawaLambda M.yukawaStep
      M.selected_yukawa_sigma_sampled
  · intro h
    rcases h with ⟨Z, hZ⟩
    rcases existsSampledYukawaClocks_of_nonabsorbing Z hZ with
      ⟨yukawaLambda, yukawaStep, hsampled⟩
    exact ⟨{
      zeroFree := Z
      yukawaLambda := yukawaLambda
      yukawaStep := yukawaStep
      selected_yukawa_sigma_sampled := hsampled
    }⟩

/-- THEOREM 7: the P374 unified-formula spine exists iff there is a zero-free
19-slot certificate whose selected Yukawa sigmas are nonabsorbing. -/
theorem unifiedFormulaSpine_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma :
    Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) ↔
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  rw [MinimalGrandUnificationProducerKernel.unifiedFormulaSpine_nonempty_iff_minimalProducerKernel_nonempty]
  exact minimalProducerKernel_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma

/-- THEOREM 8: equivalently for P378's primitive producer atoms, the sampled
clock fields add no existence content beyond nonabsorbing Yukawa sigmas. -/
theorem primitiveProducerAtoms_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma :
    Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) ↔
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  rw [GrandUnificationPrimitiveProducerAtoms.nonempty_iff_minimalProducerKernel_nonempty]
  exact minimalProducerKernel_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma

end

end StandardModelConstraint
end SaturationMonoid
