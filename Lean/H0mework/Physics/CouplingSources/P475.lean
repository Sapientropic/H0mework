/-
  Proposition 475: the running-sigma two-coordinate spine.

  P471 proves the Yukawa side:

      sampled sigma -> zero-target residual exponential flow.

  P472-P473 prove the gauge side:

      one-loop sigma -> inverse-coupling affine flow,
      and that flow composes by addition on non-pole patches.

  This file does not invent a new physical postulate.  It records the
  unification layer: the same running-sigma framework has two coordinate
  readings.

  * Yukawa coordinates read sigma through residual/keep powers.
  * Gauge coordinates read sigma through inverse coupling.

  Boundary: this is a spine/receipt theorem.  It does not construct the
  physical clock maps, threshold corrections, or higher-loop beta functions.
  It proves that the currently formalized Yukawa and gauge laws are compatible
  members of one running-sigma certificate layer.
-/

import H0mework.Physics.YukawaSources.P471
import H0mework.Realization.Claims.P474

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

/-! ## Joint coordinate statements -/

/-- THEOREM 1: a running-sigma certificate simultaneously gives the sampled
zero-target Yukawa law and the Standard-Model one-loop gauge flow law.

The two conclusions use different coordinates, but they sit in one theorem:
Yukawa is residual/exponential, gauge running is inverse-affine. -/
theorem generated_yukawa_and_standardModel_gauge_flow
    {Seed Scale Index A CKMCarrier : Type*} [AddCommGroup A]
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A ℝ CKMCarrier)
    (seed : Seed) (y : YukawaParameter)
    (lambda step : ℝ)
    (hsampled :
      C.sigma (C.yukawaScale seed y) =
        AffineRelaxation.realDecayRate lambda step)
    (G : RunningSigmaBeta.StandardModelGaugeFactor) (sigma0 t s : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden_t :
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
        sigma0 * t ≠ 0)
    (hden_ts :
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
        sigma0 * (t + s) ≠ 0) :
    C.pinned.base.generated seed (yukawaSlot y) =
        AffineRelaxation.realDecayRelaxFlow
          (0 : ℝ) lambda
          ((C.pinned.yukawaExponent seed y : ℝ) * step)
          (C.pinned.yukawaAmplitude y)
      ∧
    RunningSigmaBeta.standardModelOneLoopSigmaFlow G
        (RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 t) s =
      RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 (t + s) := by
  constructor
  · exact
      C.generated_yukawa_eq_sampled_zeroTarget_flow
        seed y lambda step hsampled
  · exact
      RunningSigmaBeta.standardModelOneLoopSigmaFlow_add
        G sigma0 t s hsigma hden_t hden_ts

/-- THEOREM 2: the minimal producer kernel inherits the same joint
two-coordinate statement for accepted parameters. -/
theorem minimalKernel_yukawa_and_standardModel_gauge_flow
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : M.zeroFree.running.pinned.base.constraints p)
    (y : YukawaParameter)
    (G : RunningSigmaBeta.StandardModelGaugeFactor) (sigma0 t s : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden_t :
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
        sigma0 * t ≠ 0)
    (hden_ts :
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
        sigma0 * (t + s) ≠ 0) :
    p (yukawaSlot y) =
        AffineRelaxation.realDecayRelaxFlow
          (0 : ℝ) (M.yukawaLambda y)
          ((M.zeroFree.running.pinned.yukawaExponent
              M.zeroFree.selectedSeed y : ℝ) * M.yukawaStep y)
          (M.zeroFree.running.pinned.yukawaAmplitude y)
      ∧
    RunningSigmaBeta.standardModelOneLoopSigmaFlow G
        (RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 t) s =
      RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 (t + s) := by
  constructor
  · exact
      M.minimalKernel_accepted_yukawa_eq_sampled_zeroTarget_flow
        p hp y
  · exact
      RunningSigmaBeta.standardModelOneLoopSigmaFlow_add
        G sigma0 t s hsigma hden_t hden_ts

/-! ## Bundled receipt -/

/-- A compact receipt for the two coordinate readings of running sigma:
Yukawa slots use the residual zero-target coordinate, while gauge couplings use
the inverse-coupling affine coordinate. -/
structure UnifiedRunningSigmaCoordinateReceipt : Prop where
  yukawa_generated_zeroTarget :
    ∀ {Seed Scale Index A CKMCarrier : Type*} [AddCommGroup A],
      ∀ C : RunningSigmaStandardModelCertificate
          Seed Scale Index A ℝ CKMCarrier,
      ∀ seed y lambda step,
      C.sigma (C.yukawaScale seed y) =
          AffineRelaxation.realDecayRate lambda step ->
      C.pinned.base.generated seed (yukawaSlot y) =
        AffineRelaxation.realDecayRelaxFlow
          (0 : ℝ) lambda
          ((C.pinned.yukawaExponent seed y : ℝ) * step)
          (C.pinned.yukawaAmplitude y)
  yukawa_generated_residual :
    ∀ {Seed Scale Index A CKMCarrier : Type*} [AddCommGroup A],
      ∀ C : RunningSigmaStandardModelCertificate
          Seed Scale Index A ℝ CKMCarrier,
      ∀ seed y lambda step,
      C.sigma (C.yukawaScale seed y) =
          AffineRelaxation.realDecayRate lambda step ->
      C.pinned.base.generated seed (yukawaSlot y) =
        C.pinned.yukawaAmplitude y *
          AffineRelaxation.realDecayResidual lambda
            ((C.pinned.yukawaExponent seed y : ℝ) * step)
  gauge_inverse_affine :
    ∀ G : RunningSigmaBeta.StandardModelGaugeFactor,
      ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 t =
        (1 : ℝ) / sigma0 +
          (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) * t
  gauge_local_semigroup :
    ∀ G : RunningSigmaBeta.StandardModelGaugeFactor,
      ∀ sigma0 t s : ℝ, sigma0 ≠ 0 ->
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
          sigma0 * t ≠ 0 ->
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
          sigma0 * (t + s) ≠ 0 ->
      RunningSigmaBeta.standardModelOneLoopSigmaFlow G
          (RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 t) s =
        RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 (t + s)
  generated_joint :
    ∀ {Seed Scale Index A CKMCarrier : Type*} [AddCommGroup A],
      ∀ C : RunningSigmaStandardModelCertificate
          Seed Scale Index A ℝ CKMCarrier,
      ∀ seed y lambda step,
      C.sigma (C.yukawaScale seed y) =
          AffineRelaxation.realDecayRate lambda step ->
      ∀ G : RunningSigmaBeta.StandardModelGaugeFactor, ∀ sigma0 t s,
      sigma0 ≠ 0 ->
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
          sigma0 * t ≠ 0 ->
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
          sigma0 * (t + s) ≠ 0 ->
      C.pinned.base.generated seed (yukawaSlot y) =
          AffineRelaxation.realDecayRelaxFlow
            (0 : ℝ) lambda
            ((C.pinned.yukawaExponent seed y : ℝ) * step)
            (C.pinned.yukawaAmplitude y)
        ∧
      RunningSigmaBeta.standardModelOneLoopSigmaFlow G
          (RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 t) s =
        RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 (t + s)
  minimal_kernel_joint :
    ∀ {Index A CKMCarrier : Type*} [AddCommGroup A],
      ∀ M : MinimalGrandUnificationProducerKernel Index A CKMCarrier,
      ∀ p : ParameterVector ℝ,
      M.zeroFree.running.pinned.base.constraints p ->
      ∀ y (G : RunningSigmaBeta.StandardModelGaugeFactor) sigma0 t s,
      sigma0 ≠ 0 ->
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
          sigma0 * t ≠ 0 ->
      1 + (RunningSigmaBeta.standardModelAsymptoticB0 G : ℝ) *
          sigma0 * (t + s) ≠ 0 ->
      p (yukawaSlot y) =
          AffineRelaxation.realDecayRelaxFlow
            (0 : ℝ) (M.yukawaLambda y)
            ((M.zeroFree.running.pinned.yukawaExponent
                M.zeroFree.selectedSeed y : ℝ) * M.yukawaStep y)
            (M.zeroFree.running.pinned.yukawaAmplitude y)
        ∧
      RunningSigmaBeta.standardModelOneLoopSigmaFlow G
          (RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 t) s =
        RunningSigmaBeta.standardModelOneLoopSigmaFlow G sigma0 (t + s)

/-- THEOREM 3: the unified running-sigma coordinate receipt. -/
theorem unifiedRunningSigmaCoordinateReceipt :
    UnifiedRunningSigmaCoordinateReceipt where
  yukawa_generated_zeroTarget :=
    fun C seed y lambda step hsampled =>
      C.generated_yukawa_eq_sampled_zeroTarget_flow
        seed y lambda step hsampled
  yukawa_generated_residual :=
    fun C seed y lambda step hsampled =>
      C.generated_yukawa_eq_sampled_closed_residual
        seed y lambda step hsampled
  gauge_inverse_affine :=
    fun G sigma0 t hsigma =>
      RunningSigmaBeta.standardModelOneLoopSigmaFlow_inverse_linear
        G sigma0 t hsigma
  gauge_local_semigroup :=
    fun G sigma0 t s hsigma hden_t hden_ts =>
      RunningSigmaBeta.standardModelOneLoopSigmaFlow_add
        G sigma0 t s hsigma hden_t hden_ts
  generated_joint :=
    fun C seed y lambda step hsampled G sigma0 t s hsigma hden_t hden_ts =>
      generated_yukawa_and_standardModel_gauge_flow
        C seed y lambda step hsampled G sigma0 t s hsigma hden_t hden_ts
  minimal_kernel_joint :=
    fun M p hp y G sigma0 t s hsigma hden_t hden_ts =>
      minimalKernel_yukawa_and_standardModel_gauge_flow
        M p hp y G sigma0 t s hsigma hden_t hden_ts

end

end StandardModelConstraint
end SaturationMonoid
