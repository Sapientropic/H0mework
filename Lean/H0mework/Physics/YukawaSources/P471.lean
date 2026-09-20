/-
  Proposition 471: running-sigma Yukawa slots are sampled zero-target flows.

  P275 proves the Yukawa residual-power law is a zero-target finite relaxation
  iterate.  P293 proves that a finite sampled-rate iterate is exactly the
  continuous fixed-target flow at sampled total time.  P468/P467 then put the
  same law in the one-target/complement language.

  This file makes the pointwise bridge explicit for the actual running-sigma
  Standard-Model certificate:

      if sigma(scale_y) = realDecayRate lambda step,
      then Yukawa_y = realDecayRelaxFlow 0 lambda (n_y * step) A_y

  and equivalently

      Yukawa_y = A_y * realDecayResidual lambda (n_y * step).

  Boundary: this still does not construct the physical clock maps `lambda` and
  `step`.  It proves that once a clock samples the running sigma, the Yukawa
  slot is not a separate ansatz; it is the same zero-target sampled flow.
-/

import H0mework.Realization.Claims.P470
import H0mework.Physics.JointSources.P376

namespace SaturationMonoid
namespace StandardModelConstraint

namespace RunningSigmaStandardModelCertificate

variable {Seed Scale Index A CKMCarrier : Type*}
variable [AddCommGroup A]

/-- THEOREM 1: if a Yukawa slot's running sigma is sampled from a continuous
decay envelope, the generated slot is exactly the zero-target sampled flow. -/
theorem generated_yukawa_eq_sampled_zeroTarget_flow
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A ℝ CKMCarrier)
    (seed : Seed) (y : YukawaParameter)
    (lambda step : ℝ)
    (hsampled :
      C.sigma (C.yukawaScale seed y) =
        AffineRelaxation.realDecayRate lambda step) :
    C.pinned.base.generated seed (yukawaSlot y) =
      AffineRelaxation.realDecayRelaxFlow
        (0 : ℝ) lambda
        ((C.pinned.yukawaExponent seed y : ℝ) * step)
        (C.pinned.yukawaAmplitude y) := by
  rw [C.generated_yukawa_eq_zeroTarget_relaxation_iterate seed y]
  rw [hsampled]
  exact
    AffineRelaxation.relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow
      (target := (0 : ℝ)) lambda step
      (C.pinned.yukawaAmplitude y)
      (C.pinned.yukawaExponent seed y)

/-- THEOREM 2: the same sampled-flow presentation has the closed residual
form. -/
theorem generated_yukawa_eq_sampled_closed_residual
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A ℝ CKMCarrier)
    (seed : Seed) (y : YukawaParameter)
    (lambda step : ℝ)
    (hsampled :
      C.sigma (C.yukawaScale seed y) =
        AffineRelaxation.realDecayRate lambda step) :
    C.pinned.base.generated seed (yukawaSlot y) =
      C.pinned.yukawaAmplitude y *
        AffineRelaxation.realDecayResidual lambda
          ((C.pinned.yukawaExponent seed y : ℝ) * step) := by
  rw [C.generated_yukawa_eq_sampled_zeroTarget_flow seed y lambda step hsampled]
  rw [AffineRelaxation.realDecayRelaxFlow_eq_closed]
  ring

end RunningSigmaStandardModelCertificate

namespace ZeroContinuousFreeStandardModelCertificate

variable {Index A CKMCarrier : Type*}
variable [AddCommGroup A]

/-- THEOREM 3: a zero-free certificate plus sampled discrete Yukawa clocks
turns every accepted Yukawa slot into the zero-target sampled flow. -/
theorem accepted_yukawa_eq_sampled_zeroTarget_flow_discrete_scale
    (C : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : C.running.pinned.base.constraints p)
    (y : YukawaParameter)
    (yukawaLambda yukawaStep : YukawaParameter -> ℝ)
    (hsampled :
      ∀ y : YukawaParameter,
        C.running.sigma (StandardModelScaleCode.yukawa y) =
          AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)) :
    p (yukawaSlot y) =
      AffineRelaxation.realDecayRelaxFlow
        (0 : ℝ) (yukawaLambda y)
        ((C.running.pinned.yukawaExponent C.selectedSeed y : ℝ) *
          yukawaStep y)
        (C.running.pinned.yukawaAmplitude y) := by
  rw [C.accepted_solution_eq_selected_generated p hp]
  have hslot :
      C.running.sigma (C.running.yukawaScale C.selectedSeed y) =
        AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y) := by
    rw [C.selected_yukawaScale_eq_discrete_code y]
    exact hsampled y
  exact
    C.running.generated_yukawa_eq_sampled_zeroTarget_flow
      C.selectedSeed y (yukawaLambda y) (yukawaStep y) hslot

/-- THEOREM 4: accepted sampled Yukawa slots also have the closed continuous
residual form. -/
theorem accepted_yukawa_eq_sampled_closed_residual_discrete_scale
    (C : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : C.running.pinned.base.constraints p)
    (y : YukawaParameter)
    (yukawaLambda yukawaStep : YukawaParameter -> ℝ)
    (hsampled :
      ∀ y : YukawaParameter,
        C.running.sigma (StandardModelScaleCode.yukawa y) =
          AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)) :
    p (yukawaSlot y) =
      C.running.pinned.yukawaAmplitude y *
        AffineRelaxation.realDecayResidual (yukawaLambda y)
          ((C.running.pinned.yukawaExponent C.selectedSeed y : ℝ) *
            yukawaStep y) := by
  rw [C.accepted_yukawa_eq_sampled_zeroTarget_flow_discrete_scale
    p hp y yukawaLambda yukawaStep hsampled]
  rw [AffineRelaxation.realDecayRelaxFlow_eq_closed]
  ring

end ZeroContinuousFreeStandardModelCertificate

namespace MinimalGrandUnificationProducerKernel

variable {Index A CKMCarrier : Type*}
variable [AddCommGroup A]

/-- THEOREM 5: the minimal producer kernel's sampled Yukawa clock directly
gives the accepted zero-target sampled-flow law. -/
theorem minimalKernel_accepted_yukawa_eq_sampled_zeroTarget_flow
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : M.zeroFree.running.pinned.base.constraints p)
    (y : YukawaParameter) :
    p (yukawaSlot y) =
      AffineRelaxation.realDecayRelaxFlow
        (0 : ℝ) (M.yukawaLambda y)
        ((M.zeroFree.running.pinned.yukawaExponent M.zeroFree.selectedSeed y : ℝ) *
          M.yukawaStep y)
        (M.zeroFree.running.pinned.yukawaAmplitude y) := by
  exact
    M.zeroFree.accepted_yukawa_eq_sampled_zeroTarget_flow_discrete_scale
      p hp y M.yukawaLambda M.yukawaStep
      M.selected_yukawa_sigma_sampled

/-- THEOREM 6: the minimal producer kernel's existing continuous residual
statement follows from the pointwise sampled-flow bridge. -/
theorem minimalKernel_accepted_yukawa_eq_sampled_closed_residual
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : M.zeroFree.running.pinned.base.constraints p)
    (y : YukawaParameter) :
    p (yukawaSlot y) =
      M.zeroFree.running.pinned.yukawaAmplitude y *
        AffineRelaxation.realDecayResidual (M.yukawaLambda y)
          ((M.zeroFree.running.pinned.yukawaExponent
              M.zeroFree.selectedSeed y : ℝ) * M.yukawaStep y) := by
  exact
    M.zeroFree.accepted_yukawa_eq_sampled_closed_residual_discrete_scale
      p hp y M.yukawaLambda M.yukawaStep
      M.selected_yukawa_sigma_sampled

end MinimalGrandUnificationProducerKernel

/-! ## Bundled receipt -/

/-- A reusable receipt for the sampled running-sigma Yukawa bridge. -/
structure SampledRunningSigmaYukawaFlowReceipt : Prop where
  running_flow :
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
  running_residual :
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

/-- THEOREM 7: the sampled running-sigma Yukawa bridge receipt. -/
theorem sampledRunningSigmaYukawaFlowReceipt :
    SampledRunningSigmaYukawaFlowReceipt where
  running_flow :=
    fun C seed y lambda step hsampled =>
      C.generated_yukawa_eq_sampled_zeroTarget_flow
        seed y lambda step hsampled
  running_residual :=
    fun C seed y lambda step hsampled =>
      C.generated_yukawa_eq_sampled_closed_residual
        seed y lambda step hsampled

end StandardModelConstraint
end SaturationMonoid
