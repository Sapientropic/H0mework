/-
  Proposition 274: running sigma as the Standard-Model-facing rate.

  P273 pins a Standard Model constraint slice:

  * theta_QCD = 0;
  * sin²(theta_W) = 3/8 at the declared GUT observable;
  * Yukawa slots have residual-power form A * (1 - sigma)^n.

  This file records the next, more physical, refinement: the sigma in that
  residual-power law is not a fixed constant.  It is a running rate/coupling,
  read at a scale.  The certificate below packages the intended bridge:

  * sigma(scale) is the gauge alpha, g(scale)^2 / fourPi;
  * sigma(M_GUT) is pinned to 0.013 = 13/1000;
  * sigma(M_Z) is pinned to 0.162 = 81/500;
  * the Higgs quartic at the GUT scale is critical/zero and is related, through
    an explicit approximation predicate, to the sigma(1-sigma) critical proxy;
  * the Yukawa residual-power sigma from P273 is the running sigma at the
    Yukawa slot's declared scale.

  Boundary: this is still certificate-relative.  It does not solve the RG beta
  equations, derive the numeric endpoints from data, prove vacuum stability, or
  construct the SU(7) breaking dynamics.  It makes those claims explicit Lean
  fields rather than leaving them as prose.
-/

import Mathlib.Tactic
import H0mework.Physics.SourceContracts.P273

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Nominal running-sigma constants -/

/-- Nominal GUT-scale sigma value: `0.013`. -/
def sigmaGUTNominal (K : Type*) [Field K] : K :=
  (13 : K) / (1000 : K)

/-- Nominal weak-scale sigma value: `0.162`. -/
def sigmaWeakNominal (K : Type*) [Field K] : K :=
  (81 : K) / (500 : K)

/-- The Higgs-critical proxy carried by a running sigma. -/
def sigmaCriticalProxy {K : Type*} [Ring K] (sigma : K) : K :=
  sigma * ((1 : K) - sigma)

/-- Gauge alpha from a coupling and the supplied `4π` carrier value. -/
def alphaFromGaugeCoupling {K : Type*} [Field K] (fourPi coupling : K) : K :=
  coupling ^ (2 : Nat) / fourPi

/-- THEOREM 1: the nominal GUT value is strictly smaller than the nominal
weak-scale value, so a certificate with both endpoints has genuine running. -/
theorem sigmaGUTNominal_lt_sigmaWeakNominal
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    sigmaGUTNominal K < sigmaWeakNominal K := by
  norm_num [sigmaGUTNominal, sigmaWeakNominal]

/-- THEOREM 2: the two nominal endpoint values are not equal. -/
theorem sigmaGUTNominal_ne_sigmaWeakNominal
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    sigmaGUTNominal K ≠ sigmaWeakNominal K :=
  ne_of_lt (sigmaGUTNominal_lt_sigmaWeakNominal K)

/-- THEOREM 3: the nominal GUT critical proxy is exactly
`13/1000 * 987/1000 = 12831/1000000`. -/
theorem sigmaCriticalProxy_gutNominal_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    sigmaCriticalProxy (sigmaGUTNominal K) =
      (12831 : K) / (1000000 : K) := by
  norm_num [sigmaCriticalProxy, sigmaGUTNominal]

/-! ## Running-sigma Standard Model certificate -/

/-- A running-sigma strengthening of P273's pinned Standard Model certificate.

The approximation relation is deliberately a field of the certificate.  That
keeps the statement honest: `lambda(M_GUT) ≈ sigma(1-sigma)` is not an equality
in the algebraic carrier, so the chosen tolerance/metric must be supplied by
the physical instance. -/
structure RunningSigmaStandardModelCertificate
    (Seed Scale Index A K CKMCarrier : Type*) [AddCommGroup A]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  pinned :
    PinnedStandardModelConstraintCertificate
      Seed Scale Index A K CKMCarrier
  gutScale : Scale
  weakScale : Scale
  sigma : Scale -> K
  gaugeCoupling : Scale -> K
  fourPi : K
  sigma_eq_alpha :
    ∀ scale, sigma scale =
      alphaFromGaugeCoupling fourPi (gaugeCoupling scale)
  sigma_gut_nominal :
    sigma gutScale = sigmaGUTNominal K
  sigma_weak_nominal :
    sigma weakScale = sigmaWeakNominal K
  higgsLambdaAtGUT : Seed -> K
  higgsLambdaAtGUT_eq_rg_slot :
    ∀ seed,
      higgsLambdaAtGUT seed =
        pinned.base.rg.evolve gutScale (pinned.base.generated seed)
          StandardModelParameter.higgs_lambda
  higgsLambdaAtGUT_zero :
    ∀ seed, higgsLambdaAtGUT seed = 0
  approx : K -> K -> Prop
  higgsLambdaAtGUT_near_sigmaCriticalProxy :
    ∀ seed,
      approx (higgsLambdaAtGUT seed)
        (sigmaCriticalProxy (sigma gutScale))
  yukawaScale : Seed -> YukawaParameter -> Scale
  yukawaSigma_is_runningSigma :
    ∀ seed y,
      pinned.yukawaSigma seed y = sigma (yukawaScale seed y)

namespace RunningSigmaStandardModelCertificate

variable {Seed Scale Index A K CKMCarrier : Type*}
variable [AddCommGroup A] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 4: sigma is gauge alpha at the GUT scale. -/
theorem gut_sigma_eq_alpha
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier) :
    C.sigma C.gutScale =
      alphaFromGaugeCoupling C.fourPi (C.gaugeCoupling C.gutScale) :=
  C.sigma_eq_alpha C.gutScale

/-- THEOREM 5: sigma is gauge alpha at the weak scale. -/
theorem weak_sigma_eq_alpha
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier) :
    C.sigma C.weakScale =
      alphaFromGaugeCoupling C.fourPi (C.gaugeCoupling C.weakScale) :=
  C.sigma_eq_alpha C.weakScale

/-- THEOREM 6: the GUT endpoint is pinned to `0.013`. -/
theorem gut_sigma_nominal
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier) :
    C.sigma C.gutScale = sigmaGUTNominal K :=
  C.sigma_gut_nominal

/-- THEOREM 7: the weak endpoint is pinned to `0.162`. -/
theorem weak_sigma_nominal
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier) :
    C.sigma C.weakScale = sigmaWeakNominal K :=
  C.sigma_weak_nominal

/-- THEOREM 8: the pinned endpoints force nontrivial running of sigma. -/
theorem sigma_runs_between_gut_and_weak
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier) :
    C.sigma C.gutScale ≠ C.sigma C.weakScale := by
  rw [C.sigma_gut_nominal, C.sigma_weak_nominal]
  exact sigmaGUTNominal_ne_sigmaWeakNominal K

/-- THEOREM 9: the pinned endpoints force the declared GUT and weak scales
to be distinct. -/
theorem gutScale_ne_weakScale
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier) :
    C.gutScale ≠ C.weakScale := by
  intro h
  apply C.sigma_runs_between_gut_and_weak
  rw [h]

/-- THEOREM 10: the GUT Higgs quartic is pinned to the critical value zero. -/
theorem higgsLambdaAtGUT_is_zero
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) :
    C.higgsLambdaAtGUT seed = 0 :=
  C.higgsLambdaAtGUT_zero seed

/-- THEOREM 11: the GUT Higgs quartic is related by the supplied approximation
predicate to `sigma(M_GUT) * (1 - sigma(M_GUT))`. -/
theorem higgsLambdaAtGUT_approx_sigmaCriticalProxy
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) :
    C.approx (C.higgsLambdaAtGUT seed)
      (sigmaCriticalProxy (C.sigma C.gutScale)) :=
  C.higgsLambdaAtGUT_near_sigmaCriticalProxy seed

/-- THEOREM 12: generated Yukawa slots use the running sigma at the slot's
declared scale. -/
theorem generated_yukawa_residual_power_running_sigma
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) (y : YukawaParameter) :
    C.pinned.base.generated seed (yukawaSlot y) =
      C.pinned.yukawaAmplitude y *
        (((1 : K) - C.sigma (C.yukawaScale seed y)) ^
          C.pinned.yukawaExponent seed y) := by
  rw [← C.yukawaSigma_is_runningSigma seed y]
  exact C.pinned.yukawa_residual_power seed y

/-- THEOREM 13: the running-sigma certificate inherits P273's `theta_QCD=0`
pin. -/
theorem generated_thetaQCD_zero
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) :
    C.pinned.base.generated seed StandardModelParameter.qcd_theta = 0 :=
  C.pinned.thetaQCD_zero seed

/-- THEOREM 14: the running-sigma certificate inherits P273's GUT weak-mixing
pin `sin²(theta_W)=3/8`. -/
theorem generated_gutWeakMixingSquared_eq_threeEighths
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) :
    C.pinned.gutWeakMixingSquared (C.pinned.base.generated seed) =
      threeEighths K :=
  C.pinned.gutWeakMixingSquared_eq_threeEighths seed

end RunningSigmaStandardModelCertificate

end StandardModelConstraint
end SaturationMonoid
