import H0mework.Physics.MatterJets.StageEightMatterFirstJetTransportNoGo
import H0mework.Realization.Residual.Process

/-!
# S9-C3h15: source matter first-jet residual orbit

C3h14 rejects keeping the actual Stage-8 finite matter jet statically
identified with the Stage-9 first jet at both endpoints.  This module derives
the minimal pointwise repair from the framework root: the same source keep
transports that actual first-jet seed, `j_(n+1) = K j_n`.

The carrier is the existing matter first-jet function type, not a new field or
source slot.  Its keep is active, SU(7)-equivariant, and packaged as an
`EffectiveResidualProcess`; the complementary trace is unique and nonzero at
every finite step, so responsibility has no third sink.  A downstream
holonomic configuration may read a transported jet through an explicit
realization predicate, but that predicate manufactures neither a germ nor a
stationarity receipt.

For any actual configuration update realizing consecutive orbit jets, the
whole conjugate-matter residual covector obeys the same `r' = K r` law and that
complete coordinate of `D_U` vanishes.  This is one positive Euler--Lagrange
coordinate, not a claim that the other eight joint coordinates or local
integrability are already closed.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceMatterFirstJetResidualOrbit

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageEightSourceGeneratedMatter
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNineJointStateLiftDefect
open StageNineConjugateMatterVariation
open StageNineMatterVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineStageEightMatterFirstJetTransportNoGo
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open DiracCliffordRepresentation
open SU7ExteriorMatterRepresentation
open ResidualProjection

noncomputable section

set_option autoImplicit false

/-- Actual Stage-8 finite-link difference, retained only as the initial
first-jet residual seed. -/
def positiveSourceMatterFirstJetSeed :
    LorentzianIndex → DiracExteriorMatterCarrier :=
  fun direction =>
    (sourceGeneratedMatterJet canonicalSource).targetField direction -
      (sourceGeneratedMatterJet canonicalSource).sourceField

/-- The existing source sigma acts on the complex matter representation by
its canonical real embedding. -/
def positiveSourceMatterFirstJetKeep :
    (LorentzianIndex → DiracExteriorMatterCarrier) →ₗ[ℂ]
      (LorentzianIndex → DiracExteriorMatterCarrier) :=
  scalarKeepLinearMap (positiveSmoothUnifiedSource.legacy.sigma : ℂ)

def positiveSourceMatterFirstJetOrbit
    (n : ℕ) : LorentzianIndex → DiracExteriorMatterCarrier :=
  (((1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n : ℝ) : ℂ) •
    positiveSourceMatterFirstJetSeed

@[simp] theorem positiveSourceMatterFirstJetOrbit_zero :
    positiveSourceMatterFirstJetOrbit 0 = positiveSourceMatterFirstJetSeed := by
  simp [positiveSourceMatterFirstJetOrbit]

/-- Literal first formula on the derived first-jet orbit. -/
theorem positiveSourceMatterFirstJetOrbit_succ (n : ℕ) :
    positiveSourceMatterFirstJetOrbit (n + 1) =
      positiveSourceMatterFirstJetKeep
        (positiveSourceMatterFirstJetOrbit n) := by
  funext direction
  simp only [positiveSourceMatterFirstJetOrbit,
    positiveSourceMatterFirstJetKeep, scalarKeepLinearMap, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, Pi.smul_apply]
  rw [pow_succ]
  push_cast
  module

theorem positiveSourceMatterFirstJetKeep_active :
    ResidualTransportActive positiveSourceMatterFirstJetKeep := by
  apply scalarKeepLinearMap_active_of_ne_zero
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos)

theorem positiveSourceMatterFirstJetSeed_ne_zero :
    positiveSourceMatterFirstJetSeed ≠ 0 := by
  intro seedZero
  have atDirectionZero := congrFun seedZero 0
  have probeZero : diracSpinTwoMatterProbe = 0 := by
    simpa [positiveSourceMatterFirstJetSeed, sourceGeneratedMatterJet,
      sourceMatterAmplitude] using atDirectionZero
  exact diracSpinTwoMatterProbe_nonzero probeZero

/-- No finite transported first jet is a terminal sink. -/
theorem positiveSourceMatterFirstJetOrbit_ne_zero (n : ℕ) :
    positiveSourceMatterFirstJetOrbit n ≠ 0 := by
  unfold positiveSourceMatterFirstJetOrbit
  apply smul_ne_zero _ positiveSourceMatterFirstJetSeed_ne_zero
  exact Complex.ofReal_ne_zero.mpr
    (pow_ne_zero n (sub_ne_zero.mpr
      (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_lt_one)))

/-- Scalar residual transport commutes with the actual SU(7) matter
representation; the repair is not tied to a hidden gauge branch. -/
theorem positiveSourceMatterFirstJetKeep_gaugeEquivariant
    (gauge : SU7MotherGroup)
    (jet : LorentzianIndex → DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    diracExteriorMatterGaugeRepresentation gauge
        (positiveSourceMatterFirstJetKeep jet direction) =
      positiveSourceMatterFirstJetKeep
        (fun candidate =>
          diracExteriorMatterGaugeRepresentation gauge (jet candidate))
        direction := by
  simp [positiveSourceMatterFirstJetKeep, scalarKeepLinearMap]

def positiveSourceMatterFirstJetTrace
    (jet : LorentzianIndex → DiracExteriorMatterCarrier) :
    LorentzianIndex → DiracExteriorMatterCarrier :=
  linearResidualTrace positiveSourceMatterFirstJetKeep jet

theorem positiveSourceMatterFirstJet_split
    (jet : LorentzianIndex → DiracExteriorMatterCarrier) :
    jet = positiveSourceMatterFirstJetKeep jet +
      positiveSourceMatterFirstJetTrace jet := by
  exact residualTransportCore_residual_split positiveSourceMatterFirstJetKeep jet

theorem positiveSourceMatterFirstJetTrace_eq_sourceSigma
    (jet : LorentzianIndex → DiracExteriorMatterCarrier) :
    positiveSourceMatterFirstJetTrace jet =
      (positiveSmoothUnifiedSource.legacy.sigma : ℂ) • jet := by
  exact residualTransportCore_scalar_trace
    (positiveSmoothUnifiedSource.legacy.sigma : ℂ) jet

theorem positiveSourceMatterFirstJetTrace_unique
    (jet trace : LorentzianIndex → DiracExteriorMatterCarrier) :
    jet = positiveSourceMatterFirstJetKeep jet + trace ↔
      trace = positiveSourceMatterFirstJetTrace jet := by
  exact residualTransportCore_trace_unique
    positiveSourceMatterFirstJetKeep jet trace

/-- Faithful transport leaves a nonzero forced responsibility at every finite
orbit step; it cannot disappear into a third sink. -/
theorem positiveSourceMatterFirstJetOrbit_trace_ne_zero (n : ℕ) :
    positiveSourceMatterFirstJetTrace
        (positiveSourceMatterFirstJetOrbit n) ≠ 0 := by
  rw [positiveSourceMatterFirstJetTrace_eq_sourceSigma]
  exact smul_ne_zero
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos))
    (positiveSourceMatterFirstJetOrbit_ne_zero n)

/-- Framework-native process on the derived first-jet carrier.  It does not
claim that a holonomic configuration lift already exists. -/
def positiveSourceMatterFirstJetEffectiveResidualProcess :
    EffectiveResidualProcess ℂ
      (LorentzianIndex → DiracExteriorMatterCarrier)
      (LorentzianIndex → DiracExteriorMatterCarrier) where
  target := 0
  keep := positiveSourceMatterFirstJetKeep
  residual := id
  update := positiveSourceMatterFirstJetKeep
  residual_transport_law := fun _ => rfl

/-- Actual holonomic configurations may only read the transported first jet;
this predicate does not manufacture a germ or stationarity receipt. -/
structure RealizesPositiveSourceMatterFirstJetOrbitAtOrigin
    (n : ℕ) (configuration : StageNineHolonomicConfiguration) : Prop where
  coframeOrigin : configuration.coframe 0 = 1
  matterOrigin : configuration.matter 0 =
    (sourceGeneratedMatterJet canonicalSource).sourceField
  matterFirstJet : ∀ direction : LorentzianIndex,
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (configuration.matter point))
        0 direction =
      matterCoordinateEquiv (positiveSourceMatterFirstJetOrbit n direction)

theorem realizingOrbit_matterCovariantDerivative_origin
    (n : ℕ) (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative configuration 0 direction =
      positiveSourceMatterFirstJetOrbit n direction := by
  unfold holonomicMatterCovariantDerivative
  rw [realizes.matterOrigin, realizes.matterFirstJet]
  simp [sourceGeneratedMatterJet]

theorem realizingOrbit_generatedContinuumMatterVector_origin
    (n : ℕ) (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration) :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField configuration 0) =
      (((1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n : ℝ) : ℂ) •
        (Complex.I • diracSpinZeroMatterProbe) := by
  unfold generatedContinuumMatterVector
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart, matterFrameRelative_zeroChart]
  rw [realizes.coframeOrigin]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl]
  simp_rw [realizingOrbit_matterCovariantDerivative_origin
    n configuration realizes]
  rw [realizes.matterOrigin]
  simp [positiveSourceMatterFirstJetOrbit,
    positiveSourceMatterFirstJetSeed, positiveSmoothUnifiedSource,
    sourceGeneratedMatterJet, sourceMatterAmplitude,
    inverseCoframeDiracGamma_identity, Fin.sum_univ_four, diracGamma,
    show (1 : LorentzianIndex) ≠ 0 by decide,
    show (2 : LorentzianIndex) ≠ 0 by decide,
    show (3 : LorentzianIndex) ≠ 0 by decide,
    diracGammaZero_maps_spinTwoProbe]
  module

theorem realizingOrbit_conjugateResidual_origin
    (n : ℕ) (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration) :
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        configuration positiveFirstJetConjugateResidualProbeDirection 0 =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n := by
  unfold conjugateMatterDirectionalCoefficient
  rw [realizingOrbit_generatedContinuumMatterVector_origin
    n configuration realizes]
  unfold positiveFirstJetConjugateResidualProbeDirection
  rw [matterDualOfCoordinates_surjective]
  simp [generatedVolumeDensity, toContinuumPointField,
    realizes.coframeOrigin]
  have castPow :
      ((((1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n : ℝ) : ℂ)) =
        (1 - (positiveSmoothUnifiedSource.legacy.sigma : ℂ)) ^ n := by
    simpa using (Complex.ofReal_pow
      (1 - positiveSmoothUnifiedSource.legacy.sigma) n)
  exact (congrArg Complex.re castPow).symm.trans
    (Complex.ofReal_re
      ((1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n))

/-- The actual conjugate-matter residual readout transports at the same
source-generated rate whenever two configurations realize consecutive jets. -/
theorem realizingOrbit_conjugateResidual_transport
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialRealizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n initial)
    (terminalRealizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin (n + 1) terminal) :
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        terminal positiveFirstJetConjugateResidualProbeDirection 0 =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) *
        conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
          initial positiveFirstJetConjugateResidualProbeDirection 0 := by
  rw [realizingOrbit_conjugateResidual_origin (n + 1) terminal terminalRealizes,
    realizingOrbit_conjugateResidual_origin n initial initialRealizes,
    pow_succ]
  ring

/-- The transport law holds for the complete conjugate-matter residual
covector, not merely the distinguished nonzero regression probe. -/
theorem realizingOrbit_conjugateResidual_transport_allDirections
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialRealizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n initial)
    (terminalRealizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin (n + 1) terminal)
    (direction : MatterCoordinateCarrier) :
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        terminal direction 0 =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) *
        conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
          initial direction 0 := by
  unfold conjugateMatterDirectionalCoefficient
  rw [realizingOrbit_generatedContinuumMatterVector_origin
        (n + 1) terminal terminalRealizes,
      realizingOrbit_generatedContinuumMatterVector_origin
        n initial initialRealizes]
  simp [generatedVolumeDensity, toContinuumPointField,
    terminalRealizes.coframeOrigin, initialRealizes.coframeOrigin,
    pow_succ, Complex.mul_re]
  ring

/-- When an actual configuration update realizes consecutive derived jets,
the corresponding conjugate-matter coordinate of `D_U` is exactly zero.  No
claim is made about the other eight coordinates. -/
theorem realizingOrbit_conjugateLiftDefect_eq_zero
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialRealizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n initial)
    (terminalRealizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
        initial) 0).eulerLagrange.conjugateMatter
          positiveFirstJetConjugateResidualProbeDirection = 0 := by
  change
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
          (update initial) positiveFirstJetConjugateResidualProbeDirection 0 -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) *
          conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
            initial positiveFirstJetConjugateResidualProbeDirection 0 = 0
  rw [updateInitial]
  exact sub_eq_zero.mpr
    (realizingOrbit_conjugateResidual_transport n initial terminal
      initialRealizes terminalRealizes)

/-- An actual update between consecutive realizers closes the entire
conjugate-matter coordinate of `D_U`.  The realization and update remain
explicit conditions; this theorem does not generate either endpoint. -/
theorem realizingOrbit_conjugateLiftDefect_eq_zero_allDirections
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialRealizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n initial)
    (terminalRealizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
        initial) 0).eulerLagrange.conjugateMatter = 0 := by
  funext direction
  change
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
          (update initial) direction 0 -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) *
          conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
            initial direction 0 = 0
  rw [updateInitial]
  exact sub_eq_zero.mpr
    (realizingOrbit_conjugateResidual_transport_allDirections
      n initial terminal initialRealizes terminalRealizes direction)

end

end SaturationMonoid.PhysicsCore.StageNineSourceMatterFirstJetResidualOrbit
