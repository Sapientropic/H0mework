import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ThreePortTransfer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionXiEscape

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryXiSlot

open Complex Filter BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped Topology

open private right_quarter below_half adjoint_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private coordinate_eq from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
open private bare_factor bare_analytic bare_nonzero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
open private coefficient_analytic from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.Source
open private seed_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial

namespace Germ
export AdjointGerm
  (probe probe_zero probe_continuous denominator denominator_continuous denominator_nonzero factor factor_read actual_adjoint_germ_exit)
end Germ
namespace Source
export DivisionXiEscape (actual_division_ambient_price)
export OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial (sourceIndex actual_raw_field actual_iterate_even)
end Source

local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "KConj" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "T" => sourceCayley
local notation "R" => burnolDirectRightResolventCLM
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner

theorem conjugate_twice (d : BurnolCompletedMellinCoordinate) : KConj (KConj d) = d := by
  apply coordinate_eq
  change star (star d.value) = d.value
  exact star_star _

private theorem chart (d : BurnolCompletedMellinCoordinate) :
    burnolDivisionCompletedMellinCoordinate (d.value/2) (right_quarter d) (below_half d) = d := by
  apply coordinate_eq
  change 2*(d.value/2) = d.value
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => KConj c
local notation "p" => Germ.probe a
local notation "m" => order observation.coordinate
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

private theorem probe_center : p 0 = c := (Germ.probe_zero a).trans (conjugate_twice c)

private theorem raw_gap (ordinal : Nat) : raw ordinal ∈ G :=
  OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal

private theorem raw_even (ordinal : Nat) : reflectL2 (raw ordinal) = raw ordinal := by
  rw [Source.actual_raw_field observation nontrivial half]
  exact Source.actual_iterate_even c _ seed_even _

/-- The original forward material has zero price at its own Xi coordinate. -/
theorem literal_silent (ordinal : Nat) : M c (raw ordinal) = 0 := by
  have price := Source.actual_division_ambient_price observation nontrivial half depth ordinal
    ((c).value/2) (right_quarter c) (below_half c)
  rw [chart c, show 2*((c).value/2) = observation.coordinate by
    change 2*(observation.coordinate/2) = observation.coordinate
    ring, observation.mathlibZero, zero_mul, mul_zero] at price
  exact price

private theorem forward_step (parameter : BurnolCompletedMellinCoordinate) (point : BurnolL2)
    (gap : point ∈ G) (silent : M c point = 0) :
    R parameter point ∈ G ∧ M c (R parameter point) = 0 := by
  have read := CombSource.Pricing.ambient_R_scalar_action (parameter.value/2) (right_quarter parameter)
    point gap ((c).value/2) (right_quarter c) (below_half c)
  rw [chart c, silent, mul_zero] at read
  exact ⟨CombSource.Pricing.ambient_R_positionGap _ (right_quarter parameter) point gap, read⟩

/-- Changing the original R parameter still leaves the source's own Xi observation silent. -/
theorem transfer_silent (parameter : BurnolCompletedMellinCoordinate) (ordinal : Nat) :
    M c (ThreePortTransfer.parameterField observation nontrivial half depth parameter ordinal) = 0 := by
  rw [ThreePortTransfer.actual_parameter_field observation nontrivial half depth]
  exact (forward_step observation half parameter (raw ordinal)
    (raw_gap observation nontrivial half depth ordinal)
    (literal_silent observation nontrivial half depth ordinal)).2

/-- The chosen ordered actions are executed on the literal original cofinal input. -/
def forwardWord (ordinal : Nat) (parameters : List BurnolCompletedMellinCoordinate) : BurnolL2 :=
  parameters.foldr (fun parameter value => R parameter value) (raw ordinal)

theorem forward_word_law (ordinal : Nat) (parameters : List BurnolCompletedMellinCoordinate) :
    let field := forwardWord observation nontrivial half depth ordinal parameters
    field ∈ G ∧ M c field = 0 := by
  induction parameters with
  | nil => exact ⟨raw_gap observation nontrivial half depth ordinal,
      literal_silent observation nontrivial half depth ordinal⟩
  | cons parameter tail previous =>
    exact forward_step observation half parameter _ previous.1 previous.2

private def denominator (t : ℝ) : ℂ := (c).value/2+(p t).value/2-1/2

local notation "den" => denominator observation half

private theorem den_nonzero (t : ℝ) : den t ≠ 0 := by
  have positive : 0 < (den t).re := by
    simp only [denominator, Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith [(c).rightHalf, (p t).rightHalf]
  exact fun zero => (not_lt_of_ge (le_of_eq (congrArg Complex.re zero))) positive

private def leading (ordinal : Nat) (t : ℝ) : ℂ :=
  (-(1/den t))^(Source.sourceIndex observation ordinal) * ((2:ℂ)*Germ.denominator a t)^m *
    (bare (c).value (p t).value * burnolPaCombResponseCoefficient (1-(p t).value) 0)

local notation "head" => leading observation half

private theorem leading_continuous (ordinal : Nat) : ContinuousAt (head ordinal) 0 := by
  have denContinuous : Continuous den :=
    (continuous_const.add ((Germ.probe_continuous a).div_const (2:ℂ))).sub continuous_const
  have native : ContinuousAt (fun t : ℝ => -(1/den t)) 0 :=
    (continuousAt_const.div denContinuous.continuousAt (den_nonzero observation half 0)).neg
  have factor : ContinuousAt (fun t : ℝ => (2:ℂ)*Germ.denominator a t) 0 :=
    continuousAt_const.mul (Germ.denominator_continuous a).continuousAt
  have bareAt : ContinuousAt (bare (c).value) (p 0).value := by
    simpa only [probe_center observation half] using (bare_analytic c).continuousAt
  have bareCont := ContinuousAt.comp' (f := fun t => (p t).value) bareAt
    (Germ.probe_continuous a).continuousAt
  let w (t : ℝ) := (p t).value/2
  have shape : ContinuousAt w 0 := (Germ.probe_continuous a).continuousAt.div_const (2:ℂ)
  have inside : w 0 ∈ burnolPhysicalHeatMellinStrip :=
    ⟨lt_trans (by norm_num) (right_quarter (p 0)), below_half (p 0)⟩
  have response := ((coefficient_analytic 0 (w 0) inside).continuousAt.comp shape)
  have responseAt : ContinuousAt (fun t => burnolPaCombResponseCoefficient (1-(p t).value) 0) 0 := by
    have align (t : ℝ) : 1-2*w t = 1-(p t).value := by
      dsimp only [w]
      ring
    simpa only [Function.comp_def, align] using response
  exact ((native.pow _).mul (factor.pow _)).mul (bareCont.mul responseAt)

private theorem leading_live (ordinal : Nat) : head ordinal 0 ≠ 0 := by
  have nonzero := den_nonzero observation half 0
  have first := pow_ne_zero (Source.sourceIndex observation ordinal)
    (neg_ne_zero.mpr (div_ne_zero one_ne_zero nonzero))
  have second := pow_ne_zero m (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (Germ.denominator_nonzero a 0))
  have response := burnolPaCombResponseCoefficient_ne_zero (1-(c).value)
    (by rw [Complex.sub_re, Complex.one_re]; linarith [(c).belowOne]) 0
  simpa only [leading, probe_center observation half] using
    (mul_ne_zero (mul_ne_zero first second) (mul_ne_zero (bare_nonzero c) response))

private theorem actual_germ (ordinal : Nat) :
    (fun t => M (p t) (raw ordinal)) =ᶠ[𝓝 (0:ℝ)]
      fun t => (Germ.factor a t)^m * head ordinal t := by
  have toward : Tendsto (fun t => (p t).value) (𝓝 (0:ℝ)) (𝓝 (c).value) := by
    have nearby : Tendsto (fun t => (p t).value) (𝓝 (0:ℝ)) (𝓝 (p 0).value) :=
      (Germ.probe_continuous a).continuousAt
    rw [probe_center observation half] at nearby
    exact nearby
  filter_upwards [toward.eventually (bare_factor c)] with t zeta
  let d := p t
  let w := d.value/2
  have scale : 2*w = d.value := by dsimp only [w]; ring
  have written := Source.actual_division_ambient_price observation nontrivial half depth ordinal
    w (right_quarter d) (below_half d)
  rw [chart d, scale] at written
  change M d (raw ordinal) = (-(1/den t))^(Source.sourceIndex observation ordinal) *
    (riemannZeta d.value * burnolPaCombResponseCoefficient (1-d.value) 0) at written
  change riemannZeta d.value = (d.value-(c).value)^m * bare (c).value d.value at zeta
  have anchor : star (a).value = (c).value :=
    congrArg BurnolCompletedMellinCoordinate.value (conjugate_twice c)
  have factorized : d.value-(c).value = Germ.factor a t * (2*Germ.denominator a t) := by
    calc
      _ = (t:ℂ)*Complex.I := by
        change star (a).value+(t:ℂ)*Complex.I-(c).value = _
        rw [anchor]
        ring
      _ = 2*(Germ.factor a t*Germ.denominator a t) := by
        rw [Germ.factor_read, div_mul_cancel₀ _ (Germ.denominator_nonzero a t)]
        ring
      _ = _ := by ring
  change M d (raw ordinal) = (Germ.factor a t)^m * head ordinal t
  rw [written, zeta, factorized, mul_pow, leading]
  dsimp only [d]
  ring

/-- The true conjugate-parameter adjoint acts on the complete retained field. -/
def slot (ordinal : Nat) : BurnolL2 :=
  (((T a).adjoint)^m) (ThreePortCausal.field observation nontrivial half depth ordinal 0)

theorem actual_slot (ordinal : Nat) :
    (∀ j < m, M c ((((T a).adjoint)^j) (ThreePortCausal.field observation nontrivial half depth ordinal 0)) = 0) ∧
    slot observation nontrivial half depth ordinal ∈ G ∧
    reflectL2 (slot observation nontrivial half depth ordinal) = slot observation nontrivial half depth ordinal ∧
    M c (slot observation nontrivial half depth ordinal) ≠ 0 ∧
    ¬ (T a).adjoint (slot observation nontrivial half depth ordinal) ∈ G := by
  have source := Germ.actual_adjoint_germ_exit a (raw ordinal)
    (raw_gap observation nontrivial half depth ordinal) (raw_even observation nontrivial half depth ordinal)
    m (head ordinal) (leading_continuous observation half ordinal) (leading_live observation half ordinal)
    (actual_germ observation nontrivial half depth ordinal)
  have evenPower (n : Nat) :
      reflectL2 ((((T a).adjoint)^n) (raw ordinal)) = (((T a).adjoint)^n) (raw ordinal) := by
    induction n with
    | zero => simpa only [pow_zero, one_apply_eq_self] using raw_even observation nontrivial half depth ordinal
    | succ n prior =>
      rw [pow_succ', mul_apply_eq_comp]
      exact adjoint_even a _ prior
  have here := source.2.1
  rw [conjugate_twice c] at here
  have exit := source.2.2.2
  rw [pow_succ', mul_apply_eq_comp] at exit
  have first (j : Nat) (before : j < m) : M c ((((T a).adjoint)^j) (raw ordinal)) = 0 := by
    simpa only [conjugate_twice c] using source.1 j before
  simp only [slot, ThreePortCausal.actual_field observation nontrivial half depth ordinal 0, Nat.add_zero]
  exact ⟨first, source.2.2.1, evenPower m, here.trans_ne (leading_live observation half ordinal), exit⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryXiSlot
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
