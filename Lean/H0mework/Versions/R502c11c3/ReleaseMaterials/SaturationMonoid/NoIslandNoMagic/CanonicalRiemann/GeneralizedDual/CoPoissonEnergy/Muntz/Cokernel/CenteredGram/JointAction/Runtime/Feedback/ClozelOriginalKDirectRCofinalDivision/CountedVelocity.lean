import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.VelocityTail
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedEndpointLimit

import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Topological.Quadrature.CutoffPair

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 30
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

open Filter BurnolPhysicalState Complex
open OriginalRieszFinitePairing.CoPoisson.Ward CountedJointStrong
open scoped Topology InnerProductSpace

open private count_endpoint_scale_channel from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointLimit
open private slopeSeed from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.Slope
open private endpoint_scale_fourier from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedEndpointLimit
open private sourceValue source_tendsto from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong

local notation "Resolvent" => burnolDirectRightResolventCLM
local notation "Riesz" => burnolCompletedMellinRieszVector
local notation "C" => ContinuousChannels.channel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "old" => D.raw observation nontrivial half depth ordinal
local notation "before" => D.raw observation nontrivial half depth (ordinal+1)
local notation "next" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "wave" => actualDivisionCompactWave observation nontrivial half depth (ordinal+1)

private theorem literal_R (n : Nat) :
    D.raw observation nontrivial half depth (n+1) =
      Resolvent coord (D.raw observation nontrivial half depth n) := by
  rw [D.raw_successor, OriginalKCombCofinalRAction.original_R_direct]
  rfl

private theorem wave_source : fourierL2 next = wave := by
  have born := actual_division_compact_wave_writeback observation nontrivial half depth (ordinal+1)
  have current := (Parent.Full.complete_of_branches observation nontrivial half _ _
    (OriginalKDirectRCofinalMaterial.actual_successor_branches observation nontrivial half depth
      (ordinal+1))).2.2.1
  have fromRaw : @Eq BurnolL2 next
      (DirectRDivisionControls.bornRead observation nontrivial half depth (ordinal+1)) :=
    (D.raw_successor observation nontrivial half depth (ordinal+1)).trans current.symm
  have known : @Eq BurnolL2 (fourierL2.symm wave) next := born.2.1.trans fromRaw.symm
  exact (congrArg fourierL2 known).symm.trans (fourierL2.apply_symm_apply wave)

/-- The leading-subtracted original counting tail, at the same actual cutoff. -/
def velocityRead (direction : ℝ) (M : Nat) (limit counted field : BurnolL2) : BurnolL2 :=
  ((M : ℝ)+1) • countEndpointScale direction (M+1)
    (limit-counted-(1/2 : ℝ) • C direction ((M : ℝ)+1) field)

private theorem channel_fourier (a : ℝ) (x : BurnolL2) :
    fourierL2 (C 1 a x) = C (-1) a (fourierL2 x) := by
  simp only [ContinuousChannels.channel, one_mul, neg_one_mul, map_smul,
    fourierL2_burnolMultiplicativeDilation]

private theorem real_fourier (z : ℝ) (x : BurnolL2) : fourierL2 (z • x) = z • fourierL2 x :=
  (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).map_smul z x

private theorem velocityRead_fourier (M : Nat) (limit counted field : BurnolL2) :
    fourierL2 (velocityRead 1 M limit counted field) =
      velocityRead (-1) M (fourierL2 limit) (fourierL2 counted) (fourierL2 field) := by
  unfold velocityRead
  rw [real_fourier, endpoint_scale_fourier]
  have inner : fourierL2 (limit-counted-(1/2 : ℝ) • C 1 ((M : ℝ)+1) field) =
      fourierL2 limit-fourierL2 counted-(1/2 : ℝ) • C (-1) ((M : ℝ)+1) (fourierL2 field) := by
    rw [map_sub, map_sub, real_fourier, channel_fourier]
  rw [inner]

private theorem velocity_coefficient (parameter : BurnolCompletedMellinCoordinate) (input output : BurnolL2) :
    (-(1/12 : ℝ)) • slopeSeed 1 output (-((parameter.value-1/2) • output + (2 : ℂ) • input)) =
      (1/12 : ℂ) • (parameter.value • output + (2 : ℂ) • input) := by
  simp only [slopeSeed, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  module

private theorem paired_velocity (parameter : BurnolCompletedMellinCoordinate) (first : BurnolL2) :
    let input := Resolvent parameter first
    let output := Resolvent parameter input
    ∃ limit : BurnolL2,
      Tendsto (fun N : Nat => DualSource.source N output) atTop (𝓝 limit) ∧
      Tendsto (fun M : Nat => velocityRead 1 M limit (DualSource.source (M+1) output) output)
        atTop (𝓝 ((1/12 : ℂ) • (parameter.value • output + (2 : ℂ) • input))) := by
  let input := Resolvent parameter first
  let output := Resolvent parameter input
  let velocity := resolventVelocity parameter input
  let acceleration := resolventAcceleration parameter first
  let limit := sourceValue 1 output
  have source := actual_resolvent_dilation_derivative parameter input
  have second := actual_resolvent_acceleration parameter first
  have counted : Tendsto (fun N : Nat => DualSource.source N output) atTop (𝓝 limit) :=
    source_tendsto 1 output velocity source
  have moved : Tendsto (fun M : Nat => velocityRead 1 M limit (DualSource.source (M+1) output) output)
      atTop (𝓝 ((-(1/12 : ℝ)) • slopeSeed 1 output velocity)) :=
    directional_source_velocity_limit 1 output velocity acceleration source second
  have coefficient := velocity_coefficient parameter input output
  change (-(1/12 : ℝ)) • slopeSeed 1 output velocity = _ at coefficient
  rw [coefficient] at moved
  exact ⟨limit, counted, moved⟩

private theorem velocity_at (parameter : BurnolCompletedMellinCoordinate) {seed x y : BurnolL2}
    (first : x = Resolvent parameter seed) (second : y = Resolvent parameter x) :
    ∃ limit : BurnolL2,
      Tendsto (fun N : Nat => DualSource.source N y) atTop (𝓝 limit) ∧
      Tendsto (fun M : Nat => velocityRead 1 M limit (DualSource.source (M+1) y) y)
        atTop (𝓝 ((1/12 : ℂ) • (parameter.value • y + (2 : ℂ) • x))) := by
  rw [second, first]
  exact paired_velocity parameter seed

/-- The directional velocity is generated at the literal next Division occurrence. -/
theorem actual_counted_velocity :
    ∃ limit : BurnolL2,
      Tendsto (fun N : Nat => (DualSource.source N next, FiniteForcing.source N wave))
        atTop (𝓝 (limit, fourierL2 limit)) ∧
      Tendsto (fun M : Nat => (velocityRead 1 M limit (DualSource.source (M+1) next) next,
          velocityRead (-1) M (fourierL2 limit) (FiniteForcing.source (M+1) wave) wave))
        atTop (𝓝 (((1/12 : ℂ) • ((coord).value • next + (2 : ℂ) • before)),
          fourierL2 ((1/12 : ℂ) • ((coord).value • next + (2 : ℂ) • before)))) := by
  have first := literal_R observation nontrivial half depth ordinal
  have second := literal_R observation nontrivial half depth (ordinal+1)
  have observationAt := velocity_at coord first second
  let limit := observationAt.choose
  have count := observationAt.choose_spec.1
  have moved := observationAt.choose_spec.2
  have waveRead : fourierL2 next = wave := wave_source observation nontrivial half depth ordinal
  have counts (N : Nat) : fourierL2 (DualSource.source N next) = FiniteForcing.source N wave := by
    exact (OriginalGamma.Source.CountingQuadraticLimit.source_fourier N next).symm.trans
      (congrArg (FiniteForcing.source N) waveRead)
  refine ⟨limit, count.prodMk_nhds (((fourierL2.continuous.tendsto _).comp count).congr'
    (Eventually.of_forall counts)), moved.prodMk_nhds ?_⟩
  apply ((fourierL2.continuous.tendsto _).comp moved).congr'
  filter_upwards with M
  rw [Function.comp_apply, velocityRead_fourier, counts, waveRead]

/-- The independent inverse of the original action uses the complete position endpoint and velocity. -/
def incidenceInput (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint slope : BurnolL2) : BurnolL2 :=
  (6 : ℂ) • slope - coordinate.value • endpoint

private theorem recover_source (coordinate : BurnolCompletedMellinCoordinate) (x y : BurnolL2) :
    incidenceInput coordinate ((1/2 : ℝ) • y)
      ((1/12 : ℂ) • (coordinate.value • y + (2 : ℂ) • x)) = x := by
  unfold incidenceInput
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  module

private theorem incidence_converges (coordinate : BurnolCompletedMellinCoordinate)
    {head slope : Nat → BurnolL2} {x y : BurnolL2}
    (headRead : Tendsto head atTop (𝓝 ((1/2 : ℝ) • y)))
    (slopeRead : Tendsto slope atTop (𝓝 ((1/12 : ℂ) • (coordinate.value • y+(2 : ℂ) • x)))) :
    Tendsto (fun M => incidenceInput coordinate (head M) (slope M)) atTop (𝓝 x) := by
  have moved := (slopeRead.const_smul (6 : ℂ)).sub (headRead.const_smul coordinate.value)
  change Tendsto (fun M => incidenceInput coordinate (head M) (slope M)) atTop
    (𝓝 (incidenceInput coordinate ((1/2 : ℝ) • y)
      ((1/12 : ℂ) • (coordinate.value • y+(2 : ℂ) • x)))) at moved
  rwa [recover_source] at moved

/-- The original compensated tail observed in its actual moving coordinates. -/
def countedTail (direction : ℝ) (count : Nat → BurnolL2) (limit : BurnolL2) (m : Nat) : BurnolL2 :=
  countEndpointScale direction (m+1) (limit-count (m+1))

private theorem velocity_is_first_correction (direction : ℝ) (count : Nat → BurnolL2)
    (limit field : BurnolL2) (m : Nat) :
    @Eq BurnolL2 (velocityRead direction m limit (count (m+1)) field)
      (((m : ℝ)+1) • (countedTail direction count limit m - (1/2 : ℝ) • field)) := by
  let S := (countEndpointScale direction (m+1)).restrictScalars ℝ
  have original : S (C direction ((m : ℝ)+1) field) = field := by
    change countEndpointScale direction (m+1) (C direction ((m : ℝ)+1) field) = field
    simpa only [Nat.cast_add, Nat.cast_one] using
      count_endpoint_scale_channel direction (m+1) (Nat.succ_pos m) field
  change ((m : ℝ)+1) • S (limit-count (m+1)-(1/2 : ℝ) • C direction ((m : ℝ)+1) field) =
    ((m : ℝ)+1) • (S (limit-count (m+1)) - (1/2 : ℝ) • field)
  rw [map_sub, map_smul, original]

/-- Read the input and output from two cutoffs of the same complete counted field. -/
def observedIncidence (coordinate : BurnolCompletedMellinCoordinate) (direction : ℝ)
    (count : Nat → BurnolL2) (limit : BurnolL2) (m : Nat) : BurnolL2 × BurnolL2 :=
  let head := countedTail direction count limit
  (incidenceInput coordinate (head m) (SourceGeneratedQuadrature.cutoffPair head m), (2 : ℝ) • head m)

private theorem observed_incidence_tendsto (coordinate : BurnolCompletedMellinCoordinate)
    (direction : ℝ) (count : Nat → BurnolL2) (limit x y : BurnolL2)
    (head : Tendsto (countedTail direction count limit) atTop (𝓝 ((1/2 : ℝ) • y)))
    (slope : Tendsto (fun m : Nat => velocityRead direction m limit (count (m+1)) y)
      atTop (𝓝 ((1/12 : ℂ) • (coordinate.value • y+(2 : ℂ) • x)))) :
    Tendsto (observedIncidence coordinate direction count limit) atTop (𝓝 (x,y)) := by
  have correction := slope.congr' (Eventually.of_forall (velocity_is_first_correction direction count limit y))
  have paid := SourceGeneratedQuadrature.cutoff_pair_tendsto correction
  have first := incidence_converges coordinate head paid
  have last := head.const_smul (2 : ℝ)
  rw [smul_smul, show (2 : ℝ)*(1/2)=1 by norm_num, one_smul] at last
  exact first.prodMk_nhds last

/-- The two complete original counts recover both adjacent original fields on each side. -/
theorem actual_counted_incidence :
    ∃ limit : BurnolL2,
      Tendsto (fun N : Nat => (DualSource.source N next, FiniteForcing.source N wave))
        atTop (𝓝 (limit, fourierL2 limit)) ∧
      Tendsto (observedIncidence coord 1 (fun N => DualSource.source N next) limit)
        atTop (𝓝 (before,next)) ∧
      Tendsto (observedIncidence coord (-1) (fun N => FiniteForcing.source N wave) (fourierL2 limit))
        atTop (𝓝 (fourierL2 before,wave)) := by
  have paired := actual_counted_velocity observation nontrivial half depth ordinal
  let limit := paired.choose
  have counted := paired.choose_spec.1
  have posSlope : Tendsto (fun M : Nat => velocityRead 1 M limit (DualSource.source (M+1) next) next)
      atTop (𝓝 ((1/12 : ℂ) • ((coord).value • next+(2 : ℂ) • before))) := paired.choose_spec.2.fst_nhds
  have freqSlope : Tendsto (fun M : Nat => velocityRead (-1) M (fourierL2 limit)
      (FiniteForcing.source (M+1) wave) wave) atTop
      (𝓝 (fourierL2 ((1/12 : ℂ) • ((coord).value • next+(2 : ℂ) • before)))) := paired.choose_spec.2.snd_nhds
  have w := wave_source observation nontrivial half depth ordinal
  have orig := actual_division_counted_endpoint_limit observation nontrivial half depth (ordinal+1)
  let other := orig.choose
  have otherCounted : Tendsto (fun N => DualSource.source N (fourierL2.symm wave)) atTop (𝓝 other) :=
    orig.choose_spec.2.1.fst_nhds
  have otherEndpoint :
      Tendsto (countedTail 1 (fun N => DualSource.source N (fourierL2.symm wave)) other)
        atTop (𝓝 ((1/2 : ℝ) • fourierL2.symm wave)) := orig.choose_spec.2.2.fst_nhds
  have otherWave :
      Tendsto (countedTail (-1) (fun N => FiniteForcing.source N wave) (fourierL2 other))
        atTop (𝓝 ((1/2 : ℝ) • wave)) := orig.choose_spec.2.2.snd_nhds
  have identity : @Eq BurnolL2 (fourierL2.symm wave) next :=
    (congrArg fourierL2.symm w.symm).trans (fourierL2.symm_apply_apply next)
  rw [identity] at otherCounted otherEndpoint
  have limits : other = limit := tendsto_nhds_unique otherCounted counted.fst_nhds
  rw [limits] at otherEndpoint otherWave
  have waveSlope : Tendsto (fun M : Nat => velocityRead (-1) M (fourierL2 limit)
      (FiniteForcing.source (M+1) wave) wave) atTop
      (𝓝 ((1/12 : ℂ) • ((coord).value • wave+(2 : ℂ) • fourierL2 before))) := by
    have eq : fourierL2 ((1/12 : ℂ) • ((coord).value • next+(2 : ℂ) • before)) =
        (1/12 : ℂ) • ((coord).value • wave+(2 : ℂ) • fourierL2 before) := by
      rw [map_smul, map_add, map_smul, map_smul, w]
    rw [← eq]
    exact freqSlope
  exact ⟨limit, counted, observed_incidence_tendsto coord 1 _ limit before next otherEndpoint posSlope,
    observed_incidence_tendsto coord (-1) _ (fourierL2 limit) (fourierL2 before) wave otherWave waveSlope⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
