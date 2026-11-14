import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactPhase

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology

open private compactPhaseRaw compact_phase_positive compact_phase_raw_even compact_phase_split_read from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactPhase

local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "box" => symmetricInterval r₀
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "N" => fun n : Nat => ((n+2 : Nat) : ℝ)
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "B" => fun c (n : Nat) => Prod.snd (clockCoefficients c (actualClockPair c n))
local notation "bφ" => fun c n => (phase c n)⁻¹*B c n

/-- The actual phase response, after removal of its full homogeneous
coefficient, has this compact logarithmic profile. -/
def countedCompactPhaseProfile (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x| ≤ q then -(1/2 : ℂ)*((|x| : ℝ) : ℂ)^(-s₀ c)*collarPrimitive c |x| else 0

private theorem compact_profile_positive_limit (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, 0 < x →
      Tendsto (fun n : Nat => compactPhaseRaw c n x) atTop (𝓝 (countedCompactPhaseProfile c x)) := by
  have reads := ae_all_iff.mpr (compact_phase_positive c)
  have indices : Tendsto N atTop atTop := by
    simpa only [Function.comp_def] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have coeff : Tendsto (bφ c) atTop (𝓝 (-(1/2 : ℂ))) := actual_phase_count_limit c
  filter_upwards [reads] with x atx positive
  unfold countedCompactPhaseProfile
  rw [abs_of_pos positive]
  by_cases inside : x ≤ q
  · rw [if_pos inside]
    apply ((coeff.mul_const ((x : ℂ)^(-s₀ c))).mul_const (collarPrimitive c x)).congr'
    filter_upwards [indices.eventually (eventually_gt_atTop (q/x))] with n covered
    exact ((atx n positive).1 inside covered).symm
  · rw [if_neg inside]
    exact tendsto_const_nhds.congr (fun n => ((atx n positive).2 (lt_of_not_ge inside)).symm)

private theorem compact_profile_raw_limit (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, Tendsto (fun n : Nat => compactPhaseRaw c n x) atTop
      (𝓝 (countedCompactPhaseProfile c x)) := by
  have positive := compact_profile_positive_limit c
  have parity := ae_all_iff.mpr (compact_phase_raw_even c)
  filter_upwards [positive, negMeasurePreserving.quasiMeasurePreserving.ae positive, parity, volume.ae_ne (0 : ℝ)]
    with x direct opposite even nonzero
  rcases lt_or_gt_of_ne nonzero with negative | live
  · change 0 < -x → Tendsto (fun n : Nat => compactPhaseRaw c n (-x)) atTop
      (𝓝 (countedCompactPhaseProfile c (-x))) at opposite
    have value : countedCompactPhaseProfile c (-x) = countedCompactPhaseProfile c x := by
      simp only [countedCompactPhaseProfile, abs_neg]
    rw [value] at opposite
    exact (opposite (neg_pos.mpr negative)).congr even
  · exact direct live

/-- Both slots have the same literal position profile at their own support. -/
theorem actual_compact_phase_limit_profile (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume,
      (countedCompactPhaseLimit c).1 x = Set.indicator box (countedCompactPhaseProfile c) x ∧
      (countedCompactPhaseLimit c).2 x = if r₀ < |x| then countedCompactPhaseProfile c x else 0 := by
  have strong := actual_counted_compact_phase_limit c
  have read := ae_all_iff.mpr (compact_phase_split_read c)
  have raw := compact_profile_raw_limit c
  have centre : ∀ᵐ x : ℝ ∂volume,
      (countedCompactPhaseLimit c).1 x = Set.indicator box (countedCompactPhaseProfile c) x := by
    obtain ⟨σ, strict, path⟩ := (tendstoInMeasure_of_tendsto_Lp strong.fst_nhds).exists_seq_tendsto_ae
    filter_upwards [read, raw, path] with x actual value converges
    by_cases inside : x ∈ box
    · rw [indicator_of_mem inside]
      apply tendsto_nhds_unique converges
      apply (value.comp strict.tendsto_atTop).congr'
      filter_upwards with n
      exact ((actual (σ n)).1.trans (indicator_of_mem inside _)).symm
    · rw [indicator_of_notMem inside]
      apply tendsto_nhds_unique converges
      exact tendsto_const_nhds.congr (fun n => ((actual (σ n)).1.trans (indicator_of_notMem inside _)).symm)
  have exterior : ∀ᵐ x : ℝ ∂volume,
      (countedCompactPhaseLimit c).2 x = if r₀ < |x| then countedCompactPhaseProfile c x else 0 := by
    obtain ⟨σ, strict, path⟩ := (tendstoInMeasure_of_tendsto_Lp strong.snd_nhds).exists_seq_tendsto_ae
    filter_upwards [read, raw, path] with x actual value converges
    by_cases outside : r₀ < |x|
    · rw [if_pos outside]
      apply tendsto_nhds_unique converges
      apply (value.comp strict.tendsto_atTop).congr'
      filter_upwards with n
      exact ((actual (σ n)).2.trans (if_pos outside)).symm
    · rw [if_neg outside]
      apply tendsto_nhds_unique converges
      exact tendsto_const_nhds.congr (fun n => ((actual (σ n)).2.trans (if_neg outside)).symm)
  exact centre.and exterior

theorem actual_compact_phase_limit_support (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, |x| > q →
      (countedCompactPhaseLimit c).1 x = 0 ∧ (countedCompactPhaseLimit c).2 x = 0 := by
  filter_upwards [actual_compact_phase_limit_profile c] with x read outside
  have rsmall : r₀ < |x| := (by norm_num : r₀ < q).trans outside
  have missing : x ∉ box := fun inside => rsmall.not_ge (abs_le.mpr inside)
  refine ⟨read.1.trans (indicator_of_notMem missing _), read.2.trans ?_⟩
  rw [if_pos rsmall, countedCompactPhaseProfile, if_neg outside.not_ge]

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
