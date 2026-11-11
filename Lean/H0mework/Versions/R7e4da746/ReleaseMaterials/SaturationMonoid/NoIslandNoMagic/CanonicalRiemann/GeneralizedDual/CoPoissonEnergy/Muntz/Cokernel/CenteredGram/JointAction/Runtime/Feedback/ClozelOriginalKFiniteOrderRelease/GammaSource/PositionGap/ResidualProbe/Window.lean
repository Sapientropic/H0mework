import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.Cayley

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe

open BurnolPhysicalState Finset
open RootInquiryCompletion SourceNativeInquiryRuntime
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped BigOperators

open private amplitude amplitude_nonneg from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedResidualProbe
open private sourcePrices original_tail_separates from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private nextCutoff from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord
open private sampleEnd nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape

namespace Grid
export SourceGeneratedPolynomialProbe (node extract scale_ge_one weightMass norm_extract_le)
end Grid

local notation "S" => burnolDirectRightResolvent
local notation "R" => burnolDirectRightResolventCLM
local notation "δ" => sourceDamping

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "root" => acquisitionRuntime observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "source" => sourcePrices observation nontrivial half depth
local notation "coeffs" => fittedCoefficients observation nontrivial half depth

private def probeAddress (base count : Nat) (a : Fin (count+1) → ℂ) (i : Fin (base+count+1)) : ℝ :=
  probeScale observation half base count a * Grid.node i

private def maxProbe (base count : Nat) (a : Fin (count+1) → ℂ) : ℝ :=
  probeAddress observation half base count a (Fin.last (base+count))

local notation "address" => probeAddress observation half
local notation "largest" => maxProbe observation half

private theorem probe_scale_pos (base count : Nat) (a : Fin (count+1) → ℂ) :
    0 < probeScale observation half base count a :=
  zero_lt_one.trans_le (Grid.scale_ge_one (base+count) (m-1) (amplitude_nonneg c count a) combDelay_pos _)

private theorem address_pos (base count : Nat) (a : Fin (count+1) → ℂ) (i : Fin (base+count+1)) :
    0 < address base count a i :=
  mul_pos (probe_scale_pos observation half base count a) (by unfold Grid.node; positivity)

private theorem address_le_max (base count : Nat) (a : Fin (count+1) → ℂ) (i : Fin (base+count+1)) :
    address base count a i ≤ largest base count a := by
  unfold maxProbe probeAddress Grid.node
  apply mul_le_mul_of_nonneg_left _ (probe_scale_pos observation half base count a).le
  simp only [Fin.val_last]
  have below : (i.val:ℝ) ≤ ((base+count:Nat):ℝ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  linarith

private def rowBudget (base count : Nat) (a : Fin (count+1) → ℂ) : ℝ :=
  (largest base count a)^(base+count) * (‖reader c‖ * ((2/δ c)*‖word c base count a‖))

private def windowBudget (base count : Nat) (a : Fin (count+1) → ℂ) : ℝ :=
  Grid.weightMass (base+count+1) (m-1) * rowBudget observation half base count a

/-- The entire grid is evaluated from a common finite prefix of positive original powers. -/
def finiteProbe (base count : Nat) (a : Fin (count+1) → ℂ) (fuel : Nat) : ℂ :=
  Grid.extract (base+count+1) (m-1) (fun i =>
    ((address base count a i:ℝ):ℂ)^(base+count) * reader c
      (finiteShift c (address base count a i) fuel (word c base count a)))

private theorem finite_probe_error (base count : Nat) (a : Fin (count+1) → ℂ) (fuel : Nat) :
    ‖weightedProbe observation half base count a - finiteProbe observation half base count a fuel‖ ≤
      windowBudget observation half base count a * (discount c (largest base count a))^fuel := by
  let v := word c base count a
  let f (i : Fin (base+count+1)) := probedWord c base count a (address base count a i)
  let g (i : Fin (base+count+1)) :=
    (address base count a i:ℂ)^(base+count) * reader c (finiteShift c (address base count a i) fuel v)
  let ρ := discount c (largest base count a)
  have split : weightedProbe observation half base count a - finiteProbe observation half base count a fuel =
      Grid.extract (base+count+1) (m-1) (fun i => f i - g i) := by
    simp only [weightedProbe,finiteProbe,Grid.extract,probeAddress,f,g,v,mul_sub,sum_sub_distrib]
  rw [split]
  have each (i : Fin (base+count+1)) :
      ‖f i-g i‖ ≤ rowBudget observation half base count a * ρ^fuel := by
    let x := address base count a i
    have pos : 0 < x := address_pos observation half base count a i
    change ‖(x:ℂ)^(base+count) * reader c (S ((c).value/2+(x:ℂ)) v) -
      (x:ℂ)^(base+count) * reader c (finiteShift c x fuel v)‖ ≤ _
    rw [← mul_sub,← map_sub,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
    have readError := (reader c).le_opNorm (S ((c).value/2+(x:ℂ)) v - finiteShift c x fuel v)
    have actual := actual_shift_error c x pos.le fuel v
    have addr := address_le_max observation half base count a i
    have ratio := discount_monotone c pos.le addr
    calc
      _ ≤ x^(base+count) * (‖reader c‖ * (((2/δ c)*‖v‖) * (discount c x)^fuel)) :=
        mul_le_mul_of_nonneg_left (readError.trans (mul_le_mul_of_nonneg_left actual (norm_nonneg _)))
          (pow_nonneg pos.le _)
      _ = (x^(base+count) * (‖reader c‖ * ((2/δ c)*‖v‖))) * (discount c x)^fuel := by ring
      _ ≤ _ := by
        unfold rowBudget
        change _ ≤ ((largest base count a)^(base+count) * (‖reader c‖ * ((2/δ c)*‖v‖))) * ρ^fuel
        have δpos := sourceDamping_pos c
        have xMax : 0 ≤ largest base count a := pos.le.trans addr
        have discountPos := discount_nonneg c pos.le
        gcongr
  have total := Grid.norm_extract_le (base+count+1) (m-1) (fun i => f i-g i) _ each
  exact total.trans_eq (by unfold windowBudget; ring)

/-- The literal amount of original R powers needed to meet a given positive budget. -/
def probeFuel (base count : Nat) (a : Fin (count+1) → ℂ) (tolerance : ℝ) : Nat :=
  ⌊windowBudget observation half base count a / (tolerance*(δ c/largest base count a))⌋₊ + 1

private theorem finite_probe_within (base count : Nat) (a : Fin (count+1) → ℂ)
    (tolerance : ℝ) (positive : 0 < tolerance) :
    ‖weightedProbe observation half base count a -
        finiteProbe observation half base count a (probeFuel observation half base count a tolerance)‖ < tolerance := by
  let x := largest base count a
  let η := δ c/x
  let B := windowBudget observation half base count a
  let N := probeFuel observation half base count a tolerance
  have xPos : 0 < x := address_pos observation half base count a (Fin.last (base+count))
  have ηPos : 0 < η := div_pos (sourceDamping_pos c) xPos
  have ratio : discount c x = (1+η)⁻¹ := by
    have fraction : 1+δ c/x = (δ c+x)/x := by
      apply (eq_div_iff xPos.ne').mpr
      rw [add_mul,one_mul,div_mul_cancel₀ _ xPos.ne',add_comm]
    unfold discount η
    rw [fraction,inv_div]
  have floor : B/(tolerance*η) < (N:ℝ) := by
    unfold N probeFuel
    exact_mod_cast Nat.lt_floor_add_one (B/(tolerance*η))
  have above : B < (N:ℝ)*(tolerance*η) :=
    (div_lt_iff₀ (mul_pos positive ηPos)).mp floor
  have grows : 1+(N:ℝ)*η ≤ (1+η)^N :=
    one_add_mul_le_pow (by linarith [ηPos]) N
  have room : B < tolerance*(1+η)^N := by
    have first : B < tolerance*(1+(N:ℝ)*η) := by nlinarith
    exact first.trans_le (mul_le_mul_of_nonneg_left grows positive.le)
  have finite := finite_probe_error observation half base count a N
  apply finite.trans_lt
  change B * (discount c x)^N < tolerance
  rw [ratio,inv_pow,← div_eq_mul_inv]
  exact (div_lt_iff₀ (pow_pos (by linarith [ηPos] : 0<1+η) _)).mpr room

def residualFuel (start count cutoff : Nat) : Nat :=
  probeFuel observation half (probeBase observation start cutoff) count (coeffs start count)
    (‖xiOpening observation half‖/4)

local notation "fuel" => residualFuel observation nontrivial half depth

/-- A bounded original R run contains a positive-time witness for the actual fitted residual. -/
theorem actual_fitted_window_live (start count cutoff : Nat) :
    ∃ offset : Nat, 0 < offset ∧ offset ≤ fuel start count cutoff ∧
      Sparse.birthResidual (source start) (schedule start count).val (cutoff+offset) ≠ 0 := by
  let base := probeBase observation start cutoff
  let a := coeffs start count
  let N := fuel start count cutoff
  let price := xiOpening observation half
  let z := weightedProbe observation half base count a
  let finite := finiteProbe observation half base count a N
  have live : 0 < ‖price‖ := norm_pos_iff.mpr
    (FixedFourierKFeedback.original_opening_price_ne_zero observation nontrivial half)
  have near : ‖z-finite‖ < ‖price‖/4 :=
    finite_probe_within observation half base count a (‖price‖/4) (by positivity)
  have margin : ‖price‖/2 ≤ ‖z‖ :=
    actual_fitted_probe_margin observation nontrivial half depth start count cutoff
  by_contra! silent
  have gone : finite = 0 := by
    unfold finite finiteProbe Grid.extract
    apply sum_eq_zero
    intro i _
    dsimp only
    rw [finite_shift_read c (address base count a i) N (reader c) (word c base count a)]
    have reads :
        (∑ k ∈ range N, ∑ j ∈ range (k+1),
          rightWeight c (address base count a i) k j *
            reader c ((R c^(j+1)) (word c base count a))) = 0 := by
      apply sum_eq_zero
      intro k hk
      apply sum_eq_zero
      intro j hj
      have erased : reader c ((R c^(j+1)) (word c base count a)) = 0 := by
        change nativePriceAt observation half (word c base count a) (j+1) = 0
        exact (actual_fitted_residual_price observation nontrivial half depth start count cutoff (j+1)).trans
          (silent (j+1) (Nat.succ_pos j)
            ((Nat.succ_le_of_lt (mem_range.mp hj)).trans (Nat.succ_le_of_lt (mem_range.mp hk))))
      rw [erased,mul_zero]
    simp only [reads,mul_zero]
  rw [gone,sub_zero] at near
  linarith

def sourceCutoff (start count : Nat) : Nat :=
  nextCutoff (schedule start count).val

def latestTime (start count : Nat) : Nat :=
  sourceCutoff observation nontrivial half depth start count +
    fuel start count (sourceCutoff observation nontrivial half depth start count)

/-- This source bound applies to the original first pivot, retaining its exact canonical address. -/
theorem actual_original_pivot_bound (start count : Nat) :
    (schedule start (count+1)).val (Fin.last count) ≤ latestTime observation nontrivial half depth start count := by
  let cutoff := sourceCutoff observation nontrivial half depth start count
  obtain ⟨offset,_,bound,live⟩ := actual_fitted_window_live observation nontrivial half depth start count cutoff
  unfold priceSchedule
  rw [SourceGeneratedFiniteGram.CofinalRecord.schedule_last]
  unfold SourceGeneratedFiniteGram.CofinalRecord.pivotTime
  apply Nat.add_le_add_left
  exact (Nat.find_min' _ live).trans bound

private def acquisitionStop (start count : Nat) : Nat :=
  Tape.index (Native.factory observation nontrivial half) (Native.initial observation nontrivial half depth)
    (Native.firstCfg observation nontrivial half depth) (nativeLanguage observation nontrivial half depth)
    (start+count+latestTime observation nontrivial half depth start count-1+2)

def boundedNativeRun (start count : Nat) :=
  (root).run (acquisitionStop observation nontrivial half depth start count+1)

private theorem endpoint_within (start count : Nat) :
    sampleEnd observation nontrivial half depth start count (Fin.last count) (Fin.last count) ≤
      acquisitionStop observation nontrivial half depth start count := by
  unfold sampleEnd acquisitionStop
  apply (Tape.strictMono (Native.factory observation nontrivial half)
    (Native.initial observation nontrivial half depth) (Native.firstCfg observation nontrivial half depth)
    (nativeLanguage observation nontrivial half depth)).monotone
  have paid := actual_original_pivot_bound observation nontrivial half depth start count
  change start+count+(schedule start (count+1)).val (Fin.last count)-1+2 ≤ _
  omega

/-- The bounded run contains the literal acquisition execution including its final paid successor. -/
theorem actual_native_sampling_prefix (start count : Nat) :
    (boundedNativeRun observation nontrivial half depth start count).prefix
      (sampleEnd observation nontrivial half depth start count (Fin.last count) (Fin.last count)+1)
      (Nat.succ_le_succ (endpoint_within observation nontrivial half depth start count)) =
      scheduledNativeRun observation nontrivial half depth start count :=
  prefix_runFrom (root) (root).initialState _ _ _

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
