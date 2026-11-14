import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryQuarterRelease

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedIncrement

open BurnolPhysicalState MeasureTheory Set Filter Complex
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

open private adjoint_even center_zero_iff from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private parity from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryAdjointDefect
open private counting_eq_actual quarterCenter from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting

local notation "q" => burnolUnscaledCommonGapRadius
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Gq" => BurnolQuarterMeanZeroCarrier
local notation "S" => HilbertInventory.PositionField
local notation "position" => ClosedSubmodule.toSubmodule HilbertInventory.positionSpace
local notation "Ppos" => Submodule.starProjection position
local notation "G" => locallyConstantFace q
local notation "Z" => OriginalRieszSource.Constructor.zeroMean
local notation "Q" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "T" => sourceCayley
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "ch" => ContinuousChannels.channel (-1)

local instance : CompleteSpace S := HilbertInventory.positionSpace.isClosed.isComplete.completeSpace_coe
local instance : CompleteSpace Gq := burnolQuarterMeanZeroClosedFace.isClosed.isComplete.completeSpace_coe

private def observe : BurnolL2 →L[ℂ] Gq := (Z).comp (Q)

private def weight (a : BurnolCompletedMellinCoordinate) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (-star a.value)

/-- The increment contains the actual integer channel and the whole new continuous cell. -/
def delta (a : BurnolCompletedMellinCoordinate) (N : Nat) : ℂ :=
  weight a N - ∫ r : ℝ in Ioc (N : ℝ) (N+1), weight a r

theorem cutoff_difference (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    FiniteForcing.source (N+1) w - FiniteForcing.source N w =
      ch N w - ∫ r : ℝ in Ioc (N : ℝ) (N+1), ch r w := by
  have n : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have ordered : (N : ℝ) ≤ (N : ℝ)+1 := by linarith
  have all := ContinuousChannels.channel_integrable (-1) ((N : ℝ)+1) w
  have split : (∫ r : ℝ in Ioc 0 ((N : ℝ)+1), ch r w) =
      (∫ r : ℝ in Ioc 0 (N : ℝ), ch r w) +
        ∫ r : ℝ in Ioc (N : ℝ) (N+1), ch r w := by
    rw [← Ioc_union_Ioc_eq_Ioc n ordered]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (all.mono_set (Ioc_subset_Ioc le_rfl ordered))
      (all.mono_set (Ioc_subset_Ioc n le_rfl))
  have integer : Channels.sourceChannel N w = ch N w := by
    simp only [Channels.sourceChannel, ContinuousChannels.channel, neg_one_mul]
  unfold FiniteForcing.source ContinuousChannels.normalization
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ N), integer, Nat.cast_succ, split]
  abel

private theorem gap_channel (w : BurnolL2) (gap : w ∈ G) (r : ℝ) (large : 1 ≤ r) :
    observe (ch r w) = 0 := by
  apply (center_zero_iff _).mpr
  unfold ContinuousChannels.channel
  apply (G).smul_mem
  apply burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive q
    (by norm_num [burnolUnscaledCommonGapRadius]) _ _ w gap
  simpa only [neg_one_mul, neg_nonpos] using Real.log_nonneg large

private theorem channel_add (r : ℝ) (u w : BurnolL2) :
    ch r (u+w) = ch r u + ch r w := by
  simp only [ContinuousChannels.channel, map_add, smul_add]

private theorem compact_smul (r : ℝ) (z : ℂ) (u : Gq) :
    observe (ch r (E ((z • u : Gq) : Hq))) = z • observe (ch r (E (u : Hq))) := by
  simp only [ContinuousChannels.channel, Submodule.coe_smul, map_smul, smul_smul]
  rw [mul_comm ((Real.sqrt r : ℂ)⁻¹) z]

/-- Each large scale sees the actual centered power after the position remainder is retained. -/
theorem actual_channel (a : BurnolCompletedMellinCoordinate) (v : S) (r : ℝ) (large : 1 ≤ r) :
    observe (ch r ((T a).adjoint (v : BurnolL2))) =
      weight a r • BoundaryQuarterRelease.release a v := by
  let w := (T a).adjoint (v : BurnolL2)
  let u := BoundaryQuarterRelease.release a v
  let kept := Ppos w
  have even : reflectL2 w = w := adjoint_even a _ (parity v)
  have split : w = E (u : Hq) + kept := eq_add_of_sub_eq (BoundaryQuarterRelease.position_cut w even)
  have gap : kept ∈ G := (Submodule.starProjection_apply_mem position w).1
  have centered : observe (ch r (E (u : Hq))) = weight a r • u := by
    let scalar := -2 * (sourceDamping a : ℂ) *
      burnolAmbientCompletedMellinEvaluator (C a) (v : BurnolL2)
    have released : u = scalar • SingularCounting.centeredPower a :=
      BoundaryQuarterRelease.release_source a v
    rw [released, compact_smul]
    change scalar • quarterCenter (ch r (E (SingularCounting.centeredPower a : Hq))) = _
    rw [← counting_eq_actual, SingularCounting.centered_power_scale a r large]
    exact smul_comm scalar (weight a r) _
  change observe (ch r w) = weight a r • u
  rw [split, channel_add, map_add, centered, gap_channel kept gap r large, add_zero]

/-- Both complete finite actions execute before the next counted effect is measured. -/
def increment (a : BurnolCompletedMellinCoordinate) (v : S) (N : Nat) : Gq :=
  let w := (T a).adjoint (v : BurnolL2)
  observe (FiniteForcing.source (N+1) w - FiniteForcing.source N w)

theorem actual_increment (a : BurnolCompletedMellinCoordinate) (v : S) (N : Nat) (positive : 0 < N) :
    increment a v N = delta a N • BoundaryQuarterRelease.release a v := by
  let w := (T a).adjoint (v : BurnolL2)
  have n : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast positive
  have integrable : IntegrableOn (fun r => ch r w) (Ioc (N : ℝ) ((N : ℝ)+1)) :=
    (ContinuousChannels.channel_integrable (-1) ((N : ℝ)+1) w).mono_set
      (Ioc_subset_Ioc (zero_le_one.trans n) le_rfl)
  change observe (FiniteForcing.source (N+1) w - FiniteForcing.source N w) = _
  rw [cutoff_difference N positive w, map_sub, ← observe.integral_comp_comm integrable]
  change observe (ch N ((T a).adjoint (v : BurnolL2))) -
    (∫ r : ℝ in Ioc (N : ℝ) (N+1), observe (ch r ((T a).adjoint (v : BurnolL2)))) = _
  rw [actual_channel a v N n, setIntegral_congr_fun measurableSet_Ioc
    (fun r hr => actual_channel a v r (n.trans hr.1.le)), integral_smul_const, ← sub_smul]
  rfl

theorem delta_ne_zero (a : BurnolCompletedMellinCoordinate) (N : Nat) (positive : 0 < N) :
    delta a N ≠ 0 := by
  let lo : ℝ := N
  let hi : ℝ := lo+1
  have loPos : 0 < lo := by
    change 0 < (N : ℝ)
    exact_mod_cast positive
  have ordered : lo < hi := by dsimp only [hi]; linarith
  have norm_read {r : ℝ} (hr : 0 < r) : ‖weight a r‖ = r ^ (-a.value.re) := by
    simp only [weight, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.neg_re, Complex.star_def, Complex.conj_re]
  have decay {r : ℝ} (hr : lo < r) : ‖weight a r‖ < ‖weight a lo‖ := by
    rw [norm_read loPos, norm_read (loPos.trans hr)]
    exact Real.rpow_lt_rpow_of_neg loPos hr (by linarith [a.rightHalf])
  have regular : ContinuousOn (fun r => ‖weight a r‖) (Icc lo hi) := by
    intro r inside
    have pos : 0 < r := loPos.trans_le inside.1
    exact (Complex.continuousAt_ofReal_cpow_const r (-star a.value)
      (Or.inr pos.ne')).norm.continuousWithinAt
  have smaller : (∫ r in lo..hi, ‖weight a r‖) < ∫ _r : ℝ in lo..hi, ‖weight a lo‖ :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ordered
      regular continuousOn_const (fun r inside => (decay inside.1).le)
      ⟨hi, ⟨ordered.le, le_rfl⟩, decay ordered⟩
  have realSize : (∫ _r : ℝ in lo..hi, ‖weight a lo‖) = ‖weight a lo‖ := by
    rw [intervalIntegral.integral_const]
    change (hi-lo) * ‖weight a lo‖ = _
    rw [show hi-lo=1 by dsimp only [hi]; ring, one_mul]
  have bound : ‖∫ r in Ioc lo hi, weight a r‖ < ‖weight a lo‖ := by
    rw [← intervalIntegral.integral_of_le ordered.le]
    exact (intervalIntegral.norm_integral_le_integral_norm ordered.le).trans_lt (smaller.trans_eq realSize)
  change weight a lo - (∫ r in Ioc lo hi, weight a r) ≠ 0
  intro gone
  exact (ne_of_lt bound) (congrArg norm (sub_eq_zero.mp gone).symm)

private def physicalPoint (c : BurnolCompletedMellinCoordinate) : S :=
  let test := BoundaryAdjointDefect.B.physicalCotest c
  ⟨(test : BurnolL2), test.property.1.1, test.property.2⟩

/-- The independent fixed test is acted by the same original counted cell. -/
def countedPrice (c : BurnolCompletedMellinCoordinate) (v : S) (N : Nat) : ℂ :=
  inner ℂ (increment (C c) (physicalPoint c) N) (BoundaryQuarterRelease.release (C c) v)

theorem counted_price_source (c : BurnolCompletedMellinCoordinate) (v : S) (N : Nat)
    (positive : 0 < N) :
    countedPrice c v N = star (delta (C c) N) *
      BoundaryQuarterRelease.quarterPrice (C c) v (BoundaryAdjointDefect.B.physicalCotest c) := by
  unfold countedPrice
  rw [actual_increment (C c) (physicalPoint c) N positive]
  change inner ℂ ((delta (C c) N) •
    (BoundaryQuarterRelease.release (C c) (physicalPoint c) : Hq))
    (BoundaryQuarterRelease.release (C c) v : Hq) = _
  rw [inner_smul_left, starRingEnd_apply]
  rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "v" => BoundaryAdjointDefect.nativeSlot observation nontrivial half depth ordinal

/-- The actual counted difference recovers the installed fixed residual with a source-generated denominator. -/
theorem installed_from_counted (N : Nat) (positive : 0 < N) :
    (star (delta a N) * BoundaryAdjointDefect.coefficient a v)⁻¹ * countedPrice c v N =
      -(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual := by
  let receipt := installedOriginalKReceiptAt observation nontrivial half.down
  let coefficient := star (delta a N) * BoundaryAdjointDefect.coefficient a v
  have live : coefficient ≠ 0 := mul_ne_zero (star_ne_zero.mpr (delta_ne_zero a N positive))
    (BoundaryAdjointDefect.actual_coefficient_live observation nontrivial half depth ordinal)
  have read : countedPrice c v N = coefficient * (-receipt.fixedResidual) := by
    rw [counted_price_source c v N positive,
      BoundaryQuarterRelease.actual_fixed_quarter observation nontrivial half depth ordinal]
    exact (mul_assoc _ _ _).symm
  change coefficient⁻¹ * countedPrice c v N = -receipt.fixedResidual
  rw [read, ← mul_assoc, inv_mul_cancel₀ live, one_mul]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedIncrement
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
