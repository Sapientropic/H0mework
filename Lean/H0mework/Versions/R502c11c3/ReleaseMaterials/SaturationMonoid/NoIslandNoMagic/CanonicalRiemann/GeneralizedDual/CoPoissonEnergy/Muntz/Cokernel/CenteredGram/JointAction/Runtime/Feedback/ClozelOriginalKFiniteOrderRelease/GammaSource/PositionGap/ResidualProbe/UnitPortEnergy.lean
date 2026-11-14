import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FullCayleyCoupling

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.UnitPortEnergy

open BurnolPhysicalState RootInquiryCompletion SourceNativeInquiryRuntime
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private betaRead from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private beta_zero_of_pa from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ReentryDifferenceClock
open private projection_fixed seed_in_pa from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FirstPaReturn
open private source_unit_ne selected_wholes from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.JointFeeInverse
open private read_scalar_dual seed_coefficient_ne damping_ne from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FullCayleyCoupling

namespace Pa
export OriginalKCombCofinalPaAction (E invisible wholePa_normal_read)
end Pa

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => (sourceDamping c : ℂ)
local notation "T" => sourceCayley c
local notation "U" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "S" => Pa.invisible
local notation "E" => Pa.E
local notation "κ" => FullCayleyCoupling.coupling observation half
local notation "unitPrice" => FullCayleyCoupling.unitRead observation nontrivial half
local notation "α" => FullCayleyCoupling.sourceAmount observation half
local notation "β" => betaRead observation half
local notation "αDual" => ContinuousLinearMap.adjoint α 1
local notation "βDual" => ContinuousLinearMap.adjoint β 1

private theorem beta_dual_invisible : E βDual = 0 := by
  let p := E βDual
  have inside : p ∈ burnolCompactCoPoissonClosedRange := Submodule.starProjection_apply_mem _ _
  have full : (p : BurnolL2) ∈ burnolOriginalPaInL2 := Submodule.mem_map.mpr ⟨p, inside, rfl⟩
  have read : inner ℂ βDual (p : BurnolL2) = 0 :=
    (read_scalar_dual β (p : BurnolL2)).trans (beta_zero_of_pa observation half full)
  have projected : inner ℂ p p = inner ℂ (p : BurnolL2) βDual :=
    Pa.wholePa_normal_read βDual p inside
  exact inner_self_eq_zero.mp (projected.trans (inner_eq_zero_symm.mp read))

private theorem orthogonal_duals : inner ℂ αDual βDual = 0 := by
  rw [read_scalar_dual]
  change burnolPaResolventSourceCoefficient c (E βDual) = 0
  rw [beta_dual_invisible observation half, map_zero]

include nontrivial in
private theorem amount_dual_ne : αDual ≠ 0 := by
  intro erased
  let seed := burnolPaCombApproximation 0
  have fixed : E (seed : BurnolL2) = seed := Subtype.ext (projection_fixed seed_in_pa)
  have read := read_scalar_dual α (seed : BurnolL2)
  rw [erased, inner_zero_left] at read
  change 0 = burnolPaResolventSourceCoefficient c (E (seed : BurnolL2)) at read
  rw [fixed] at read
  exact seed_coefficient_ne observation nontrivial half read.symm

private theorem unit_ne : U ≠ 0 := by
  intro erased
  exact source_unit_ne observation nontrivial half (Subtype.ext erased)

/-- Full adjoint energy separates the original Pa payment and the invisible return. -/
theorem unit_energy :
    ‖U‖ ^ 2 = (‖δ * unitPrice U‖ * ‖αDual‖) ^ 2 + (‖κ‖ * ‖βDual‖) ^ 2 := by
  let pa := star (δ * unitPrice U) • αDual
  let hidden := star κ • βDual
  have orthogonal : inner ℂ pa hidden = 0 := by
    simp only [pa, hidden, inner_smul_left, inner_smul_right, orthogonal_duals observation half, mul_zero]
  have unchanged : ‖(T).adjoint U‖ = ‖U‖ := by
    rw [sourceCayley_actual_adjoint, sourceAdjointCayley_norm]
  have squared := congrArg (fun n : ℝ => n ^ 2) unchanged
  rw [FullCayleyCoupling.adjoint_unit observation nontrivial half] at squared
  change ‖pa - hidden‖ ^ 2 = ‖U‖ ^ 2 at squared
  rw [norm_sub_sq (𝕜 := ℂ), orthogonal, RCLike.zero_re, mul_zero, sub_zero] at squared
  simpa only [pa, hidden, norm_smul, norm_star] using squared.symm

theorem strict_invisible_gain : ‖κ‖ * ‖βDual‖ < ‖U‖ := by
  have energy : unitPrice U ≠ 0 := fun zero =>
    unit_ne observation nontrivial half (inner_self_eq_zero.mp zero)
  have positive : 0 < ‖δ * unitPrice U‖ * ‖αDual‖ :=
    mul_pos (norm_pos_iff.mpr (mul_ne_zero (damping_ne observation half) energy))
      (norm_pos_iff.mpr (amount_dual_ne observation nontrivial half))
  apply (sq_lt_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  linarith only [unit_energy observation nontrivial half, sq_pos_of_pos positive]

/-- Normalized gain of the original hidden unit read, with the whole invisible norm as input. -/
def invisibleFactor : ℝ := ‖κ‖ * ‖βDual‖ / ‖U‖

local notation "factor" => invisibleFactor observation nontrivial half

theorem invisible_factor_range : 0 ≤ factor ∧ factor < 1 := by
  have unitPositive := norm_pos_iff.mpr (unit_ne observation nontrivial half)
  refine ⟨div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) unitPositive.le, ?_⟩
  have strict := strict_invisible_gain observation nontrivial half
  exact (div_lt_iff₀ unitPositive).mpr (by simpa only [one_mul] using strict)

theorem invisible_read_bound (value : BurnolL2) :
    ‖unitPrice (T (S value))‖ ≤ factor * ‖U‖ * ‖S value‖ := by
  have inside : (E value : BurnolL2) ∈ burnolOriginalPaInL2 :=
    Submodule.mem_map.mpr ⟨E value, Submodule.starProjection_apply_mem _ _, rfl⟩
  have unchanged : β (S value) = β value := by
    change β (value - (E value : BurnolL2)) = β value
    rw [map_sub, beta_zero_of_pa observation half inside, sub_zero]
  have bound := norm_inner_le_norm (𝕜 := ℂ) βDual (S value)
  rw [read_scalar_dual, unchanged] at bound
  have positive := norm_pos_iff.mpr (unit_ne observation nontrivial half)
  change ‖inner ℂ U (T (S value))‖ ≤ _
  rw [FullCayleyCoupling.invisible_return observation nontrivial half, norm_neg, norm_mul, mul_comm ‖β value‖]
  calc
    _ ≤ ‖κ‖ * (‖βDual‖ * ‖S value‖) := mul_le_mul_of_nonneg_left bound (norm_nonneg _)
    _ = factor * ‖U‖ * ‖S value‖ := by
      rw [invisibleFactor, div_mul_cancel₀ _ positive.ne']
      ring

variable (depth : Nat)
local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "Packet" => PacketFit.Packet
local notation "whole" => PacketFit.packetWhole
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

variable (origin last : Nat) (table : Vector Packet (last + 1)) (cursor : Fin (last + 1))
variable (owned : RetainedLiveWindows.recorded observation nontrivial half depth origin last table)
variable (live : ReentryDifferenceClock.fee observation nontrivial half depth (origin + cursor.val + 1) ≠ 0)

local notation "moved" => RetainedLiveWindows.advance observation nontrivial half depth origin last table cursor owned live
local notation "ordinal" => (origin + 1 + Fin.val (Prod.fst (Prod.snd moved)))
local notation "observed" => JointFeeInverse.readSelected observation nontrivial half depth origin last table cursor owned live

/-- The same selected write's recovered return is bounded by its original complete invisible input. -/
theorem selected_gain_bound {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    let data := observed history
    ‖data.2.2 * κ‖ ≤ factor * ‖U‖ * ‖S (whole data.1.1.2.2.1)‖ := by
  have fields := selected_wholes observation nontrivial half depth origin last table cursor owned live
  have fees := JointFeeInverse.selected_recovery observation nontrivial half depth origin last table cursor owned live history
  have before : whole (moved).2.2.1 = raw ordinal := congrArg Prod.fst fields
  have returning : (observed history).2.2 = ReentryDifferenceClock.fee observation nontrivial half depth ordinal :=
    congrArg Prod.snd fees
  have bounded := invisible_read_bound observation nontrivial half (raw ordinal)
  have action := FullCayleyCoupling.invisible_return observation nontrivial half (raw ordinal)
  rw [← ReentryDifferenceClock.literal_fee observation nontrivial half depth ordinal] at action
  change ‖inner ℂ U (T (S (raw ordinal)))‖ ≤ _ at bounded
  rw [action, norm_neg] at bounded
  change ‖(observed history).2.2 * κ‖ ≤ factor * ‖U‖ * ‖S (whole (moved).2.2.1)‖
  rw [returning, before]
  exact bounded

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.UnitPortEnergy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
