import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedTransport

set_option autoImplicit false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedInverse

open BurnolPhysicalState MeasureTheory Set OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open RootInquiryCompletion SourceNativeInquiryRuntime SourceOperationScalarInventoryLift

open private counting_R from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedTransport
open private source_left_inverse source_right_inverse from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private nativeLanguage from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private generated_at from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedNativeHistory

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "U" => burnolMultiplicativeDilation
local notation "T" => sourceCayley
local notation "R" => burnolDirectRightResolventCLM
local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- This is the whole difference of the two literal original counting operators. -/
def cell (N : Nat) : End := CountingDual.sourceCLM (N+1) - CountingDual.sourceCLM N

theorem cell_apply (N : Nat) (w : BurnolL2) :
    cell N w = FiniteForcing.source (N+1) w - FiniteForcing.source N w := rfl

private def weight (r : ℝ) : ℝ := (Real.sqrt r)⁻¹

private def mass (N : Nat) : ℝ := ∫ r : ℝ in Ioc (N : ℝ) ((N : ℝ)+1), weight r

/-- The discrete norm exceeds the entire continuous compensation by this margin. -/
def margin (N : Nat) : ℝ := weight N - mass N

private def head (N : Nat) : End :=
  ((Real.sqrt (N : ℝ) : ℂ)⁻¹) • (U (-Real.log (N : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap

private def remainder (N : Nat) : End := head N - cell N

private theorem remainder_apply (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    remainder N w = ∫ r : ℝ in Ioc (N : ℝ) ((N : ℝ)+1), ContinuousChannels.channel (-1) r w := by
  change head N w - cell N w = _
  rw [cell_apply, BoundaryCountedIncrement.cutoff_difference N positive]
  have same : head N w = ContinuousChannels.channel (-1) N w := by
    simp only [head, smul_apply, ContinuousChannels.channel, neg_one_mul]
    rfl
  rw [same, sub_sub_cancel]

private theorem mass_nonneg (N : Nat) : 0 ≤ mass N :=
  integral_nonneg (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))

private theorem mass_lt (N : Nat) (positive : 0 < N) : mass N < weight N := by
  let lo : ℝ := N
  let hi : ℝ := lo+1
  have loPos : 0 < lo := by
    change (0 : ℝ) < (N : ℝ)
    exact_mod_cast positive
  have ordered : lo < hi := by dsimp only [hi]; linarith
  have regular : ContinuousOn weight (Icc lo hi) :=
    Real.continuous_sqrt.continuousOn.inv₀ (fun _ h => (Real.sqrt_pos.mpr (loPos.trans_le h.1)).ne')
  have strict (r : ℝ) (after : lo < r) : weight r < weight lo :=
    inv_lt_inv₀ (Real.sqrt_pos.mpr (loPos.trans after)) (Real.sqrt_pos.mpr loPos) |>.mpr
      (Real.sqrt_lt_sqrt loPos.le after)
  have smaller : (∫ r in lo..hi, weight r) < ∫ _r : ℝ in lo..hi, weight lo :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ordered
      regular continuousOn_const (fun r inside => (strict r inside.1).le)
      ⟨hi, ⟨ordered.le, le_rfl⟩, strict hi ordered⟩
  have interval : (∫ _r : ℝ in lo..hi, weight lo) = weight lo := by
    rw [intervalIntegral.integral_const]
    change (hi-lo) * weight lo = _
    rw [show hi-lo=1 by dsimp only [hi]; ring, one_mul]
  change (∫ r in Ioc lo hi, weight r) < weight lo
  rw [← intervalIntegral.integral_of_le ordered.le]
  exact smaller.trans_eq interval

theorem margin_pos (N : Nat) (positive : 0 < N) : 0 < margin N :=
  sub_pos.mpr (mass_lt N positive)

private theorem channel_norm (r : ℝ) (w : BurnolL2) :
    ‖ContinuousChannels.channel (-1) r w‖ = weight r * ‖w‖ := by
  simp only [ContinuousChannels.channel, weight, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), (U _).norm_map]

private theorem remainder_bound (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    ‖remainder N w‖ ≤ mass N * ‖w‖ := by
  rw [remainder_apply N positive]
  have estimate := norm_integral_le_integral_norm (μ := volume.restrict (Ioc (N : ℝ) ((N : ℝ)+1)))
    (fun r : ℝ => ContinuousChannels.channel (-1) r w)
  simp only [channel_norm, integral_mul_const] at estimate
  exact estimate

private def headUnit (N : Nat) (positive : 0 < N) : Endˣ := by
  let D := U (-Real.log (N : ℝ))
  let z : ℂ := Real.sqrt (N : ℝ)
  have zLive : z ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by exact_mod_cast positive)).ne'
  refine ⟨head N, z • D.symm.toContinuousLinearEquiv.toContinuousLinearMap, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro w
    change z⁻¹ • D (z • D.symm w) = w
    rw [map_smul, D.apply_symm_apply, smul_smul, inv_mul_cancel₀ zLive, one_smul]
  · apply ContinuousLinearMap.ext
    intro w
    change z • D.symm (z⁻¹ • D w) = w
    rw [map_smul, D.symm_apply_apply, smul_smul, mul_inv_cancel₀ zLive, one_smul]

private def normalized (N : Nat) (positive : 0 < N) : End :=
  (↑(headUnit N positive)⁻¹ : End) * remainder N

private theorem normalized_strict (N : Nat) (positive : 0 < N) :
    ‖normalized N positive‖ < 1 := by
  have rootPos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast positive)
  have bound : ‖normalized N positive‖ ≤ Real.sqrt (N : ℝ) * mass N := by
    apply (normalized N positive).opNorm_le_bound (mul_nonneg rootPos.le (mass_nonneg N))
    intro w
    change ‖(Real.sqrt (N : ℝ) : ℂ) • (U (-Real.log (N : ℝ))).symm (remainder N w)‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg rootPos.le, LinearIsometryEquiv.norm_map, mul_assoc]
    exact mul_le_mul_of_nonneg_left (remainder_bound N positive w) rootPos.le
  apply bound.trans_lt
  calc
    _ < Real.sqrt (N : ℝ) * (Real.sqrt (N : ℝ))⁻¹ :=
      mul_lt_mul_of_pos_left (mass_lt N positive) rootPos
    _ = 1 := mul_inv_cancel₀ rootPos.ne'

private def cellUnit (N : Nat) (positive : 0 < N) : Endˣ :=
  headUnit N positive * Units.oneSub (normalized N positive) (normalized_strict N positive)

private theorem cellUnit_val (N : Nat) (positive : 0 < N) : (cellUnit N positive : End) = cell N := by
  change (headUnit N positive : End) * (1 - normalized N positive) = cell N
  rw [mul_sub, mul_one, normalized, ← mul_assoc, Units.mul_inv, one_mul]
  change head N - (head N - cell N) = _
  exact sub_sub_cancel _ _

/-- The whole original counted cell has an inverse generated by its two actual channels. -/
def cellEquiv (N : Nat) (positive : 0 < N) : BurnolL2 ≃L[ℂ] BurnolL2 :=
  ContinuousLinearEquiv.ofUnit (cellUnit N positive)

theorem cellEquiv_apply (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    cellEquiv N positive w = cell N w :=
  congrArg (fun action : End => action w) (cellUnit_val N positive)

private theorem cell_lower (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    margin N * ‖w‖ ≤ ‖cell N w‖ := by
  have split : cell N w + remainder N w = head N w := by
    change cell N w + (head N w - cell N w) = _
    abel
  have triangle : ‖head N w‖ ≤ ‖cell N w‖ + ‖remainder N w‖ := by
    rw [← split]
    exact norm_add_le (cell N w) (remainder N w)
  have headNorm : ‖head N w‖ = weight N * ‖w‖ := by
    change ‖((Real.sqrt (N : ℝ) : ℂ)⁻¹) • U (-Real.log (N : ℝ)) w‖ = _
    simp only [weight, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      LinearIsometryEquiv.norm_map]
  rw [headNorm] at triangle
  unfold margin
  rw [sub_mul]
  linarith only [triangle, remainder_bound N positive w]

theorem cell_inverse_bound (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    ‖(cellEquiv N positive).symm w‖ ≤ ‖w‖ / margin N := by
  apply (le_div_iff₀ (margin_pos N positive)).mpr
  have bound := cell_lower N positive ((cellEquiv N positive).symm w)
  rw [← cellEquiv_apply N positive, ContinuousLinearEquiv.apply_symm_apply, mul_comm] at bound
  exact bound

private def cayleyUnit (anchor : BurnolCompletedMellinCoordinate) : Endˣ :=
  ⟨T anchor, (T anchor).adjoint,
    ContinuousLinearMap.ext (source_right_inverse anchor), ContinuousLinearMap.ext (source_left_inverse anchor)⟩

/-- Decode an actual counted adjoint word without projecting away either physical port. -/
def actedEquiv (anchor : BurnolCompletedMellinCoordinate) (order N : Nat) (positive : 0 < N) :
    BurnolL2 ≃L[ℂ] BurnolL2 :=
  ContinuousLinearEquiv.ofUnit (cellUnit N positive * (cayleyUnit anchor)⁻¹ ^ order)

theorem actedEquiv_apply (anchor : BurnolCompletedMellinCoordinate) (order N : Nat) (positive : 0 < N) (w : BurnolL2) :
    actedEquiv anchor order N positive w = cell N ((((T anchor).adjoint)^order) w) := by
  change ((cellUnit N positive : End) * (↑((cayleyUnit anchor)⁻¹ ^ order) : End)) w = _
  rw [cellUnit_val, Units.val_pow_eq_pow_val]
  rfl

theorem acted_original_R (coordinate anchor : BurnolCompletedMellinCoordinate) (order N : Nat)
    (positive : 0 < N) (w : BurnolL2) :
    actedEquiv anchor order N positive (R coordinate w) =
      R coordinate (actedEquiv anchor order N positive w) := by
  have square := congrArg (fun action : End => action w)
    ((BoundaryCountedTransport.adjoint_commutes coordinate anchor).pow_right order).eq
  change R coordinate ((((T anchor).adjoint)^order) w) =
    (((T anchor).adjoint)^order) (R coordinate w) at square
  simp only [actedEquiv_apply, ← square, cell_apply, counting_R, map_sub]

theorem recover_from_ports (anchor : BurnolCompletedMellinCoordinate) (order N : Nat)
    (positive : 0 < N) (w : BurnolL2) :
    let encoded := actedEquiv anchor order N positive w
    (actedEquiv anchor order N positive).symm ((P encoded : BurnolL2) + O encoded) = w := by
  dsimp only
  have split (value : BurnolL2) : (P value : BurnolL2) + O value = value :=
    ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal value)
  rw [split]
  exact ContinuousLinearEquiv.symm_apply_apply _ _

/-- The exact inverse fibre of the physical port still contains every erased outside component. -/
theorem physical_fibre (anchor : BurnolCompletedMellinCoordinate) (order N : Nat)
    (positive : 0 < N) (left right : BurnolL2) :
    P (actedEquiv anchor order N positive left) = P (actedEquiv anchor order N positive right) ↔
      ∃ outside : LinearMap.ker (P : BurnolL2 →ₗ[ℂ] BurnolPaAmbientCarrier),
        left = right + (actedEquiv anchor order N positive).symm (outside : BurnolL2) := by
  let encode := actedEquiv anchor order N positive
  constructor
  · intro same
    let erased : LinearMap.ker (P : BurnolL2 →ₗ[ℂ] BurnolPaAmbientCarrier) :=
      ⟨encode left - encode right, by
        change P (encode left - encode right) = 0
        rw [map_sub, same, sub_self]⟩
    refine ⟨erased, ?_⟩
    change left = right + encode.symm (encode left - encode right)
    rw [map_sub, encode.symm_apply_apply, encode.symm_apply_apply]
    abel
  · rintro ⟨outside, same⟩
    rw [same, map_add, ContinuousLinearEquiv.apply_symm_apply, map_add]
    have zero : P (outside : BurnolL2) = 0 := outside.property
    rw [zero, add_zero]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "slot" => BoundaryAdjointDefect.nativeSlot observation nontrivial half depth
local notation "pairAt" => PaBJointVisibility.actualPair observation nontrivial half depth
local notation "chosen" => PaBJointVisibility.selected observation nontrivial half depth
local notation "whole" => PacketFit.packetWhole
local notation "oldCount" => fun cutoff N : Nat => BoundaryCountedTransport.countedWhole a (slot (chosen cutoff)) N
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth

/-- Both ports recover the original packet and the literal R successor from their counted fields. -/
theorem actual_pair_recovered (cutoff N : Nat) (positive : 0 < N) :
    let packets := pairAt cutoff
    let counted := oldCount cutoff N
    let nextCounted := R c counted
    let decode := (actedEquiv a (m+1) N positive).symm
    decode ((P counted : BurnolL2) + O counted) = whole packets.1 ∧
      decode ((P nextCounted : BurnolL2) + O nextCounted) = whole packets.2 := by
  let packets := pairAt cutoff
  let encode := actedEquiv a (m+1) N positive
  let ordinal := chosen cutoff
  have first := BoundaryCountedTransport.actual_pair_counted_next observation nontrivial half depth cutoff N positive
  have old : encode (whole packets.1) = oldCount cutoff N := by
    dsimp only [encode]
    rw [actedEquiv_apply, pow_succ', mul_apply_eq_comp, ← first.1, cell_apply]
    rfl
  have next : encode (whole packets.2) = R c (oldCount cutoff N) := by
    dsimp only [encode]
    rw [actedEquiv_apply, pow_succ', mul_apply_eq_comp, ← first.2.1, cell_apply,
      ← BoundaryCountedTransport.actual_whole_counted_next observation nontrivial half depth ordinal N]
    rfl
  change encode.symm ((P (oldCount cutoff N) : BurnolL2) + O (oldCount cutoff N)) = whole packets.1 ∧
    encode.symm ((P (R c (oldCount cutoff N)) : BurnolL2) + O (R c (oldCount cutoff N))) = whole packets.2
  constructor
  · rw [← old]
    exact recover_from_ports a (m+1) N positive _
  · rw [← next]
    exact recover_from_ports a (m+1) N positive _

set_option cleanup.letToHave false in
/-- Recovered old and next wholes are delivered by the production joint consumer at its original occurrence. -/
def consumeRecoveredPair {Result : Sort u} (cutoff N : Nat) (positive : 0 < N)
    (consumer : (packets : PacketFit.Packet × PacketFit.Packet) →
      packets = pairAt cutoff →
      (let counted := oldCount cutoff N
       let nextCounted := R c counted
       let decode := (actedEquiv a (m+1) N positive).symm
       decode ((P counted : BurnolL2) + O counted) = whole packets.1 ∧
         decode ((P nextCounted : BurnolL2) + O nextCounted) = whole packets.2) →
      (∃ height : Nat, PhysicalPriceCountable.price
        (DenseDivisionPrice.height observation nontrivial half depth height)
        (PaBJointVisibility.paEffect observation half packets) ≠ 0) →
      PaBJointVisibility.outsideEffect observation half packets ≠ 0 →
      (type_of% (PaBJointVisibility.RootRead.consume factory initial cfg language (chosen cutoff+1))) →
      (type_of% (generated_at observation nontrivial half depth (chosen cutoff))) → Result) : Result :=
  BoundaryCountedTransport.consumeCountedPair observation nontrivial half depth cutoff N positive
    (fun packets literal _ _ _ _ _ pa outside ledger next =>
      consumer packets literal (by
        rw [literal]
        exact actual_pair_recovered observation nontrivial half depth cutoff N positive)
        pa outside ledger next)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedInverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
