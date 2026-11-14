import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.JointFeeInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.FullCayleyCoupling

open BurnolPhysicalState RootInquiryCompletion SourceNativeInquiryRuntime
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private betaRead from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private opening_ne from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.NativeReturnImpulse
open private projection_fixed seed_in_pa from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FirstPaReturn
open private selected_wholes from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.JointFeeInverse

namespace Pa
export OriginalKCombCofinalPaAction (E invisible invisible_mem wholePa_normal_read)
end Pa
namespace Reentry
export OriginalKDirectRCofinalReentrySourceAction (full_invisible_reentry source_unit_invisible_pair_Q)
end Reentry

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => (sourceDamping c : ℂ)
local notation "T" => sourceCayley c
local notation "U" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "V" => OriginalKDirectRCofinalMobiusSourceAction.actualReentryVector observation half
local notation "S" => Pa.invisible
local notation "E" => Pa.E
local notation "B" => burnolPaResolventSourceCoefficient c
local notation "β" => betaRead observation half
local notation "seed" => burnolPaCombApproximation 0
local notation "ClosedPa" => burnolCompactCoPoissonClosedRange.toSubmodule

private theorem damping_ne : δ ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'

include nontrivial in
private theorem seed_coefficient_ne : B seed ≠ 0 := by
  have paid := opening_ne observation nontrivial half
  change B (E ((burnolDirectRightResolventCLM c ^ (0 : Nat)) (seed : BurnolL2))) ≠ 0 at paid
  rw [pow_zero, one_apply_eq_self] at paid
  have fixed : E (seed : BurnolL2) = seed := Subtype.ext (projection_fixed seed_in_pa)
  rwa [fixed] at paid

private theorem unit_port (p : BurnolPaAmbientCarrier) (inside : p ∈ ClosedPa) :
    T (p : BurnolL2) = (E (T (p : BurnolL2)) : BurnolL2) + (δ * B p) • U :=
  OriginalWholeDebtRJointMobiusPaCayleySource.actual_whole_update observation nontrivial half ⟨p, inside⟩

include nontrivial in
private theorem return_port (value : BurnolL2) :
    E (T (S value)) = (δ * β value) • V := by
  have hidden : E (S value) = 0 := Pa.invisible_mem value
  have observed := Reentry.source_unit_invisible_pair_Q observation nontrivial half.down value
  have source := Reentry.full_invisible_reentry c value
  change E (burnolDirectRightResolvent ((c).value / 2) (S value)) =
    (inner ℂ (fourierL2 (burnolUnitTailResponse (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4))
      (S value)) • V at source
  change inner ℂ (fourierL2 (burnolUnitTailResponse (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4))
    (S value) = β value at observed
  rw [sourceCayley_apply, map_add, hidden, zero_add, map_smul, source, observed, smul_smul]

private def row (p : BurnolPaAmbientCarrier) : ℂ :=
  inner ℂ (E (T (p : BurnolL2)) : BurnolL2) (V : BurnolL2)

/-- This coefficient is read on the original opening Pa seed and its actual Cayley image. -/
def coupling : ℂ := row observation half seed / star (B seed)

local notation "κ" => coupling observation half

private theorem cross_ports (p : BurnolPaAmbientCarrier) (inside : p ∈ ClosedPa) (value : BurnolL2) :
    β value * row observation half p + star (B p) * inner ℂ U (T (S value)) = 0 := by
  let output := E (T (p : BurnolL2))
  have hidden : E (S value) = 0 := Pa.invisible_mem value
  have silent := Pa.wholePa_normal_read (S value) p inside
  rw [hidden, inner_zero_right] at silent
  have conserved := (sourceCayley_inner c (p : BurnolL2) (S value)).trans silent.symm
  have projected := (Pa.wholePa_normal_read (T (S value)) output (Submodule.starProjection_apply_mem _ _)).symm
  have visible : inner ℂ (output : BurnolL2) (T (S value)) = (δ * β value) * row observation half p := by
    change inner ℂ (output : BurnolL2) (T (S value)) =
      (δ * β value) * inner ℂ (output : BurnolL2) (V : BurnolL2)
    change inner ℂ (output : BurnolL2) (T (S value)) =
      inner ℂ (output : BurnolL2) (E (T (S value)) : BurnolL2) at projected
    rw [projected, return_port observation nontrivial half, Submodule.coe_smul,
      inner_smul_right (𝕜 := ℂ) (output : BurnolL2) (V : BurnolL2) (δ * β value)]
  have real_star (a : ℂ) : (starRingEnd ℂ) (δ * a) = δ * star a := by
    rw [map_mul, Complex.conj_ofReal]
    rfl
  rw [unit_port observation nontrivial half p inside, inner_add_left, visible,
    inner_smul_left, real_star] at conserved
  have factored : δ * (β value * row observation half p + star (B p) * inner ℂ U (T (S value))) = 0 := by
    calc
      _ = (δ * β value) * row observation half p + (δ * star (B p)) * inner ℂ U (T (S value)) := by ring
      _ = 0 := conserved
  exact (mul_eq_zero.mp factored).resolve_left (damping_ne observation half)

/-- Orthogonality of the two original inputs fixes the invisible-to-invisible unit read. -/
theorem invisible_return (value : BurnolL2) :
    inner ℂ U (T (S value)) = -(β value * κ) := by
  have paid := cross_ports observation nontrivial half seed (burnolPaCombApproximation_mem 0) value
  have denominator : star (B seed) ≠ 0 := star_ne_zero.mpr (seed_coefficient_ne observation nontrivial half)
  have exactRead : inner ℂ U (T (S value)) = -(β value * row observation half seed) / star (B seed) := by
    apply (eq_div_iff denominator).2
    linear_combination paid
  rw [exactRead, coupling]
  ring

def sourceAmount : BurnolL2 →L[ℂ] ℂ := (B).comp E

local notation "amount" => sourceAmount observation half

private theorem unit_orthogonal (p : BurnolPaAmbientCarrier) (inside : p ∈ ClosedPa) :
    inner ℂ U (p : BurnolL2) = 0 := by
  let unit := OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half
  have member : unit ∈ ClosedPaᗮ := Submodule.starProjection_apply_mem _ _
  exact (inner_eq_zero_symm.mp (member p inside) : inner ℂ unit p = 0)

def unitRead (value : BurnolL2) : ℂ := inner ℂ U value

local notation "unitPrice" => unitRead observation nontrivial half

/-- Both source fees generate the next unit read from one whole current. -/
theorem unit_write (value : BurnolL2) :
    unitPrice (T value) = δ * amount value * unitPrice U - β value * κ := by
  let p := E value
  have split : value = (p : BurnolL2) + S value := by
    change value = (p : BurnolL2) + (value - (p : BurnolL2))
    abel
  have written := congrArg (fun x : BurnolL2 => inner ℂ U (T x)) split
  have inside : p ∈ ClosedPa := Submodule.starProjection_apply_mem _ _
  have gone := unit_orthogonal observation nontrivial half (E (T (p : BurnolL2)))
    (Submodule.starProjection_apply_mem _ _)
  rw [map_add, inner_add_right, unit_port observation nontrivial half p inside,
    inner_add_right, gone, zero_add, inner_smul_right, invisible_return observation nontrivial half] at written
  rw [sub_eq_add_neg]
  exact written

private theorem read_scalar_dual (f : BurnolL2 →L[ℂ] ℂ) (value : BurnolL2) :
    inner ℂ (f.adjoint 1) value = f value := by
  rw [ContinuousLinearMap.adjoint_inner_left, RCLike.inner_apply, map_one, mul_one]

/-- The actual full adjoint moves the original Division unit into the two source covectors. -/
theorem adjoint_unit :
    (T).adjoint U = star (δ * unitPrice U) • (amount).adjoint 1 - star κ • (β).adjoint 1 := by
  apply ext_inner_right ℂ
  intro value
  rw [ContinuousLinearMap.adjoint_inner_left T value U]
  simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_star, read_scalar_dual]
  change unitPrice (T value) = _
  rw [unit_write]
  ring

variable (depth : Nat)
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "α" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth

/-- Two adjacent literal R packets give the same Cayley unit write without executing a new event. -/
theorem literal_write (ordinal : Nat) :
    unitPrice (raw ordinal) + δ * unitPrice (raw (ordinal + 1)) =
      δ * α ordinal * unitPrice U - fee ordinal * κ := by
  have action : T (raw ordinal) = raw ordinal + δ • raw (ordinal + 1) := by
    simp only [sourceCayley_apply, OriginalKCombFirstFullSourceDynamics.raw_successor,
      OriginalKCombCofinalRAction.original_R_direct]
    rfl
  have written := unit_write observation nontrivial half (raw ordinal)
  rw [action, unitRead, inner_add_right, inner_smul_right] at written
  rw [ReentryDifferenceClock.literal_fee]
  exact written

local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "Packet" => PacketFit.Packet
local notation "whole" => PacketFit.packetWhole

variable (origin last : Nat) (table : Vector Packet (last + 1)) (cursor : Fin (last + 1))
variable (owned : RetainedLiveWindows.recorded observation nontrivial half depth origin last table)
variable (live : ReentryDifferenceClock.fee observation nontrivial half depth (origin + cursor.val + 1) ≠ 0)

local notation "moved" => RetainedLiveWindows.advance observation nontrivial half depth origin last table cursor owned live
local notation "ordinal" => (origin + 1 + Fin.val (Prod.fst (Prod.snd moved)))
local notation "observed" => JointFeeInverse.readSelected observation nontrivial half depth origin last table cursor owned live

theorem selected_write {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    let data := observed history
    let packets := data.1.1.2.2
    unitPrice (whole packets.1) + δ * unitPrice (whole packets.2) =
      δ * data.2.1 * unitPrice U - data.2.2 * κ := by
  have fields := selected_wholes observation nontrivial half depth origin last table cursor owned live
  have fees := JointFeeInverse.selected_recovery observation nontrivial half depth origin last table cursor owned live history
  have price := congrArg (fun pair : BurnolL2 × BurnolL2 => unitPrice pair.1 + δ * unitPrice pair.2) fields
  have paid := congrArg (fun pair : ℂ × ℂ => δ * pair.1 * unitPrice U - pair.2 * κ) fees
  exact price.trans ((literal_write observation nontrivial half depth ordinal).trans paid.symm)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.FullCayleyCoupling
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
