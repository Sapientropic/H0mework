import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedIncrement
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaBJointVisibility

set_option autoImplicit false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedTransport

open BurnolPhysicalState RootInquiryCompletion SourceNativeInquiryRuntime
open SourceOperationScalarInventoryLift
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open MeasureTheory Set OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

open private right_quarter below_half from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private coordinate_eq from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
open private source_left_inverse source_right_inverse from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private chart from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryXiSlot
open private pair_fields exact_pair from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaBJointVisibility
open private nativeLanguage from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private generated_at from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedNativeHistory

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

local notation "T" => sourceCayley
local notation "R" => burnolDirectRightResolventCLM
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "S" => HilbertInventory.PositionField

private theorem resolvent_commutes (c d : BurnolCompletedMellinCoordinate) : Commute (R c) (R d) := by
  by_cases same : c.value = d.value
  · rw [show c = d from coordinate_eq same]
  change R c * R d = R d * R c
  apply ContinuousLinearMap.ext
  intro w
  change R c (R d w) = R d (R c w)
  have forward : R c w - R d w = (c.value/2-d.value/2) • R c (R d w) :=
    burnolDirectRightResolvent_identity (c.value/2) (d.value/2) (right_quarter c) (right_quarter d) w
  have reverse : R d w - R c w = (d.value/2-c.value/2) • R d (R c w) :=
    burnolDirectRightResolvent_identity (d.value/2) (c.value/2) (right_quarter d) (right_quarter c) w
  have live : c.value/2-d.value/2 ≠ 0 := by
    intro vanished
    apply same
    linear_combination 2 * (sub_eq_zero.mp vanished)
  apply smul_right_injective BurnolL2 live
  calc
    _ = R c w - R d w := forward.symm
    _ = -(R d w - R c w) := (neg_sub _ _).symm
    _ = _ := by
      rw [reverse, ← neg_smul, neg_sub]

/-- The true adjoint commutes with the actual source R by the original resolvent identity and two-sided inverse. -/
theorem adjoint_commutes (c d : BurnolCompletedMellinCoordinate) : Commute (R c) ((T d).adjoint) := by
  let End := BurnolL2 →L[ℂ] BurnolL2
  let U : Endˣ := ⟨T d,(T d).adjoint,
    ContinuousLinearMap.ext (source_right_inverse d),ContinuousLinearMap.ext (source_left_inverse d)⟩
  have forward : Commute (R c) (U : End) := by
    change Commute (R c) (1 + (sourceDamping d : ℂ) • R d)
    exact (Commute.one_right _).add_right ((resolvent_commutes c d).smul_right _)
  exact forward.units_inv_right

private def gain (c : BurnolCompletedMellinCoordinate) : ℂ := -(1 / (c.value - 1/2))

private theorem original_gain (c : BurnolCompletedMellinCoordinate) (v : S) :
    M c (R c (v : BurnolL2)) = gain c * M c (v : BurnolL2) := by
  have source := CombSource.Pricing.ambient_R_scalar_action (c.value/2) (right_quarter c)
    (v : BurnolL2) v.property.1 (c.value/2) (right_quarter c) (below_half c)
  rw [chart c] at source
  change M c (R c (v : BurnolL2)) = -(1/(c.value/2+c.value/2-1/2))*M c (v : BurnolL2) at source
  rw [show c.value/2+c.value/2-1/2 = c.value-1/2 by ring] at source
  exact source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "slot" => BoundaryAdjointDefect.nativeSlot observation nontrivial half depth
local notation "field" => ThreePortCausal.field observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

/-- The stored cofinal successor executes the original R on the complete adjoint slot. -/
theorem actual_slot_next (ordinal : Nat) :
    (slot (ordinal+1) : BurnolL2) = R c (slot ordinal : BurnolL2) := by
  have moved : field (ordinal+1) 0 = R c (field ordinal 0) := by
    rw [ThreePortCausal.actual_field observation nontrivial half depth,
      ThreePortCausal.actual_field observation nontrivial half depth, Nat.add_zero, Nat.add_zero,
      OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth]
    exact OriginalKCombCofinalRAction.original_R_direct observation nontrivial half (raw ordinal)
  have source := congrArg (fun op : BurnolL2 →L[ℂ] BurnolL2 => op (field ordinal 0))
    ((adjoint_commutes c a).pow_right m).eq
  change R c ((((T a).adjoint)^m) (field ordinal 0)) =
    (((T a).adjoint)^m) (R c (field ordinal 0)) at source
  change (((T a).adjoint)^m) (field (ordinal+1) 0) =
    R c ((((T a).adjoint)^m) (field ordinal 0))
  rw [moved]
  exact source.symm

private theorem counting_R (coordinate : BurnolCompletedMellinCoordinate) (N : Nat) (w : BurnolL2) :
    FiniteForcing.source N (R coordinate w) = R coordinate (FiniteForcing.source N w) := by
  let A := CountingDual.sourceCLM N
  change A (burnolDirectRightResolvent (coordinate.value/2) w) =
    burnolDirectRightResolvent (coordinate.value/2) (A w)
  unfold burnolDirectRightResolvent
  rw [map_neg, ← A.integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn (coordinate.value/2) (right_quarter coordinate) w)]
  apply congrArg (Neg.neg : BurnolL2 → BurnolL2)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  unfold burnolDirectRightResolventIntegrand
  change A (positiveMellinQuarterRightResolventWeight (coordinate.value/2) h •
    burnolMultiplicativeDilation (-h/2) w) =
    positiveMellinQuarterRightResolventWeight (coordinate.value/2) h •
      burnolMultiplicativeDilation (-h/2) (A w)
  rw [map_smul]
  exact congrArg (fun value : BurnolL2 => positiveMellinQuarterRightResolventWeight (coordinate.value/2) h • value)
    (SeedCounting.source_dilation N (-h/2) w)

/-- The two finite counting actions leave their complete difference available before either projection. -/
def countedWhole (anchor : BurnolCompletedMellinCoordinate) (v : S) (N : Nat) : BurnolL2 :=
  let w := (T anchor).adjoint (v : BurnolL2)
  FiniteForcing.source (N+1) w - FiniteForcing.source N w

theorem actual_whole_counted_next (ordinal N : Nat) :
    countedWhole a (slot (ordinal+1)) N = R c (countedWhole a (slot ordinal) N) := by
  let w := (slot ordinal : BurnolL2)
  have commute := congrArg (fun op : BurnolL2 →L[ℂ] BurnolL2 => op w) (adjoint_commutes c a).eq
  change R c ((T a).adjoint w) = (T a).adjoint (R c w) at commute
  unfold countedWhole
  dsimp only
  rw [actual_slot_next observation nontrivial half depth ordinal]
  change FiniteForcing.source (N+1) ((T a).adjoint (R c w)) -
    FiniteForcing.source N ((T a).adjoint (R c w)) = _
  rw [← commute, counting_R, counting_R, map_sub]

theorem actual_release_next (ordinal : Nat) :
    BoundaryQuarterRelease.release a (slot (ordinal+1)) =
      gain c • BoundaryQuarterRelease.release a (slot ordinal) := by
  rw [BoundaryQuarterRelease.release_source a (slot (ordinal+1)),
    BoundaryQuarterRelease.release_source a (slot ordinal), BoundaryXiSlot.conjugate_twice c,
    actual_slot_next observation nontrivial half depth ordinal, original_gain c (slot ordinal), smul_smul]
  congr 1
  ring

/-- The cofinal R step acts on the newly counted effect, using the same finite counting cell. -/
theorem actual_counted_next (ordinal N : Nat) (positive : 0 < N) :
    BoundaryCountedIncrement.increment a (slot (ordinal+1)) N =
      gain c • BoundaryCountedIncrement.increment a (slot ordinal) N := by
  rw [BoundaryCountedIncrement.actual_increment a (slot (ordinal+1)) N positive,
    BoundaryCountedIncrement.actual_increment a (slot ordinal) N positive,
    actual_release_next observation nontrivial half depth ordinal]
  exact smul_comm _ _ _

theorem actual_counted_price_next (ordinal N : Nat) :
    BoundaryCountedIncrement.countedPrice c (slot (ordinal+1)) N =
      gain c * BoundaryCountedIncrement.countedPrice c (slot ordinal) N := by
  unfold BoundaryCountedIncrement.countedPrice
  rw [actual_release_next observation nontrivial half depth ordinal]
  change inner ℂ (_ : BurnolQuarterIntervalL2)
    (gain c • (BoundaryQuarterRelease.release a (slot ordinal) : BurnolQuarterIntervalL2)) = _
  exact inner_smul_right _ _ _

local notation "packetPair" => PaBJointVisibility.actualPair observation nontrivial half depth
local notation "selected" => PaBJointVisibility.selected observation nontrivial half depth
local notation "whole" => PacketFit.packetWhole
local notation "adjointWord" => (ContinuousLinearMap.adjoint (T a))^m

/-- The two acted fields are the actual two literal packet slots of the same table acquisition. -/
theorem actual_pair_counted_next (cutoff N : Nat) (positive : 0 < N) :
    let packets := packetPair cutoff
    let ordinal := selected cutoff
    (slot ordinal : BurnolL2) = adjointWord (whole packets.1) ∧
    (slot (ordinal+1) : BurnolL2) = adjointWord (whole packets.2) ∧
    R c (adjointWord (whole packets.1)) = adjointWord (whole packets.2) ∧
    BoundaryCountedIncrement.increment a (slot (ordinal+1)) N =
      gain c • BoundaryCountedIncrement.increment a (slot ordinal) N := by
  let ordinal := selected cutoff
  let packets := packetPair cutoff
  have fields : (whole packets.1, whole packets.2) = (raw ordinal, raw (ordinal+1)) :=
    pair_fields observation nontrivial half depth cutoff
  have left : whole packets.1 = raw ordinal := congrArg (fun w : BurnolL2 × BurnolL2 => w.1) fields
  have right : whole packets.2 = raw (ordinal+1) := congrArg (fun w : BurnolL2 × BurnolL2 => w.2) fields
  have source (n : Nat) : (slot n : BurnolL2) = adjointWord (raw n) := by
    change adjointWord (field n 0) = _
    rw [ThreePortCausal.actual_field observation nontrivial half depth, Nat.add_zero]
  have first : (slot ordinal : BurnolL2) = adjointWord (whole packets.1) :=
    (source ordinal).trans (congrArg (fun w : BurnolL2 => adjointWord w) left.symm)
  have next : (slot (ordinal+1) : BurnolL2) = adjointWord (whole packets.2) :=
    (source (ordinal+1)).trans (congrArg (fun w : BurnolL2 => adjointWord w) right.symm)
  have action : R c (adjointWord (whole packets.1)) = adjointWord (whole packets.2) := by
    rw [← first, ← next, actual_slot_next observation nontrivial half depth ordinal]
  exact ⟨first,next,action,actual_counted_next observation nontrivial half depth ordinal N positive⟩

local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth

set_option cleanup.letToHave false in
/-- The original joint consumer reads the counted effect on its exact packets and carries its whole and next. -/
def consumeCountedPair {Result : Sort u} (cutoff N : Nat) (positive : 0 < N)
    (consumer : (packets : PacketFit.Packet × PacketFit.Packet) →
      packets = packetPair cutoff →
      R c (adjointWord (whole packets.1)) = adjointWord (whole packets.2) →
      (type_of% (actual_whole_counted_next observation nontrivial half depth (selected cutoff) N)) →
      (type_of% (actual_counted_next observation nontrivial half depth (selected cutoff) N positive)) →
      (type_of% (actual_counted_price_next observation nontrivial half depth (selected cutoff) N)) →
      (type_of% (BoundaryCountedIncrement.installed_from_counted
        observation nontrivial half depth (selected cutoff) N positive)) →
      (∃ height : Nat, PhysicalPriceCountable.price
        (DenseDivisionPrice.height observation nontrivial half depth height)
        (PaBJointVisibility.paEffect observation half packets) ≠ 0) →
      PaBJointVisibility.outsideEffect observation half packets ≠ 0 →
      (type_of% (PaBJointVisibility.RootRead.consume factory initial cfg language (selected cutoff+1))) →
      (type_of% (generated_at observation nontrivial half depth (selected cutoff))) → Result) : Result :=
  PaBJointVisibility.consumeJoint observation nontrivial half depth cutoff
    (fun packets identity pa outside ledger next =>
      let literal := identity.trans (exact_pair observation nontrivial half depth cutoff).symm
      let source := actual_pair_counted_next observation nontrivial half depth cutoff N positive
      let action : R c (adjointWord (whole packets.1)) = adjointWord (whole packets.2) := by
        rw [literal]
        exact source.2.2.1
      consumer packets literal action
        (actual_whole_counted_next observation nontrivial half depth (selected cutoff) N) source.2.2.2
        (actual_counted_price_next observation nontrivial half depth (selected cutoff) N)
        (BoundaryCountedIncrement.installed_from_counted
          observation nontrivial half depth (selected cutoff) N positive)
        pa outside ledger next)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedTransport
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
