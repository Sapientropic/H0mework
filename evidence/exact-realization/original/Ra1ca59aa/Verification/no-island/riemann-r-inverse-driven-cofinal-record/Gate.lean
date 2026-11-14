import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.InverseDrivenRecord
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace InverseDrivenRecordCertificate

open BurnolPhysicalState Matrix Finset RootInquiryCompletion SourceNativeInquiryRuntime
open scoped Matrix
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PacketFit
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedRecord
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedMatrix
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.InverseDrivenRecord
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
  (actual_relation_stock_next modelInventory advanceStock)
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)

open private prepareFromInverse from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.InverseDrivenRecord
open private PreparedAt PreparedAt.fit PreparedAt.cutoff PreparedAt.fuel PreparedAt.columns
  carryTo oldStop carried_covers oldColumnFrom firstFrom from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedRecord
open private birthColumn oldActorRow birthPrice from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedMatrix
open private nextCutoff from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord
open private candidateEpoch from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CandidateRead
open private toRange from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "factory" => Native.factory observation nontrivial half
local notation "observe" => observed observation nontrivial half depth
local notation "oldStep" => RetainedRecord.advance observation nontrivial half depth
local notation "newStep" => InverseDrivenRecord.step observation nontrivial half depth
local notation "drivenRun" => runUsingInverse observation nontrivial half depth
local notation "emit" => emitFromInverse observation nontrivial half depth
local notation "prepare" => prepareFromInverse observation nontrivial half depth
local notation "pick" => firstFrom observation nontrivial half depth
local notation "pivot" => paidPivot observation nontrivial half depth
local notation "epoch" => candidateEpoch observation nontrivial half depth
local notation "packet" => Native.packet observation nontrivial half depth

set_option cleanup.letToHave false in
private theorem the_old_inverse_fits_the_actual_retained_newborn_column
    {start n : Nat} (prior : MatrixState observation nontrivial half depth start n) :
    let old := prior.source
    let stop := oldStop observation nontrivial half depth old
    let held := carryTo observation nontrivial half depth old.source stop
    let covered := carried_covers observation nontrivial half depth old.source stop
    let birth := oldColumnFrom observation nontrivial half depth old held covered (Fin.last n)
    let ready := prepare prior
    PreparedAt.fit ready = WithLp.toLp 2 (prior.inverse.invOf *ᵥ (fun j => birth j)) ∧
    PreparedAt.columns ready = Fin.lastCases birth (Block.columns (observe old)) ∧
    PreparedAt.cutoff ready = nextCutoff old.times ∧
    PreparedAt.fuel ready = probeFuel observation half (probeBase observation start (PreparedAt.cutoff ready)) n
      (Fin.snoc (fun j => -(PreparedAt.fit ready) j) 1) (‖xiOpening observation half‖/4) :=
  ⟨rfl,rfl,rfl,rfl⟩

#eval IO.println "CP603_CONTROL + the_old_inverse_fits_the_actual_retained_newborn_column"

private def OriginalRead (start n : Nat) (actor : Fin (n+1)) (both : Packet × Packet) : Prop :=
  (tapeOccurrence observation nontrivial half depth start n actor (Fin.last n)).1.engine.node =
    .active (Tape.admissionPresentation factory both.1) ∧
  Table.nextPacket factory both.1 = both.2 ∧
  (candidateSuccessor observation nontrivial half depth start n actor (pivot start n)).1.engine.node =
    .active (Tape.admissionPresentation factory both.2)

private theorem original_packet_read (start n : Nat) (actor : Fin (n+1)) :
    OriginalRead observation nontrivial half depth start n actor
      (candidatePackets observation nontrivial half depth start n actor (pivot start n)) := by
  unfold OriginalRead
  rw [← actual_selected_occurrence]
  exact candidate_born_from_packets observation nontrivial half depth start n actor (pivot start n)

set_option cleanup.letToHave false in
private theorem inverse_driven_emission_carries_the_entire_original_progress
    {start n : Nat} (prior : MatrixState observation nontrivial half depth start n) (actor : Fin (n+1)) :
    let event := emit prior
    let both := event.selected actor
    event = oldStep prior.source ∧
    both = (packet (epoch start n actor (pivot start n)),
      packet (epoch start n actor (pivot start n)+1)) ∧
    OriginalRead observation nontrivial half depth start n actor both ∧
    type_of% (actual_candidate_paid_segment observation nontrivial half depth start n actor (pivot start n)) ∧
    type_of% (actual_tape_whole observation nontrivial half depth start n actor (Fin.last n)) ∧
    type_of% (actual_tape_next observation nontrivial half depth start n actor (Fin.last n)) := by
  have same := (emit prior).selected_actual actor
  have original := original_packet_read observation nontrivial half depth start n actor
  exact ⟨emitted_same_source observation nontrivial half depth prior,
    same.trans (actual_candidate_packets observation nontrivial half depth start n actor (pivot start n)),
    (congrArg (OriginalRead observation nontrivial half depth start n actor) same.symm).mp original,
    actual_candidate_paid_segment observation nontrivial half depth start n actor (pivot start n),
    actual_tape_whole observation nontrivial half depth start n actor (Fin.last n),
    actual_tape_next observation nontrivial half depth start n actor (Fin.last n)⟩

#eval IO.println "CP603_CONTROL + inverse_driven_emission_carries_the_entire_original_progress"

set_option cleanup.letToHave false in
private theorem inverse_driven_run_advances_its_literal_source_and_inverse_together
    (start n : Nat) :
    let prior := drivenRun start n
    let event := newStep prior
    letI : Invertible (observe prior.source) := prior.inverse
    prior = runMatrix observation nontrivial half depth start n ∧
    prior.source = RetainedRecord.run observation nontrivial half depth start n ∧
    drivenRun start (n+1) = event.2 ∧ event.1 = emit prior ∧ event.2.source = event.1.record ∧
    event.2.determinant = prior.determinant * Block.pivot (observe prior.source)
      (birthColumn observation nontrivial half depth event.1)
      (oldActorRow observation nontrivial half depth event.1)
      (birthPrice observation nontrivial half depth event.1) ∧
    (∀ input : Fin (n+1) → ℂ, event.2.inverse.invOf *ᵥ (observe event.2.source *ᵥ input) = input) := by
  have same := run_using_inverse_actual observation nontrivial half depth start n
  have source := (congrArg MatrixState.source same).trans (run_matrix_source observation nontrivial half depth start n)
  exact ⟨same,source,rfl,rfl,rfl,rfl,
    inverse_recovers observation nontrivial half depth (newStep (drivenRun start n)).2⟩

#eval IO.println "CP603_CONTROL + inverse_driven_run_advances_its_literal_source_and_inverse_together"

set_option cleanup.letToHave false in
private def SparseWrite (start ordinal : Nat) (a : Record.Values (ordinal+1)) (b : ℂ)
    (paid : Record.Values (ordinal+1) × ℂ) : Prop :=
  let n := ordinal+1
  let decoded := decodeRecordedPrices observation nontrivial half depth start n paid.1 paid.2
  let rebuilt := rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal decoded.1,decoded.2)
  let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal a,b)
  (advanceWide c observation.mathlibZero rebuilt.1,
    advanceStock c (modelInventory observation nontrivial half rebuilt.2)) =
      (next.1,modelInventory observation nontrivial half next.2)

set_option cleanup.letToHave false in
private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
  type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

private theorem literal_whole_next (ordinal : Nat) :
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

set_option cleanup.letToHave false in
private theorem the_same_step_prices_feed_new_inverse_and_original_decoder
    (start ordinal : Nat) (a : Record.Values (ordinal+1)) (b : ℂ) :
    let n := ordinal+1
    let prior := drivenRun start n
    let actual := newStep prior
    let paid := sourceRecords observation nontrivial half depth actual.1 a b
    (actual.2.inverse.invOf *ᵥ Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => paid.1 j) paid.2 =
      Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => a j) b) ∧
    SparseWrite observation nontrivial half depth start ordinal a b paid ∧
    LiteralWholeNext observation nontrivial half depth
      (sampleSourceOrdinal observation nontrivial half depth start n (Fin.last n) (Fin.last n)) := by
  let prior := drivenRun start (ordinal+1)
  let read := fun event : Progress observation nontrivial half depth start (ordinal+1) =>
    sourceRecords observation nontrivial half depth event a b
  have values := congrArg read (emitted_same_source observation nontrivial half depth prior)
  have original : SparseWrite observation nontrivial half depth start ordinal a b (read (oldStep prior.source)) :=
    advance_writeback observation nontrivial half depth start ordinal prior.source a b
  exact ⟨step_inverse_reads observation nontrivial half depth prior a b,
    (congrArg (SparseWrite observation nontrivial half depth start ordinal a b) values.symm).mp original,
    literal_whole_next observation nontrivial half depth _⟩

#eval IO.println "CP603_CONTROL + the_same_step_prices_feed_new_inverse_and_original_decoder"

private theorem an_old_address_is_strictly_earlier_than_the_inverse_driven_emission
    {start n : Nat} (prior : MatrixState observation nontrivial half depth start n) (j : Fin n) :
    prior.source.times j < (emit prior).record.times (Fin.last n) := by
  let ready := prepare prior
  have earlier : prior.source.times j < PreparedAt.cutoff ready :=
    Nat.lt_succ_of_le (Finset.le_sup (f := prior.source.times) (mem_univ j))
  change prior.source.times j < Fin.snoc (α := fun _ : Fin (n+1) => Nat) prior.source.times
    (PreparedAt.cutoff ready+(pick ready).val) (Fin.last n)
  rw [Fin.snoc_last]
  exact earlier.trans_le (Nat.le_add_right _ _)

#eval IO.println "CP603_CONTROL - an_old_address_is_strictly_earlier_than_the_inverse_driven_emission"
#eval IO.println "CP603_GATE_PASS positive=4 negative=1"

end InverseDrivenRecordCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
