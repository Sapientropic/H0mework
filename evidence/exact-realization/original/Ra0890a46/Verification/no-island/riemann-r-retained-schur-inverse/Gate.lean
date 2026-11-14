import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedMatrix
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace MatrixBorderCertificate
open Matrix
open scoped Matrix

namespace B
export SourceGeneratedFiniteGram.MatrixBorder
  (border border_old_old border_old_new border_new_old border_new_new pivot border_det borderInverse)
end B

set_option cleanup.letToHave false in
private theorem emitted_border_has_all_four_blocks_and_the_full_inverse
    {R : Type u} [CommRing R] {n : Nat}
    (old : Matrix (Fin n) (Fin n) R) [Invertible old]
    (right bottom : Fin n → R) (corner : R) (paid : IsUnit (B.pivot old right bottom corner)) :
    let assembled := B.border old right bottom corner
    let recovered := B.borderInverse old right bottom corner paid
    (∀ i j : Fin n, assembled i.castSucc j.castSucc = old i j) ∧
    (∀ i : Fin n, assembled i.castSucc (Fin.last n) = right i) ∧
    (∀ j : Fin n, assembled (Fin.last n) j.castSucc = bottom j) ∧
    assembled (Fin.last n) (Fin.last n) = corner ∧
    assembled.det = old.det * (corner - dotProduct bottom ((⅟old) *ᵥ right)) ∧
    assembled * recovered.invOf = 1 ∧ recovered.invOf * assembled = 1 := by
  let recovered := B.borderInverse old right bottom corner paid
  exact ⟨B.border_old_old old right bottom corner,
    B.border_old_new old right bottom corner,
    B.border_new_old old right bottom corner,
    B.border_new_new old right bottom corner,
    B.border_det old right bottom corner,recovered.mul_invOf_self,recovered.invOf_mul_self⟩

#eval IO.println "CP602_CONTROL + emitted_border_has_all_four_blocks_and_the_full_inverse"

private theorem a_predicted_corner_makes_this_same_border_singular
    {R : Type u} [CommRing R] {n : Nat}
    (old : Matrix (Fin n) (Fin n) R) [Invertible old] (right bottom : Fin n → R) :
    (B.border old right bottom (dotProduct bottom ((⅟old) *ᵥ right))).det = 0 := by
  rw [B.border_det]
  simp only [B.pivot,sub_self,mul_zero]

#eval IO.println "CP602_CONTROL - a_predicted_corner_makes_this_same_border_singular"

end MatrixBorderCertificate

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace RetainedMatrixCertificate

open BurnolPhysicalState Matrix
open scoped Matrix
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedRecord
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedMatrix
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
  (actual_relation_stock_next modelInventory advanceStock)
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)

open private birthColumn oldActorRow birthPrice from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedMatrix
open private toRange from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "observe" => observed observation nontrivial half depth
local notation "step" => RetainedRecord.advance observation nontrivial half depth
local notation "right" => birthColumn observation nontrivial half depth
local notation "bottom" => oldActorRow observation nontrivial half depth
local notation "corner" => birthPrice observation nontrivial half depth
local notation "pick" => paidPivot observation nontrivial half depth
local notation "matrixRun" => runMatrix observation nontrivial half depth
local notation "matrixStep" => extendMatrix observation nontrivial half depth

set_option cleanup.letToHave false in
private theorem one_actual_event_supplies_the_bordered_observation_and_paid_pivot
    {start n : Nat} (prior : RecordAt observation nontrivial half depth start n)
    [Invertible (observe prior)] :
    let event := step prior
    (∀ i : Fin n, right event i = event.columns (Fin.last n) i) ∧
    (∀ j : Fin n, bottom event j = selectedRow observation nontrivial half depth event j.castSucc) ∧
    corner event = selectedRow observation nontrivial half depth event (Fin.last n) ∧
    observe event.record = Block.border (observe prior) (right event) (bottom event) (corner event) ∧
    Block.pivot (observe prior) (right event) (bottom event) (corner event) =
      paidCandidateResidual observation nontrivial half depth start n (pick start n) :=
  ⟨fun _ => rfl,fun _ => rfl,rfl,observed_next observation nontrivial half depth prior,
    generated_pivot observation nontrivial half depth prior⟩

#eval IO.println "CP602_CONTROL + one_actual_event_supplies_the_bordered_observation_and_paid_pivot"

set_option cleanup.letToHave false in
private theorem original_matrix_run_keeps_the_source_and_updates_its_stored_inverse
    (start n : Nat) :
    let prior := matrixRun start n
    let event := step prior.source
    let current := matrixRun start (n+1)
    letI : Invertible (observe prior.source) := prior.inverse
    prior.source = RetainedRecord.run observation nontrivial half depth start n ∧
    current = matrixStep prior ∧ current.source = event.record ∧
    current.determinant = prior.determinant *
      Block.pivot (observe prior.source) (right event) (bottom event) (corner event) ∧
    (∀ input : Fin (n+1) → ℂ, current.inverse.invOf *ᵥ (observe current.source *ᵥ input) = input) :=
  ⟨run_matrix_source observation nontrivial half depth start n,rfl,
    extend_matrix_source observation nontrivial half depth (matrixRun start n),
    determinant_update observation nontrivial half depth (matrixRun start n),
    inverse_recovers observation nontrivial half depth (matrixRun start (n+1))⟩

#eval IO.println "CP602_CONTROL + original_matrix_run_keeps_the_source_and_updates_its_stored_inverse"

set_option cleanup.letToHave false in
private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
  type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

private theorem literal_whole_next (ordinal : Nat) :
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

set_option cleanup.letToHave false in
private theorem the_same_emitted_values_feed_both_matrix_and_original_sparse_consumers
    (start ordinal : Nat) (a : Record.Values (ordinal+1)) (b : ℂ) :
    let n := ordinal+1
    let prior := matrixRun start n
    let event := step prior.source
    let updated := matrixStep prior
    let paid := sourceRecords observation nontrivial half depth event a b
    let decoded := decodeRecordedPrices observation nontrivial half depth start n paid.1 paid.2
    let rebuilt := rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal decoded.1,decoded.2)
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal a,b)
    (updated.inverse.invOf *ᵥ Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => paid.1 j) paid.2 =
      Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => a j) b) ∧
    ((advanceWide c observation.mathlibZero rebuilt.1,
      advanceStock c (modelInventory observation nontrivial half rebuilt.2)) =
        (next.1,modelInventory observation nontrivial half next.2)) ∧
    LiteralWholeNext observation nontrivial half depth
      (sampleSourceOrdinal observation nontrivial half depth start n (Fin.last n) (Fin.last n)) :=
  ⟨inverse_reads_emitted observation nontrivial half depth (matrixRun start (ordinal+1)) a b,
    advance_writeback observation nontrivial half depth start ordinal (matrixRun start (ordinal+1)).source a b,
    literal_whole_next observation nontrivial half depth _⟩

#eval IO.println "CP602_CONTROL + the_same_emitted_values_feed_both_matrix_and_original_sparse_consumers"
#eval IO.println "CP602_GATE_PASS positive=4 negative=1"

end RetainedMatrixCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
