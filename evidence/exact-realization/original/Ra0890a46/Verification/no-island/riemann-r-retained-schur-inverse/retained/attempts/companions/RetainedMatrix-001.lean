import SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.MatrixBorder
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedRecord

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedMatrix

open BurnolPhysicalState Matrix
open scoped Matrix
open PacketFit RetainedRecord
open private predecessor scheduled_time_pos paidAt materialWhole material_whole_is_target from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativePrice
open private packet_whole_at from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit
open private candidateEpoch candidate_time_pos from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CandidateRead

namespace Block
export SourceGeneratedFiniteGram.MatrixBorder
  (border border_old_old border_old_new border_new_old border_new_new border_det borderInverse
   pivot columns coefficients_from_inverse)
end Block

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "packet" => Native.packet observation nontrivial half depth
local notation "raw" => Native.raw observation nontrivial half depth
local notation "original" => paidPivot observation nontrivial half depth
local notation "time" => candidateTime observation nontrivial half depth
local notation "epoch" => candidateEpoch observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "Source" => RetainedRecord.RecordAt observation nontrivial half depth
local notation "Event" => RetainedRecord.Progress observation nontrivial half depth
local notation "next" => RetainedRecord.advance observation nontrivial half depth

private def sampleAddress {start n : Nat} (current : Source start n)
    (row actor : Fin n) : Fin (current.source.last+1) :=
  ⟨actor.val+current.times row-1,Nat.lt_succ_of_le
    ((Nat.sub_le _ _).trans (current.paid actor row))⟩

/-- The complete square observation matrix reads the actual retained packet inventory. -/
def observed {start n : Nat} (current : Source start n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun row actor => packetPrice observation half (current.source.packets.get
    (sampleAddress observation nontrivial half depth current row actor)))

private theorem observed_packet {start n : Nat} (current : Source start n) (row actor : Fin n) :
    current.source.packets.get (sampleAddress observation nontrivial half depth current row actor) =
      packet (predecessor observation nontrivial half depth start n (start+actor.val) row) := by
  let index := sampleAddress observation nontrivial half depth current row actor
  have position := congrFun current.times_actual row
  have positive := scheduled_time_pos observation nontrivial half depth start n row
  have address : start+index.val = predecessor observation nontrivial half depth start n (start+actor.val) row := by
    change start+(actor.val+current.times row-1) = start+actor.val+(schedule start n).val row-1
    omega
  exact (current.source.actual index).trans (congrArg packet address)

theorem observed_entry_actual {start n : Nat} (current : Source start n) (row actor : Fin n) :
    observed observation nontrivial half depth current row actor =
      paidPriceSample observation nontrivial half depth start n (start+actor.val) row := by
  let ordinal := predecessor observation nontrivial half depth start n (start+actor.val) row
  let read (v : BurnolL2) := reader c (OriginalKCombCofinalPaAction.Q v : BurnolL2)
  have actual := (congrArg packetWhole
    (observed_packet observation nontrivial half depth current row actor)).trans
    (packet_whole_at observation nontrivial half depth ordinal)
  change read _ = read (materialWhole observation nontrivial half depth ordinal
    (paidAt observation nontrivial half depth ordinal))
  exact congrArg read (actual.trans (material_whole_is_target observation nontrivial half depth ordinal).symm)

private theorem observed_column_actual {start n : Nat} (current : Source start n) (actor : Fin n) :
    Block.columns (observed observation nontrivial half depth current) actor =
      paidPriceRecord observation nontrivial half depth start n (start+actor.val) :=
  congrArg (WithLp.toLp 2) (funext fun row => observed_entry_actual observation nontrivial half depth current row actor)

def selectedRow {start n : Nat} (event : Event start n) (actor : Fin (n+1)) : ℂ :=
  packetPrice observation half (event.selected actor).1

private theorem selected_row_actual {start n : Nat} (event : Event start n) (actor : Fin (n+1)) :
    selectedRow observation nontrivial half depth event actor =
      candidatePrice observation nontrivial half depth start n actor (original start n) :=
  (congrArg (fun pair : Packet × Packet => packetPrice observation half pair.1)
    (event.selected_actual actor)).trans
    (candidate_price_from_packets observation nontrivial half depth start n actor (original start n))

private theorem old_row {start n : Nat} (event : Event start n) (row : Fin n) (actor : Fin (n+1)) :
    observed observation nontrivial half depth event.record row.castSucc actor = event.columns actor row := by
  let a := start+actor.val
  have retained := (actual_paid_price_sample observation nontrivial half depth start (n+1) a row.castSucc).trans
    ((actual_price_record_prior observation nontrivial half depth start n (raw a) row).trans
      (actual_paid_price_sample observation nontrivial half depth start n a row).symm)
  exact (observed_entry_actual observation nontrivial half depth event.record row.castSucc actor).trans
    (retained.trans (congrArg (fun column : Record.Values n => column row) (event.columns_actual actor)).symm)

private theorem last_row {start n : Nat} (event : Event start n) (actor : Fin (n+1)) :
    observed observation nontrivial half depth event.record (Fin.last n) actor =
      selectedRow observation nontrivial half depth event actor := by
  let index := sampleAddress observation nontrivial half depth event.record (Fin.last n) actor
  have position := (congrFun event.record.times_actual (Fin.last n)).trans
    (actual_paid_pivot_time observation nontrivial half depth start n).symm
  have positive := candidate_time_pos observation nontrivial half depth start n (original start n)
  have address : start+index.val = epoch start n actor (original start n) := by
    change start+(actor.val+event.record.times (Fin.last n)-1) =
      start+actor.val+time start n (original start n)-1
    omega
  have left := (event.record.source.actual index).trans (congrArg packet address)
  have right := congrArg (fun pair : Packet × Packet => pair.1)
    ((event.selected_actual actor).trans (actual_candidate_packets observation nontrivial half depth
      start n actor (original start n)))
  exact congrArg (packetPrice observation half) (left.trans right.symm)

private def birthColumn {start n : Nat} (event : Event start n) (row : Fin n) : ℂ :=
  event.columns (Fin.last n) row

private def oldActorRow {start n : Nat} (event : Event start n) (actor : Fin n) : ℂ :=
  selectedRow observation nontrivial half depth event actor.castSucc

private def birthPrice {start n : Nat} (event : Event start n) : ℂ :=
  selectedRow observation nontrivial half depth event (Fin.last n)

local notation "observe" => observed observation nontrivial half depth
local notation "newColumn" => birthColumn observation nontrivial half depth
local notation "newRow" => oldActorRow observation nontrivial half depth
local notation "newCorner" => birthPrice observation nontrivial half depth

/-- The next complete matrix is the old matrix bordered by the same generated column and row. -/
theorem observed_next {start n : Nat} (current : Source start n) :
    let event := next current
    observe event.record = Block.border (observe current) (newColumn event) (newRow event) (newCorner event) := by
  let event := next current
  change observe event.record = Block.border (observe current) (newColumn event) (newRow event) (newCorner event)
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun row => ?_) i
  · refine Fin.lastCases ?_ (fun actor => ?_) j
    · rw [Block.border_new_new]
      exact last_row observation nontrivial half depth event (Fin.last n)
    · rw [Block.border_new_old]
      exact last_row observation nontrivial half depth event actor.castSucc
  · refine Fin.lastCases ?_ (fun actor => ?_) j
    · rw [Block.border_old_new]
      exact old_row observation nontrivial half depth event row (Fin.last n)
    · rw [Block.border_old_old]
      let read := fun column : Record.Values n => column row
      have old := congrArg read (observed_column_actual observation nontrivial half depth current actor)
      have retained := congrArg read (event.columns_actual actor.castSucc)
      exact (old_row observation nontrivial half depth event row actor.castSucc).trans (retained.trans old.symm)

private theorem inverse_fit {start n : Nat} (current : Source start n) [Invertible (observe current)]
    (event : Event start n) :
    (⅟(observe current)) *ᵥ newColumn event =
      (fun j => paidOldFit observation nontrivial half depth start n j) := by
  have columnEq : Block.columns (observe current) =
      fun j => paidPriceRecord observation nontrivial half depth start n (start+j.val) :=
    funext (observed_column_actual observation nontrivial half depth current)
  have birthEq : WithLp.toLp 2 (newColumn event) =
      paidPriceRecord observation nontrivial half depth start n (start+n) := by
    have full : WithLp.toLp 2 (newColumn event) = event.columns (Fin.last n) := by
      ext i
      rfl
    exact full.trans (event.columns_actual (Fin.last n))
  have fit : SourceGeneratedFiniteGram.Projection.coefficients (Block.columns (observe current))
      (WithLp.toLp 2 (newColumn event)) = paidOldFit observation nontrivial half depth start n := by
    unfold paidOldFit
    rw [columnEq,birthEq]
  have solved := (Block.coefficients_from_inverse (observe current) (newColumn event)).symm.trans fit
  exact congrArg (fun word : Record.Values n => fun j => word j) solved

/-- The scalar used by the block inverse is the residual selected from the actual row. -/
theorem generated_pivot {start n : Nat} (current : Source start n) [Invertible (observe current)] :
    let event := next current
    Block.pivot (observe current) (newColumn event) (newRow event) (newCorner event) =
      paidCandidateResidual observation nontrivial half depth start n (original start n) := by
  let event := next current
  dsimp only
  unfold Block.pivot
  rw [inverse_fit observation nontrivial half depth current event]
  unfold paidCandidateResidual candidateMixture
  simp only [birthPrice,oldActorRow,selected_row_actual,dotProduct,PiLp.neg_apply,neg_mul,
    Finset.sum_neg_distrib,one_mul]
  have balance :
      (∑ j : Fin n, candidatePrice observation nontrivial half depth start n j.castSucc (original start n) *
        paidOldFit observation nontrivial half depth start n j) =
      ∑ j : Fin n, paidOldFit observation nontrivial half depth start n j *
        candidatePrice observation nontrivial half depth start n j.castSucc (original start n) :=
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [balance,sub_eq_add_neg]
  exact add_comm _ _

/-- The inverse and determinant belong to the same actual retained observation record. -/
structure MatrixState (start n : Nat) where
  private mk ::
  source : Source start n
  inverse : Invertible (observe source)
  determinant : ℂ
  determinant_actual : determinant = (observe source).det

local notation "StoredMatrix" => MatrixState observation nontrivial half depth

private def emptyState (start : Nat) : StoredMatrix start 0 := by
  let initial := RetainedRecord.run observation nontrivial half depth start 0
  have emptyInverse : Invertible (observe initial) :=
    ⟨1,by apply Matrix.ext; intro i _; exact Fin.elim0 i,
      by apply Matrix.ext; intro i _; exact Fin.elim0 i⟩
  exact ⟨initial,emptyInverse,1,(Matrix.det_fin_zero (A := observe initial)).symm⟩

/-- Consume the previous inverse and the single newly emitted native row. -/
def extendMatrix {start n : Nat} (previous : StoredMatrix start n) : StoredMatrix start (n+1) := by
  let event := next previous.source
  let A := observe previous.source
  letI : Invertible A := previous.inverse
  let residual := Block.pivot A (newColumn event) (newRow event) (newCorner event)
  have live : residual ≠ 0 := fun zero =>
    actual_paid_pivot_live observation nontrivial half depth start n
      ((generated_pivot observation nontrivial half depth previous.source).symm.trans zero)
  let assembled := Block.border A (newColumn event) (newRow event) (newCorner event)
  have installed : observe event.record = assembled :=
    observed_next observation nontrivial half depth previous.source
  let inverse : Invertible assembled := Block.borderInverse A (newColumn event) (newRow event)
    (newCorner event) (isUnit_iff_ne_zero.mpr live)
  have determinant : previous.determinant*residual = (observe event.record).det := calc
    _ = A.det*residual := congrArg (fun value => value*residual) previous.determinant_actual
    _ = assembled.det := (Block.border_det A (newColumn event) (newRow event) (newCorner event)).symm
    _ = (observe event.record).det := congrArg Matrix.det installed.symm
  exact ⟨event.record,
    Eq.mp (congrArg (fun matrix : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => Invertible matrix) installed.symm) inverse,
    previous.determinant*residual,determinant⟩

def runMatrix (start : Nat) : (n : Nat) → StoredMatrix start n :=
  Nat.rec (motive := StoredMatrix start) (emptyState observation nontrivial half depth start)
    (fun _ previous => extendMatrix observation nontrivial half depth previous)

theorem run_matrix_source (start n : Nat) :
    (runMatrix observation nontrivial half depth start n).source =
      RetainedRecord.run observation nontrivial half depth start n := by
  induction n with
  | zero => rfl
  | succ n prior =>
    change (next (runMatrix observation nontrivial half depth start n).source).record =
      (next (RetainedRecord.run observation nontrivial half depth start n)).record
    exact congrArg (fun old : Source start n => (next old).record) prior

theorem determinant_update {start n : Nat} (previous : StoredMatrix start n) :
    let event := next previous.source
    letI : Invertible (observe previous.source) := previous.inverse
    (extendMatrix observation nontrivial half depth previous).determinant =
      previous.determinant * Block.pivot (observe previous.source)
        (newColumn event) (newRow event) (newCorner event) :=
  rfl

theorem inverse_recovers {start n : Nat} (current : StoredMatrix start n) (input : Fin n → ℂ) :
    current.inverse.invOf *ᵥ ((observe current.source) *ᵥ input) = input := by
  letI : Invertible (observe current.source) := current.inverse
  change (⅟(observe current.source)) *ᵥ ((observe current.source) *ᵥ input) = input
  rw [Matrix.mulVec_mulVec,invOf_mul_self,Matrix.one_mulVec]

open private mix from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketSelection

/-- The matrix action gives the same old and selected values consumed by the original sparse decoder. -/
theorem matrix_observes_records {start n : Nat} (current : Source start n)
    (a : Record.Values n) (b : ℂ) :
    let event := next current
    let paid := sourceRecords observation nontrivial half depth event a b
    observe event.record *ᵥ Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => a j) b =
      Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => paid.1 j) paid.2 := by
  let event := next current
  dsimp only
  funext i
  rw [Matrix.mulVec_apply_eq_sum,Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun row => ?_) i
  · simp only [Fin.snoc_castSucc,Fin.snoc_last,last_row,sourceRecords,mix,selectedRow]
    exact congrArg₂ (·+·)
      (Finset.sum_congr rfl (fun j _ => mul_comm _ _)) (mul_comm _ _)
  · simp only [Fin.snoc_castSucc,Fin.snoc_last,old_row,sourceRecords,WithLp.ofLp_add,Pi.add_apply,
      WithLp.ofLp_smul,WithLp.ofLp_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact congrArg₂ (·+·)
      (Finset.sum_congr rfl (fun j _ => mul_comm _ _)) (mul_comm _ _)

theorem extend_matrix_source {start n : Nat} (previous : StoredMatrix start n) :
    (extendMatrix observation nontrivial half depth previous).source = (next previous.source).record :=
  rfl

/-- The updated matrix inverse directly decodes the two actual emitted price records. -/
theorem inverse_reads_emitted {start n : Nat} (previous : StoredMatrix start n)
    (a : Record.Values n) (b : ℂ) :
    let updated := extendMatrix observation nontrivial half depth previous
    let paid := sourceRecords observation nontrivial half depth (next previous.source) a b
    updated.inverse.invOf *ᵥ Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => paid.1 j) paid.2 =
      Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => a j) b := by
  let updated := extendMatrix observation nontrivial half depth previous
  let input := Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => a j) b
  have fromSource := congrArg (fun source : Source start (n+1) => observe source *ᵥ input)
    (extend_matrix_source observation nontrivial half depth previous)
  have reads := fromSource.trans (matrix_observes_records observation nontrivial half depth previous.source a b)
  exact (congrArg (fun price => updated.inverse.invOf *ᵥ price) reads.symm).trans
    (inverse_recovers observation nontrivial half depth updated input)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedMatrix
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
