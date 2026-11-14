import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketSelection

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedRecord

open BurnolPhysicalState Finset RootInquiryCompletion SourceNativeInquiryRuntime
open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot
open PacketFit
open private nativeLanguage from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private oldAddress old_column_actual from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit
open private candidateEpoch from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CandidateRead
open private earlier_zero from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketSelection
open private nextCutoff from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord
open private oldFit from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedResidualProbe
open private toRange from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "packet" => Native.packet observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "cut" => sourceCutoff observation nontrivial half depth
local notation "Offsets" => CandidateOffsets observation nontrivial half depth
local notation "time" => candidateTime observation nontrivial half depth
local notation "epoch" => candidateEpoch observation nontrivial half depth
local notation "original" => paidPivot observation nontrivial half depth

/-- Full original admission packets carried across successive observations of one fixed source. -/
structure PacketPrefix (start : Nat) where
  private mk ::
  last : Nat
  packets : Vector Packet (last+1)
  actual : ∀ i : Fin (last+1), packets.get i = packet (start+i.val)

local notation "Prefix" => PacketPrefix observation nontrivial half depth

private def carryTo {start : Nat} (held : Prefix start) (required : Nat) : Prefix start := by
  let extra := required-held.last
  refine ⟨held.last+extra,Table.extend factory held.packets extra,?_⟩
  have old (j : Fin (held.last+1)) : held.packets.get j =
      Table.packetAt factory initial cfg language (start+1+j.val) :=
    (held.actual j).trans (congrArg (Table.packetAt factory initial cfg language) (by omega))
  intro i
  exact (Table.actual_at_extend factory initial cfg language (start+1) held.packets old extra i).trans
    (congrArg (Table.packetAt factory initial cfg language) (by omega))

private theorem carried_covers {start : Nat} (held : Prefix start) (required : Nat) :
    required ≤ (carryTo observation nontrivial half depth held required).last := by
  change required ≤ held.last+(required-held.last)
  omega

/-- The previous row addresses and their paid packet inventory are carried as data. -/
structure RecordAt (start count : Nat) where
  private mk ::
  source : Prefix start
  times : Fin count → Nat
  times_actual : times = (schedule start count).val
  paid : ∀ actor row : Fin count, actor.val+times row ≤ source.last

local notation "RecordAtSource" => RecordAt observation nontrivial half depth

private def seed (start : Nat) : RecordAtSource start 0 where
  source := ⟨0,Vector.singleton (packet start),fun i => by rw [Fin.eq_zero i]; rfl⟩
  times := Fin.elim0
  times_actual := funext (fun i => Fin.elim0 i)
  paid := fun actor _ => Fin.elim0 actor

private def oldStop {start count : Nat} (previous : RecordAtSource start count) : Nat :=
  count+Finset.univ.sup previous.times-1

private def beforeAddress {start count : Nat} (previous : RecordAtSource start count)
    (source : Prefix start) (covered : oldStop observation nontrivial half depth previous ≤ source.last)
    (actor : Fin (count+1)) (row : Fin count) : Fin (source.last+1) := by
  refine ⟨actor.val+previous.times row-1,Nat.lt_succ_of_le ?_⟩
  have actorWithin := Nat.le_of_lt_succ actor.isLt
  have timeWithin : previous.times row ≤ Finset.univ.sup previous.times :=
    Finset.le_sup (f := previous.times) (Finset.mem_univ row)
  unfold oldStop at covered
  omega

private def oldColumnFrom {start count : Nat} (previous : RecordAtSource start count)
    (source : Prefix start) (covered : oldStop observation nontrivial half depth previous ≤ source.last)
    (actor : Fin (count+1)) : Record.Values count :=
  WithLp.toLp 2 (fun row => packetPrice observation half (source.packets.get
    (beforeAddress observation nontrivial half depth previous source covered actor row)))

private theorem old_column_from_actual {start count : Nat} (previous : RecordAtSource start count)
    (source : Prefix start) (covered : oldStop observation nontrivial half depth previous ≤ source.last)
    (actor : Fin (count+1)) :
    oldColumnFrom observation nontrivial half depth previous source covered actor =
      paidPriceRecord observation nontrivial half depth start count (start+actor.val) := by
  refine (Eq.trans ?_ (old_column_actual observation nontrivial half depth start count actor))
  apply congrArg (WithLp.toLp 2)
  funext row
  apply congrArg (packetPrice observation half)
  let atOld := beforeAddress observation nontrivial half depth previous source covered actor row
  let atPaid := oldAddress observation nontrivial half depth start count actor row
  have same : start+atOld.val = start+atPaid.val := by
    change start+(actor.val+previous.times row-1) = start+(actor.val+(schedule start count).val row-1)
    rw [previous.times_actual]
  exact (source.actual atOld).trans ((congrArg packet same).trans
    (prepared_packet_at observation nontrivial half depth start count atPaid).symm)

private structure PreparedAt (start count : Nat) where
  source : Prefix start
  cutoff : Nat
  fuel : Nat
  columns : Fin (count+1) → Record.Values count
  fit : Record.Values count
  covers : count+cutoff+fuel ≤ source.last
  cutoff_actual : cutoff = cut start count
  fuel_actual : fuel = residualFuel observation nontrivial half depth start count (cut start count)
  columns_actual : ∀ actor, columns actor = paidPriceRecord observation nontrivial half depth start count (start+actor.val)
  fit_actual : fit = paidOldFit observation nontrivial half depth start count

local notation "Ready" => PreparedAt observation nontrivial half depth

private def prepare {start count : Nat} (previous : RecordAtSource start count) : Ready start count := by
  let before := carryTo observation nontrivial half depth previous.source (oldStop observation nontrivial half depth previous)
  have covered := carried_covers observation nontrivial half depth previous.source
    (oldStop observation nontrivial half depth previous)
  let columns := oldColumnFrom observation nontrivial half depth previous before covered
  let fit := Fit.coefficients (fun j : Fin count => columns j.castSucc) (columns (Fin.last count))
  have columnEq (actor : Fin (count+1)) :
      columns actor = paidPriceRecord observation nontrivial half depth start count (start+actor.val) :=
    old_column_from_actual observation nontrivial half depth previous before covered actor
  have fitEq : fit = paidOldFit observation nontrivial half depth start count := by
    simp only [fit,paidOldFit,columnEq,Fin.val_castSucc,Fin.val_last]
  let cutoff := nextCutoff previous.times
  have sameCut : cutoff = cut start count := by
    simp only [cutoff,sourceCutoff,previous.times_actual]
  let fuel := probeFuel observation half (probeBase observation start cutoff) count
    (Fin.snoc (fun j => -fit j) 1) (‖xiOpening observation half‖/4)
  have sameFuel : fuel = residualFuel observation nontrivial half depth start count (cut start count) := by
    simp only [fuel,sameCut,fitEq,residualFuel,fittedCoefficients,oldFit,actual_paid_old_fit]
  let bound := count+cutoff+fuel
  let completed := carryTo observation nontrivial half depth before bound
  exact ⟨completed,cutoff,fuel,columns,fit,carried_covers observation nontrivial half depth before bound,
    sameCut,sameFuel,columnEq,fitEq⟩

private theorem cutoff_positive (start count : Nat) : 0 < cut start count := by
  unfold sourceCutoff nextCutoff
  omega

private def nativeAddress {start count : Nat} (ready : Ready start count)
    (actor : Fin (count+1)) (offset : Fin (ready.fuel+1)) : Fin ready.source.last := by
  refine ⟨actor.val+ready.cutoff+offset.val-1,?_⟩
  have actorWithin := Nat.le_of_lt_succ actor.isLt
  have offsetWithin := Nat.le_of_lt_succ offset.isLt
  have bound := ready.covers
  have positive : 0 < ready.cutoff := by
    rw [ready.cutoff_actual]
    exact cutoff_positive observation nontrivial half depth start count
  omega

private def candidateFrom {start count : Nat} (ready : Ready start count)
    (actor : Fin (count+1)) (offset : Fin (ready.fuel+1)) : Packet × Packet :=
  let i := nativeAddress observation nontrivial half depth ready actor offset
  (ready.source.packets.get i.castSucc,ready.source.packets.get i.succ)

private def originalOffset {start count : Nat} (ready : Ready start count)
    (offset : Fin (ready.fuel+1)) : Offsets start count :=
  offset.cast (congrArg (·+1) ready.fuel_actual)

private theorem candidate_from_actual {start count : Nat} (ready : Ready start count)
    (actor : Fin (count+1)) (offset : Fin (ready.fuel+1)) :
    candidateFrom observation nontrivial half depth ready actor offset =
      candidatePackets observation nontrivial half depth start count actor
        (originalOffset observation nontrivial half depth ready offset) := by
  rw [actual_candidate_packets]
  let index := nativeAddress observation nontrivial half depth ready actor offset
  let originalIndex := originalOffset observation nontrivial half depth ready offset
  have sameCut := ready.cutoff_actual
  have positive := cutoff_positive observation nontrivial half depth start count
  have address : start+index.val = epoch start count actor originalIndex := by
    change start+(actor.val+ready.cutoff+offset.val-1) =
      start+actor.val+(cut start count+offset.val)-1
    omega
  exact Prod.ext ((ready.source.actual index.castSucc).trans (congrArg packet address))
    ((ready.source.actual index.succ).trans
      (congrArg packet (by rw [Fin.val_succ,← Nat.add_assoc,address])))

open private mix from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketSelection

private def residualFrom {start count : Nat} (ready : Ready start count)
    (offset : Fin (ready.fuel+1)) : ℂ :=
  mix (fun actor => packetPrice observation half (candidateFrom observation nontrivial half depth ready actor offset).1)
    (-ready.fit) 1

private theorem residual_from_actual {start count : Nat} (ready : Ready start count)
    (offset : Fin (ready.fuel+1)) :
    residualFrom observation nontrivial half depth ready offset =
      paidCandidateResidual observation nontrivial half depth start count
        (originalOffset observation nontrivial half depth ready offset) := by
  unfold residualFrom mix paidCandidateResidual candidateMixture
  simp only [candidate_from_actual,candidate_price_from_packets,ready.fit_actual]

private def scan {start count : Nat} (ready : Ready start count) : Option (Fin (ready.fuel+1)) := by
  classical
  exact Fin.find? (fun i => decide (residualFrom observation nontrivial half depth ready i ≠ 0))

private theorem scan_actual {start count : Nat} (ready : Ready start count) :
    scan observation nontrivial half depth ready =
      some ((original start count).cast (congrArg (·+1) ready.fuel_actual.symm)) := by
  classical
  let chosen := (original start count).cast (congrArg (·+1) ready.fuel_actual.symm)
  have same : originalOffset observation nontrivial half depth ready chosen = original start count := Fin.ext rfl
  have payment : residualFrom observation nontrivial half depth ready chosen =
      paidCandidateResidual observation nontrivial half depth start count (original start count) :=
    (residual_from_actual observation nontrivial half depth ready chosen).trans
      (congrArg (paidCandidateResidual observation nontrivial half depth start count) same)
  have live : residualFrom observation nontrivial half depth ready chosen ≠ 0 :=
    fun erased => actual_paid_pivot_live observation nontrivial half depth start count (payment.symm.trans erased)
  have earlier (j : Fin (ready.fuel+1)) (less : j < chosen) :
      residualFrom observation nontrivial half depth ready j = 0 := by
    have old : originalOffset observation nontrivial half depth ready j < original start count := less
    exact (residual_from_actual observation nontrivial half depth ready j).trans
      (earlier_zero observation nontrivial half depth start count
        (originalOffset observation nontrivial half depth ready j) old)
  apply Option.mem_def.mp
  unfold scan
  exact Fin.mem_find?_iff.mpr ⟨decide_eq_true live,fun j less accepted =>
    (of_decide_eq_true accepted) (earlier j less)⟩


private theorem prepare_old_time_le {start count : Nat}
    (previous : RecordAtSource start count) (row : Fin count) :
    previous.times row ≤ (prepare observation nontrivial half depth previous).cutoff := by
  change previous.times row ≤ nextCutoff previous.times
  exact Nat.le_succ_of_le (Finset.le_sup (f := previous.times) (Finset.mem_univ row))

private def firstFrom {start count : Nat} (ready : Ready start count) : Fin (ready.fuel+1) :=
  (scan observation nontrivial half depth ready).get
    (Option.isSome_of_eq_some (scan_actual observation nontrivial half depth ready))

private theorem first_value_actual {start count : Nat} (ready : Ready start count) :
    (firstFrom observation nontrivial half depth ready).val = (original start count).val :=
  congrArg Fin.val (Option.get_of_eq_some _ (scan_actual observation nontrivial half depth ready))

private theorem first_time_actual {start count : Nat} (ready : Ready start count) :
    ready.cutoff+(firstFrom observation nontrivial half depth ready).val =
      (schedule start (count+1)).val (Fin.last count) := by
  rw [ready.cutoff_actual,first_value_actual]
  exact actual_paid_pivot_time observation nontrivial half depth start count

private theorem first_packets_actual {start count : Nat} (ready : Ready start count) (actor : Fin (count+1)) :
    candidateFrom observation nontrivial half depth ready actor (firstFrom observation nontrivial half depth ready) =
      candidatePackets observation nontrivial half depth start count actor (original start count) := by
  let picked := firstFrom observation nontrivial half depth ready
  let index := nativeAddress observation nontrivial half depth ready actor picked
  have sameTime : ready.cutoff+picked.val = time start count (original start count) :=
    congrArg₂ Nat.add ready.cutoff_actual (first_value_actual observation nontrivial half depth ready)
  have positive := cutoff_positive observation nontrivial half depth start count
  have cutoffEq := ready.cutoff_actual
  have address : start+index.val = epoch start count actor (original start count) := by
    change start+(actor.val+ready.cutoff+picked.val-1) =
      start+actor.val+time start count (original start count)-1
    omega
  have atNext : start+index.succ.val = epoch start count actor (original start count)+1 := by
    rw [Fin.val_succ,← Nat.add_assoc,address]
  have matched :
      candidateFrom observation nontrivial half depth ready actor picked =
        (packet (epoch start count actor (original start count)),
          packet (epoch start count actor (original start count)+1)) :=
    Prod.ext ((ready.source.actual index.castSucc).trans (congrArg packet address))
      ((ready.source.actual index.succ).trans (congrArg packet atNext))
  exact matched.trans
    (actual_candidate_packets observation nontrivial half depth start count actor (original start count)).symm


/-- One advance retains the entire next record and the full selected source row. -/
structure Progress (start count : Nat) where
  private mk ::
  record : RecordAtSource start (count+1)
  columns : Fin (count+1) → Record.Values count
  selected : Fin (count+1) → Packet × Packet
  columns_actual : ∀ actor, columns actor = paidPriceRecord observation nontrivial half depth start count (start+actor.val)
  selected_actual : ∀ actor, selected actor =
    candidatePackets observation nontrivial half depth start count actor (original start count)

local notation "ProgressAt" => Progress observation nontrivial half depth

def advance {start count : Nat} (previous : RecordAtSource start count) : ProgressAt start count := by
  let ready := prepare observation nontrivial half depth previous
  let picked := firstFrom observation nontrivial half depth ready
  let latest := ready.cutoff+picked.val
  refine ⟨⟨ready.source,Fin.snoc previous.times latest,?_,?_⟩,ready.columns,
    (fun actor => candidateFrom observation nontrivial half depth ready actor picked),ready.columns_actual,?_⟩
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      exact first_time_actual observation nontrivial half depth ready
    · simp only [Fin.snoc_castSucc,previous.times_actual,priceSchedule,Record.schedule_prior]
  · intro actor row
    have actorWithin := Nat.le_of_lt_succ actor.isLt
    have covered := ready.covers
    have offsetWithin := Nat.le_of_lt_succ picked.isLt
    refine Fin.lastCases ?_ (fun j => ?_) row
    · rw [Fin.snoc_last]
      dsimp only [latest]
      omega
    · rw [Fin.snoc_castSucc]
      have older : previous.times j ≤ ready.cutoff :=
        prepare_old_time_le observation nontrivial half depth previous j
      omega
  · exact first_packets_actual observation nontrivial half depth ready

/-- Every rank is generated by its literal retained predecessor record. -/
def run (start : Nat) : (count : Nat) → RecordAtSource start count :=
  Nat.rec (motive := RecordAtSource start) (seed observation nontrivial half depth start)
    (fun _ previous => (advance observation nontrivial half depth previous).record)

private theorem prepare_grows {start count : Nat} (previous : RecordAtSource start count) :
    previous.source.last ≤ (prepare observation nontrivial half depth previous).source.last := by
  let before := carryTo observation nontrivial half depth previous.source
    (oldStop observation nontrivial half depth previous)
  have previousWithin : previous.source.last ≤ before.last := Nat.le_add_right _ _
  have extended : before.last ≤ (prepare observation nontrivial half depth previous).source.last :=
    Nat.le_add_right _ _
  exact previousWithin.trans extended

theorem advance_retains {start count : Nat} (previous : RecordAtSource start count) :
    let next := (advance observation nontrivial half depth previous).record
    (∀ j : Fin count, next.times j.castSucc = previous.times j) ∧
      ∃ within : previous.source.last+1 ≤ next.source.last+1,
        ∀ j : Fin (previous.source.last+1),
          next.source.packets.get (j.castLE within) = previous.source.packets.get j := by
  dsimp only
  refine ⟨?_,⟨Nat.succ_le_succ (prepare_grows observation nontrivial half depth previous),?_⟩⟩
  · intro j
    let ready := prepare observation nontrivial half depth previous
    change Fin.snoc (α := fun _ : Fin (count+1) => Nat) previous.times
      (ready.cutoff+(firstFrom observation nontrivial half depth ready).val) j.castSucc = previous.times j
    simp only [Fin.snoc_castSucc]
  · intro j
    exact ((advance observation nontrivial half depth previous).record.source.actual _).trans
      (previous.source.actual j).symm

/-- The actual next record and the inverse consumer share the emitted source batch. -/
def sourceRecords {start count : Nat} (event : ProgressAt start count)
    (a : Record.Values count) (b : ℂ) : Record.Values count × ℂ :=
  ((∑ j : Fin count, a j • event.columns j.castSucc)+b • event.columns (Fin.last count),
    mix (fun actor => packetPrice observation half (event.selected actor).1) a b)

theorem advance_records_actual {start count : Nat} (previous : RecordAtSource start count)
    (a : Record.Values count) (b : ℂ) :
    sourceRecords observation nontrivial half depth (advance observation nontrivial half depth previous) a b =
      (paidMixtureRecord observation nontrivial half depth start count count a b,
        candidateMixture observation nontrivial half depth start count (original start count) a b) := by
  let event := advance observation nontrivial half depth previous
  have old : event.columns =
      fun actor => paidPriceRecord observation nontrivial half depth start count (start+actor.val) :=
    funext event.columns_actual
  have latest : (fun actor => packetPrice observation half (event.selected actor).1) =
      fun actor => candidatePrice observation nontrivial half depth start count actor (original start count) := by
    funext actor
    exact (congrArg (fun both : Packet × Packet => packetPrice observation half both.1)
      (event.selected_actual actor)).trans
      (candidate_price_from_packets observation nontrivial half depth start count actor (original start count))
  change ((∑ j : Fin count, a j • event.columns j.castSucc)+b • event.columns (Fin.last count),
    mix (fun actor => packetPrice observation half (event.selected actor).1) a b) = _
  rw [old,latest]; rfl

/-- Read the sparse inverse from the actual accumulated row and write both original inventories. -/
theorem advance_writeback (start ordinal : Nat) (previous : RecordAtSource start (ordinal+1))
    (a : Record.Values (ordinal+1)) (b : ℂ) :
    let count := ordinal+1
    let paid := sourceRecords observation nontrivial half depth (advance observation nontrivial half depth previous) a b
    let decoded := decodeRecordedPrices observation nontrivial half depth start count paid.1 paid.2
    let rebuilt := rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal decoded.1,decoded.2)
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal a,b)
    (advanceWide c observation.mathlibZero rebuilt.1,
      advanceStock c (modelInventory observation nontrivial half rebuilt.2)) =
      (next.1,modelInventory observation nontrivial half next.2) := by
  dsimp only
  rw [advance_records_actual]
  exact actual_selected_paid_writeback observation nontrivial half depth start ordinal a b

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedRecord
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
