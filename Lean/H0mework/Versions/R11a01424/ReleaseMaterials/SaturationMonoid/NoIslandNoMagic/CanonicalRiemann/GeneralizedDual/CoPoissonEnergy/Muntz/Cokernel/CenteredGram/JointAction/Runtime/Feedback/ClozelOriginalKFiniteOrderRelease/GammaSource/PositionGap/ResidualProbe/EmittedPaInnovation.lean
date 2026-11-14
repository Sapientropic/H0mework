import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.InverseDrivenRecord
import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FinitePaGraphInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.EmittedPaInnovation

open BurnolPhysicalState Finset
open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot
open PacketFit RetainedRecord RetainedMatrix
open scoped InnerProductSpace

open private candidateEpoch candidate_time_pos from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CandidateRead
open private packet_whole_at from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit
open private original_K_separates from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse
open private toRange from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback

namespace Fit
export SourceGeneratedFiniteGram.Projection
  (synthesis sourceSpan innovationCLM innovation_ne_zero_of_new_column insertedCoefficient
    coefficients insertion_read innovation_value predictable_mem)
end Fit

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "E" => OriginalKCombCofinalPaAction.E
local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "raw" => Native.raw observation nontrivial half depth
local notation "R" => OriginalKCombPhysicalAction.R observation nontrivial half
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "Event" => RetainedRecord.Progress observation nontrivial half depth
local notation "Stored" => RetainedMatrix.MatrixState observation nontrivial half depth
local notation "advance" => InverseDrivenRecord.step observation nontrivial half depth
local notation "pivotAt" => paidPivot observation nontrivial half depth
local notation "clockAt" => candidateTime observation nontrivial half depth

/-- Both physical columns are evaluated from the four actual action branches of the paid packets. -/
def physicalPair {start n : Nat} (event : Event start n) (actor : Fin (n+1)) :
    BurnolPaAmbientCarrier × BurnolPaAmbientCarrier :=
  let pair := event.selected actor
  (E (packetWhole pair.1), E (packetWhole pair.2))

private theorem paid_raw_pair {start n : Nat} (event : Event start n) (actor : Fin (n+1)) :
    let clock := clockAt start n (pivotAt start n)
    Prod.map packetWhole packetWhole (event.selected actor) =
      (raw (start+actor.val+clock), raw (start+actor.val+clock+1)) := by
  let picked := pivotAt start n
  let clock := clockAt start n picked
  let ordinal := candidateEpoch observation nontrivial half depth start n actor picked
  have matched := (event.selected_actual actor).trans
    (actual_candidate_packets observation nontrivial half depth start n actor picked)
  have positive := candidate_time_pos observation nontrivial half depth start n picked
  have address : ordinal+1 = start+actor.val+clock := by
    change 0 < clock at positive
    change (start+actor.val+clock-1)+1 = _
    omega
  have target (packetIndex : Nat) :
      packetWhole (Native.packet observation nontrivial half depth packetIndex) = raw (packetIndex+1) :=
    (packet_whole_at observation nontrivial half depth packetIndex).trans
      (OriginalKDirectRCofinalCalculatedSource.calculated_target_raw observation nontrivial half depth packetIndex)
  exact Prod.ext
    ((congrArg (fun pair : Packet × Packet => packetWhole pair.1) matched).trans
      ((target ordinal).trans (congrArg raw address)))
    ((congrArg (fun pair : Packet × Packet => packetWhole pair.2) matched).trans
      ((target (ordinal+1)).trans (congrArg (fun index => raw (index+1)) address)))

theorem physical_pair_actual {start n : Nat} (event : Event start n) (actor : Fin (n+1)) :
    let clock := clockAt start n (pivotAt start n)
    physicalPair observation nontrivial half depth event actor =
      (pa (start+actor.val+clock), pa (start+actor.val+clock+1)) := by
  let ordinal := start+actor.val+clockAt start n (pivotAt start n)
  have paid : Prod.map packetWhole packetWhole (event.selected actor) =
      (raw ordinal, raw (ordinal+1)) :=
    paid_raw_pair observation nontrivial half depth event actor
  have before : packetWhole (event.selected actor).1 = raw ordinal := congrArg Prod.fst paid
  have after : packetWhole (event.selected actor).2 = raw (ordinal+1) := congrArg Prod.snd paid
  have first : (physicalPair observation nontrivial half depth event actor).1 = pa ordinal :=
    congrArg (fun value : BurnolL2 => E value) before
  have second : (physicalPair observation nontrivial half depth event actor).2 = pa (ordinal+1) :=
    congrArg (fun value : BurnolL2 => E value) after
  exact Prod.ext first second

/-- The same old full packet supplies the invisible contribution to the next Pa column. -/
theorem physical_reentry_actual {start n : Nat} (event : Event start n) (actor : Fin (n+1)) :
    let pair := physicalPair observation nontrivial half depth event actor
    let old := packetWhole (event.selected actor).1
    pair.2 - E (R (pair.1 : BurnolL2)) = E (R (OriginalKCombCofinalPaAction.invisible old)) := by
  let ordinal := start+actor.val+clockAt start n (pivotAt start n)
  have matched : physicalPair observation nontrivial half depth event actor =
      (pa ordinal,pa (ordinal+1)) :=
    physical_pair_actual observation nontrivial half depth event actor
  have full : packetWhole (event.selected actor).1 = raw ordinal :=
    congrArg Prod.fst (paid_raw_pair observation nontrivial half depth event actor)
  let difference (pair : BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) :=
    pair.2 - E (R (pair.1 : BurnolL2))
  let reentry (value : BurnolL2) := E (R (OriginalKCombCofinalPaAction.invisible value))
  exact ((congrArg difference matched).trans
    (OriginalKCombCofinalPaAction.actual_defect_value observation nontrivial half depth ordinal)).trans
    (congrArg reentry full.symm)

private theorem actual_rank (start n clock : Nat) :
    LinearIndependent ℂ (fun i : Fin (n+1) => pa (start+i.val+clock)) :=
  (LocalPaSmear.actual_division_Pa_linearIndependent observation nontrivial half depth).comp
    (fun i : Fin (n+1) => start+i.val+clock)
    (fun i j same => Fin.ext (by
      change start+i.val+clock = start+j.val+clock at same
      omega))

theorem physical_ranks {start n : Nat} (event : Event start n) :
    LinearIndependent ℂ (fun actor => (physicalPair observation nontrivial half depth event actor).1) ∧
    LinearIndependent ℂ (fun actor => (physicalPair observation nontrivial half depth event actor).2) := by
  let clock := clockAt start n (pivotAt start n)
  have before : (fun actor => (physicalPair observation nontrivial half depth event actor).1) =
      fun actor => pa (start+actor.val+clock) :=
    funext (fun actor => congrArg Prod.fst (physical_pair_actual observation nontrivial half depth event actor))
  have after : (fun actor => (physicalPair observation nontrivial half depth event actor).2) =
      fun actor => pa (start+actor.val+(clock+1)) := by
    funext actor
    simpa only [Nat.add_assoc] using congrArg Prod.snd
      (physical_pair_actual observation nontrivial half depth event actor)
  rw [before, after]
  exact ⟨actual_rank observation nontrivial half depth start n clock,
    actual_rank observation nontrivial half depth start n (clock+1)⟩

private abbrev retained {n : Nat} (row : Fin (n+1) → BurnolPaAmbientCarrier) :
    Fin n → BurnolPaAmbientCarrier := row ∘ Fin.castSucc

private theorem physical_novel {n : Nat} {row : Fin (n+1) → BurnolPaAmbientCarrier}
    (rank : LinearIndependent ℂ row) : row (Fin.last n) ∉ Fit.sourceSpan (retained row) := by
  rintro ⟨coeff, same⟩
  let probe : Fin (n+1) → ℂ :=
    Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => coeff j) (-1)
  have cancelled : ∑ j, probe j • row j = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [probe, Fin.snoc_castSucc, Fin.snoc_last, neg_one_smul]
    change Fit.synthesis (retained row) coeff + -(row (Fin.last n)) = 0
    rw [same, add_neg_cancel]
  have erased := (Fintype.linearIndependent_iff.mp rank) probe cancelled (Fin.last n)
  change Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => coeff j) (-1) (Fin.last n) = 0 at erased
  rw [Fin.snoc_last] at erased
  exact (by norm_num : (-1 : ℂ) ≠ 0) erased

private theorem retained_faithful {n : Nat} {row : Fin (n+1) → BurnolPaAmbientCarrier}
    (rank : LinearIndependent ℂ row) : Function.Injective (Fit.synthesis (retained row)) := by
  have distinct : Function.Injective (Fin.castSucc : Fin n → Fin (n+1)) := by
    intro i j same
    exact Fin.ext (congrArg (fun slot : Fin (n+1) => slot.val) same)
  have old : LinearIndependent ℂ (retained row) := rank.comp Fin.castSucc distinct
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro coeff erased
  have vanish := (Fintype.linearIndependent_iff.mp old) (fun j => coeff j) erased
  change coeff = 0
  ext j
  exact vanish j

/-- The original infinite Pa projection generates its own orthogonal innovation from the paid row. -/
def physicalInnovation {start n : Nat} (event : Event start n) : BurnolPaAmbientCarrier :=
  let row := fun actor => (physicalPair observation nontrivial half depth event actor).1
  Fit.innovationCLM (retained row) (row (Fin.last n))

theorem physical_innovation_mem {start n : Nat} (event : Event start n) :
    physicalInnovation observation nontrivial half depth event ∈ burnolCompactCoPoissonClosedRange := by
  let row := fun actor => (physicalPair observation nontrivial half depth event actor).1
  let actualPaSpace := burnolCompactCoPoissonClosedRange.toSubmodule
  have row_mem (actor : Fin (n+1)) : row actor ∈ actualPaSpace := by
    let ordinal := start+actor.val+clockAt start n (pivotAt start n)
    have paid : row actor = pa ordinal :=
      congrArg Prod.fst (physical_pair_actual observation nontrivial half depth event actor)
    rw [paid]
    exact OriginalKCombCofinalPaAction.actualPa_mem observation nontrivial half depth ordinal
  have oldSpan : Fit.sourceSpan (retained row) ≤ actualPaSpace := by
    rintro _ ⟨coeff,rfl⟩
    change (∑ j : Fin n, coeff j • row j.castSucc) ∈ actualPaSpace
    exact actualPaSpace.sum_mem (fun j _ => actualPaSpace.smul_mem (coeff j) (row_mem j.castSucc))
  change Fit.innovationCLM (retained row) (row (Fin.last n)) ∈ actualPaSpace
  rw [Fit.innovation_value]
  exact actualPaSpace.sub_mem (row_mem _) (oldSpan (Fit.predictable_mem _ _))

/-- The fixed zero's original K annihilates the generated Pa innovation. -/
theorem fixed_zero_probe_silent {start n : Nat} (event : Event start n) :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
      (physicalInnovation observation nontrivial half depth event : BurnolL2) = 0 := by
  have silent := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  exact inner_eq_zero_symm.mp (silent _ (physical_innovation_mem observation nontrivial half depth event))

theorem physical_innovation_visible {start n : Nat} (event : Event start n) :
    let error := physicalInnovation observation nontrivial half depth event
    0 < (inner ℂ error error).re ∧
      ∃ test : Probe, test.1 ≠ c ∧
        inner ℂ (burnolCompletedMellinRieszVector test.1 : BurnolL2) (error : BurnolL2) ≠ 0 := by
  let row := fun actor => (physicalPair observation nontrivial half depth event actor).1
  let error := physicalInnovation observation nontrivial half depth event
  have nonzero : error ≠ 0 :=
    Fit.innovation_ne_zero_of_new_column (retained row)
      (physical_novel (physical_ranks observation nontrivial half depth event).1)
  refine ⟨(re_inner_self_pos (𝕜 := ℂ)).mpr nonzero, ?_⟩
  by_contra invisible
  have zero : (error : BurnolL2) = 0 := original_K_separates error (fun test => by
    by_contra live
    have distinct : test.1 ≠ c := by
      intro same
      apply live
      rw [same]
      exact fixed_zero_probe_silent observation nontrivial half depth event
    exact invisible ⟨test,distinct,live⟩)
  exact nonzero (Subtype.ext zero)

def physicalMixture {n : Nat} (row : Fin (n+1) → BurnolPaAmbientCarrier)
    (a : Record.Values n) (b : ℂ) : BurnolPaAmbientCarrier :=
  Fit.synthesis (retained row) a + b • row (Fin.last n)

def physicalDecode {n : Nat} (row : Fin (n+1) → BurnolPaAmbientCarrier)
    (value : BurnolPaAmbientCarrier) : Record.Values n × ℂ :=
  let born := row (Fin.last n)
  let recovered := Fit.insertedCoefficient (retained row) born value
  (Fit.coefficients (retained row) (value-recovered • born), recovered)

private theorem physical_decode_exact {n : Nat} {row : Fin (n+1) → BurnolPaAmbientCarrier}
    (rank : LinearIndependent ℂ row) (a : Record.Values n) (b : ℂ) :
    physicalDecode row (physicalMixture row a b) = (a,b) := by
  have paid := Fit.insertion_read (retained row) (row (Fin.last n)) (physical_novel rank)
    (retained_faithful rank) a b
  exact Prod.ext paid.2 paid.1

/-- The same emitted pair of physical rows independently recovers both actor mixtures. -/
theorem physical_readback {start n : Nat} (event : Event start n) (a : Record.Values n) (b : ℂ) :
    let before := fun actor => (physicalPair observation nontrivial half depth event actor).1
    let after := fun actor => (physicalPair observation nontrivial half depth event actor).2
    physicalDecode before (physicalMixture before a b) = (a,b) ∧
      physicalDecode after (physicalMixture after a b) = (a,b) :=
  let rank := physical_ranks observation nontrivial half depth event
  ⟨physical_decode_exact rank.1 a b,physical_decode_exact rank.2 a b⟩

/-- The physical inverse on the emitted row writes the installed graph and relation successor. -/
theorem physical_writeback {start ordinal : Nat} (previous : Stored start (ordinal+1))
    (a : Record.Values (ordinal+1)) (b : ℂ) :
    let event := (advance previous).1
    let before := fun actor => (physicalPair observation nontrivial half depth event actor).1
    let after := fun actor => (physicalPair observation nontrivial half depth event actor).2
    let old := physicalDecode before (physicalMixture before a b)
    let new := physicalDecode after (physicalMixture after a b)
    let current := rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal old.1,old.2)
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal new.1,new.2)
    (advanceWide c observation.mathlibZero current.1, advanceStock c (modelInventory observation nontrivial half current.2)) =
      (next.1,modelInventory observation nontrivial half next.2) := by
  have recovered := physical_readback observation nontrivial half depth (advance previous).1 a b
  dsimp only at recovered ⊢
  rw [recovered.1,recovered.2]
  have native := actual_born_price_writeback observation nontrivial half depth start ordinal (toRange ordinal a) b
  have paid := native.2
  rw [native.1] at paid
  exact paid

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.EmittedPaInnovation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
