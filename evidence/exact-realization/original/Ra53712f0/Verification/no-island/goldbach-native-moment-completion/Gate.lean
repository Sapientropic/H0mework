import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.NativeMomentCompletion

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentCompletionCertificate

open SourceOperationRuntime SourceOperationEffects SourceOperationScalarRelations SourceGeneratedFiniteGram
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.FirstCompletion
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentPulse (effectRows decode decoded_effect)
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentCompletion
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActuality
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirect
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open scoped BigOperators
open private rank_zero live_effect readAt receiptIndex from
  SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.NativeMomentCompletion
open private effect effect_held from
  SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.NativeMomentPulse

private theorem the_four_moment_stop_is_the_first_rank_zero_or_the_literal_last
    {steps : Nat} (rows : Fin steps → Fin 4 → ℚ) :
    (∀ i, SparseMoment.order (bound := 2) (rows i) = 0 →
      (∀ j < i, SparseMoment.order (bound := 2) (rows j) ≠ 0) →
      stopIndex rows = i.castSucc) ∧
    ((∀ i, SparseMoment.order (bound := 2) (rows i) ≠ 0) → stopIndex rows = Fin.last steps) := by
  constructor
  · intro i quiet before
    have found : Fin.find? (fun j => decide (SparseMoment.order (bound := 2) (rows j) = 0)) = some i :=
      Fin.find?_eq_some_iff.mpr ⟨decide_eq_true quiet,fun j earlier => decide_eq_false (before j earlier)⟩
    unfold stopIndex
    rw [found]
  · intro allLive
    have absent : Fin.find? (fun i => decide (SparseMoment.order (bound := 2) (rows i) = 0)) = none :=
      Fin.find?_eq_none_iff.mpr (fun i => decide_eq_false (allLive i))
    unfold stopIndex
    rw [absent]

#eval IO.println "CP616_CONTROL + the_four_moment_stop_is_the_first_rank_zero_or_the_literal_last"

private theorem actual_rank_zero_reads_the_original_effect_and_the_actual_stop_follows_bind
    (depth : Nat) (i : Fin (budget depth+1)) :
    (SparseMoment.order (bound := 2) (effectRows depth i) = 0 ↔ effect depth i = 0) ∧
    (firstComplete depth ≤ i.castSucc → SparseMoment.order (bound := 2) (effectRows depth i) = 0) ∧
    actualStop depth = firstComplete depth ∧ 2 ≤ (actualStop depth).val := by
  have measured := actual_stop depth
  have afterBind : 2 ≤ (actualStop depth).val := (congrArg (fun j : Fin (budget depth+2) => 2 ≤ j.val) measured).mpr (first_after_bind depth)
  exact ⟨rank_zero depth i,fun after => (rank_zero depth i).mpr (effect_held depth i after),measured,afterBind⟩

#eval IO.println "CP616_CONTROL + actual_rank_zero_reads_the_original_effect_and_the_actual_stop_follows_bind"

private theorem the_measured_prefix_sums_the_actual_decoded_integer_increments (depth : Nat) :
    terminalMaterial depth = readMaterial depth (mathSeed depth).state +
      (∑ step ∈ Finset.range (actualStop depth).val, readAt depth step) ∧
    terminalMaterial depth = storedFinal depth ∧
    ∀ step ∈ Finset.range (actualStop depth).val,
      ∃ live : step < budget depth+1,
        let i : Fin (budget depth+1) := ⟨step,live⟩
        let pair := (fullHistory depth).storedPairAt i
        readAt depth step = decode depth (effectRows depth i) ∧
        decode depth (effectRows depth i) = readMaterial depth pair.2-readMaterial depth pair.1 := by
  refine ⟨rfl,actual_terminal depth,?_⟩
  intro step paid
  have live : step < budget depth+1 :=
    (Finset.mem_range.mp paid).trans_le (Nat.le_of_lt_succ (actualStop depth).isLt)
  let i : Fin (budget depth+1) := ⟨step,live⟩
  have read : readAt depth step = decode depth (effectRows depth i) := by
    unfold readAt
    rw [dif_pos live]
  have diff : decode depth (effectRows depth i) = readMaterial depth ((fullHistory depth).storedPairAt i).2 -
      readMaterial depth ((fullHistory depth).storedPairAt i).1 := decoded_effect depth i
  exact ⟨live,read,diff⟩

#eval IO.println "CP616_CONTROL + the_measured_prefix_sums_the_actual_decoded_integer_increments"

private def OriginalDisposition (depth : Nat) (terminal : Material depth) : Prop :=
  (∃ reached : ReachedAt (Registered.actor depth).rooted.rootSource.source,
    terminal = Finsupp.single
      (some (⟨(Registered.runtime depth).emittedOccurrence,.completed (.inl reached)⟩ : Registered.Point depth)) 1 ∧
    ∃ generated : PrimePairActualitySettlementAt (directRuntimeActuality depth),
      generatePrimePairActualityDisposition (directRuntimeActuality depth) = .settlement generated) ∨
  (∃ exhausted : ExhaustedAt (Registered.actor depth).rooted.rootSource.source,
    terminal = Finsupp.single
      (some (⟨(Registered.runtime depth).emittedOccurrence,.completed (.inr exhausted)⟩ : Registered.Point depth)) 1 ∧
    ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
      generatePrimePairActualityDisposition (directRuntimeActuality depth) = .obstruction generated)

private theorem the_measured_predecessor_consumes_the_same_receipt_whole_next_and_disposition (depth : Nat) :
    (receiptIndex depth).succ = actualStop depth ∧
    type_of% (terminal_consumer depth) ∧
    OriginalDisposition depth (terminalMaterial depth) ∧
    type_of% (Registered.receipt depth) := by
  have selected : (receiptIndex depth).succ = actualStop depth :=
    (congrArg (fun i : Fin (budget depth+1) => i.succ) (actual_receipt_index depth)).trans
      ((terminal_successor depth).trans (actual_stop depth).symm)
  have final : OriginalDisposition depth (storedFinal depth) := stored_consumes_original_disposition depth
  have original := (congrArg (OriginalDisposition depth) (actual_terminal depth).symm).mp final
  exact ⟨selected,terminal_consumer depth,original,Registered.receipt depth⟩

#eval IO.println "CP616_CONTROL + the_measured_predecessor_consumes_the_same_receipt_whole_next_and_disposition"

private theorem a_live_original_pulse_before_completion_cannot_pay_a_stop
    (depth : Nat) (i : Fin (budget depth+1)) (before : i.castSucc < firstComplete depth) :
    ¬ (SparseMoment.order (bound := 2) (effectRows depth i) = 0 ∨ actualStop depth = i.castSucc) := by
  rintro (quiet | early)
  · exact live_effect depth i before ((rank_zero depth i).mp quiet)
  · exact (ne_of_lt before) (early.symm.trans (actual_stop depth))

#eval IO.println "CP616_CONTROL - a_live_original_pulse_before_completion_cannot_pay_a_stop"
#eval IO.println "CP616_GATE_PASS positive=4 negative=1"

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentCompletionCertificate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
