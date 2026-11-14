import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.NativeMomentPulse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentCompletion

open SourceOperationRuntime SourceGeneratedFiniteGram
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Registered
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.FirstCompletion
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentPulse
open scoped BigOperators
open private clock_injective restrict restore restore_restricted effect effect_held effect_support from SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.NativeMomentPulse

private abbrev Steps (depth : Nat) := budget depth+1

private theorem rank_zero (depth : Nat) (i : Fin (Steps depth)) :
    SparseMoment.order (effectRows depth i) = 0 ↔ effect depth i = 0 := by
  have support := effect_support depth i
  have rank : SparseMoment.order (effectRows depth i) = (restrict depth (effect depth i)).support.card :=
    SparseMoment.order_from_source (clock depth) (clock_injective depth) _ support.2
  rw [rank]
  constructor
  · intro zero
    have erased : restrict depth (effect depth i) = 0 :=
      Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp zero)
    have exactWord := restore_restricted depth (effect depth i) support.1
    rw [erased] at exactWord
    exact exactWord.symm
  · intro zero
    rw [zero,map_zero,Finsupp.support_zero,Finset.card_empty]

private theorem live_effect (depth : Nat) (i : Fin (Steps depth)) (before : i.castSucc < firstComplete depth) :
    effect depth i ≠ 0 := by
  classical
  let j : Fin (firstComplete depth).val := ⟨i.val,before⟩
  let new := prefixPoint depth j.succ
  let old := prefixPoint depth j.castSucc
  have different : new ≠ old := fun same =>
    Nat.succ_ne_self i.val (congrArg Fin.val (prefix_point_injective depth same))
  have read : effect depth i = Finsupp.single new 1 - Finsupp.single old 1 :=
    (congrArg (fun pair : Material depth × Material depth => pair.2-pair.1)
      (actor_material_adjacent depth i)).symm
  intro vanished
  have coeff := congrArg (fun word : Material depth => word new) (read.symm.trans vanished)
  simp only [Finsupp.sub_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne different,
    sub_zero,Finsupp.zero_apply] at coeff
  exact one_ne_zero coeff

/-- Stop at the first zero-rank measured effect, or at the end of the measured tape. -/
def stopIndex {steps : Nat} (rows : Fin steps → Fin 4 → ℚ) : Fin (steps+1) :=
  match Fin.find? (fun i => decide (SparseMoment.order (rows i) = 0)) with
  | some i => i.castSucc
  | none => Fin.last steps

def actualStop (depth : Nat) : Fin (Steps depth+1) := stopIndex (effectRows depth)

theorem actual_stop (depth : Nat) : actualStop depth = firstComplete depth := by
  let finish := firstComplete depth
  change stopIndex (effectRows depth) = finish
  have nonzero (i : Fin (Steps depth)) (before : i.castSucc < finish) :
      SparseMoment.order (effectRows depth i) ≠ 0 :=
    fun quiet => live_effect depth i before ((rank_zero depth i).mp quiet)
  by_cases last : finish.val = Steps depth
  · have none : Fin.find? (fun i => decide (SparseMoment.order (effectRows depth i) = 0)) = none := by
      apply Fin.find?_eq_none_iff.mpr
      intro i
      have live : i.castSucc < finish := by change i.val < finish.val; rw [last]; exact i.isLt
      exact decide_eq_false (nonzero i live)
    unfold stopIndex
    rw [none]
    exact Fin.ext last.symm
  · have before : finish.val < Steps depth := lt_of_le_of_ne (Nat.le_of_lt_succ finish.isLt) last
    let i : Fin (Steps depth) := ⟨finish.val,before⟩
    have atStop : i.castSucc = finish := Fin.ext rfl
    have found : Fin.find? (fun i => decide (SparseMoment.order (effectRows depth i) = 0)) = some i := by
      apply Fin.find?_eq_some_iff.mpr
      exact ⟨decide_eq_true ((rank_zero depth i).mpr (effect_held depth i atStop.ge)),
        fun j earlier => decide_eq_false (nonzero j earlier)⟩
    unfold stopIndex
    rw [found]
    exact atStop

private def materialAt (depth step : Nat) : Material depth :=
  if live : step < budget depth+2 then
    Finsupp.single ((actorTable depth).get ⟨step,live⟩) 1
  else 0

private def readAt (depth step : Nat) : Material depth :=
  if live : step < Steps depth then decode depth (effectRows depth ⟨step,live⟩) else 0

private theorem material_start (depth : Nat) :
    materialAt depth 0 = readMaterial depth (mathSeed depth).state := by
  unfold materialAt
  rw [dif_pos (by omega)]
  exact (congrArg (fun point => Finsupp.single point (1 : ℤ)) (actor_table_root depth)).trans
    (seed_material depth).symm

private theorem read_as_diff (depth step : Nat) (live : step < Steps depth) :
    readAt depth step = materialAt depth (step+1) - materialAt depth step := by
  unfold readAt materialAt
  rw [dif_pos live,dif_pos (by omega),dif_pos (by omega),decoded_effect]
  exact (congrArg (fun pair : Material depth × Material depth => pair.2-pair.1)
    (actor_material_adjacent depth ⟨step,live⟩)).symm

/-- Accumulate the decoded live effects from the literal seed up to the measured terminal. -/
def terminalMaterial (depth : Nat) : Material depth :=
  readMaterial depth (mathSeed depth).state +
    ∑ i ∈ Finset.range (actualStop depth).val, readAt depth i

theorem actual_terminal (depth : Nat) : terminalMaterial depth = storedFinal depth := by
  let stop := actualStop depth
  have delta : (∑ i ∈ Finset.range stop.val, readAt depth i) =
      ∑ i ∈ Finset.range stop.val, (materialAt depth (i+1) - materialAt depth i) := by
    apply Finset.sum_congr rfl
    intro i within
    exact read_as_diff depth i ((Finset.mem_range.mp within).trans_le (Nat.le_of_lt_succ stop.isLt))
  change readMaterial depth (mathSeed depth).state + (∑ i ∈ Finset.range stop.val, readAt depth i) = _
  rw [delta,Finset.sum_range_sub,← material_start,add_sub_cancel]
  have address := actual_stop depth
  change stop = firstComplete depth at address
  have word : materialAt depth stop.val = Finsupp.single ((actorTable depth).get stop) 1 := by
    unfold materialAt
    rw [dif_pos stop.isLt]
  rw [word,address]
  exact first_material_terminal depth

private def receiptIndex (depth : Nat) : Fin (Steps depth) :=
  ⟨(actualStop depth).val-1,by
    have within := (actualStop depth).isLt
    have positive := first_after_bind depth
    rw [actual_stop depth] at within ⊢
    omega⟩

theorem actual_receipt_index (depth : Nat) : receiptIndex depth = terminalTransition depth :=
  Fin.ext (congrArg (fun point : Fin (Steps depth+1) => point.val-1) (actual_stop depth))

/-- The measured address reads the original activation receipt and independent disposition. -/
theorem terminal_consumer (depth : Nat) :
    terminalMaterial depth = storedFinal depth ∧
      HEq ((fullHistory depth).storedActivation (receiptIndex depth))
        ((mathSeed depth).advance (terminalTransition depth).val).tick ∧
      ((fullHistory depth).storedActivation (receiptIndex depth)).nextCurrent =
        (OF.process (old depth) (origin depth) (reader depth)).stateAt
          ((fullHistory depth).storedPairAt (terminalTransition depth)).2 ∧
      type_of% (stored_consumes_original_disposition depth) := by
  rw [actual_receipt_index]
  exact ⟨actual_terminal depth,(stored_whole_and_next depth (terminalTransition depth)).1,
    (stored_whole_and_next depth (terminalTransition depth)).2,stored_consumes_original_disposition depth⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
