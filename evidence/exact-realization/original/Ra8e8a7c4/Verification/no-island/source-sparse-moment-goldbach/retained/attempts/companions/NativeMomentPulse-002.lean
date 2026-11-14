import SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.SparseMoment
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.ActionMatrix

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentPulse

open SourceOperationEffects SourceOperationRuntime
open SourceGeneratedFiniteGram
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.FirstCompletion
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.ActionMatrix
open private pointRemaining prefix_remaining from SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.FirstCompletion
open private hold_word from SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.ActionMatrix

private def inventory (depth : Nat) : Finset (Option (Registered.Point depth)) :=
  open Classical in Finset.univ.image (actorTable depth).get

private abbrev Site (depth : Nat) := ↥(inventory depth)

private def actor (depth : Nat) : Site depth ↪ Option (Registered.Point depth) :=
  ⟨Subtype.val,Subtype.val_injective⟩

private theorem actual_in_inventory (depth : Nat) (i : Fin (budget depth+2)) :
    (actorTable depth).get i ∈ inventory depth := by
  classical
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩

private theorem represented (depth : Nat) (site : Site depth) :
    ∃ i : Fin (length depth+1), prefixPoint depth i = actor depth site := by
  classical
  have present := site.property
  unfold inventory at present
  obtain ⟨j,_,read⟩ := Finset.mem_image.mp present
  by_cases within : j ≤ firstComplete depth
  · let i : Fin (length depth+1) := ⟨j.val,Nat.lt_succ_of_le within⟩
    exact ⟨i,(congrArg (actorTable depth).get (Fin.ext rfl : i.castLE _ = j)).trans read⟩
  · refine ⟨Fin.last (length depth),?_⟩
    change (actorTable depth).get ((Fin.last (length depth)).castLE _) = site.val
    have address : (Fin.last (length depth)).castLE (Nat.succ_le_of_lt (firstComplete depth).isLt) =
        firstComplete depth := Fin.ext rfl
    rw [address, ← completed_suffix depth j (le_of_not_ge within)]
    exact read

/-- Read the actual remaining budget of each distinct point in the complete stored inventory. -/
def clock (depth : Nat) (site : Site depth) : ℚ :=
  (pointRemaining depth (actor depth site) : ℚ)

private theorem clock_injective (depth : Nat) : Function.Injective (clock depth) := by
  intro left right same
  obtain ⟨i,leftRead⟩ := represented depth left
  obtain ⟨j,rightRead⟩ := represented depth right
  have remaining : pointRemaining depth (actor depth left) = pointRemaining depth (actor depth right) :=
    Nat.cast_injective (R := ℚ) same
  have slots : i = j := (prefix_remaining depth).injective (by rw [leftRead,rightRead,remaining])
  exact (actor depth).injective (leftRead.symm.trans (slots ▸ rightRead))

private def restrict (depth : Nat) : Material depth →+ (Site depth →₀ ℚ) :=
  (Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ)).comp
    (Finsupp.lcomapDomain (R := ℤ) (actor depth) (actor depth).injective).toAddMonoidHom

private theorem restrict_single (depth : Nat) (i : Site depth) (a : ℤ) :
    restrict depth (Finsupp.single (actor depth i) a) = Finsupp.single i (a : ℚ) := by
  change Finsupp.mapRange (Int.castAddHom ℚ) _
    (Finsupp.comapDomain (actor depth) (Finsupp.single (actor depth i) a) _) = _
  rw [Finsupp.comapDomain_single,Finsupp.mapRange_single]
  rfl

private def restore (depth : Nat) (row : Site depth →₀ ℚ) : Material depth :=
  Finsupp.embDomain (actor depth) (Finsupp.mapRange Rat.num (by decide) row)

private theorem restore_restricted (depth : Nat) (word : Material depth)
    (supported : ↑word.support ⊆ Set.range (actor depth)) :
    restore depth (restrict depth word) = word := by
  have scalars :
      Finsupp.mapRange Rat.num (by decide) (restrict depth word) =
        Finsupp.comapDomain (actor depth) word (actor depth).injective.injOn := by
    ext i
    let coefficient := Finsupp.comapDomain (actor depth) word (actor depth).injective.injOn i
    change ((coefficient : ℚ).num) = coefficient
    exact Rat.num_intCast coefficient
  exact (congrArg (Finsupp.embDomain (actor depth)) scalars).trans
    (Finsupp.embDomain_comapDomain supported)

private def effect (depth : Nat) (i : Fin (budget depth+1)) : Material depth :=
  let states := (fullHistory depth).storedPairAt i
  readMaterial depth states.2 - readMaterial depth states.1

private theorem effect_held (depth : Nat) (i : Fin (budget depth+1))
    (after : firstComplete depth ≤ i.castSucc) : effect depth i = 0 := by
  have same := congrArg (fun pair : Material depth × Material depth => pair.2-pair.1) (actor_material_adjacent depth i)
  have word := TimelineBasis.word_succ (R := ℤ) (actorTable depth).get i
  exact same.symm.trans (word.symm.trans (hold_word depth i after))

private theorem support_pair {A R : Type*} [AddCommGroup R] [DecidableEq A] (x y : A) (a b : R) :
    (Finsupp.single x a - Finsupp.single y b).support ⊆ ({x} ∪ {y} : Finset A) := by
  rw [sub_eq_add_neg]
  exact Finsupp.support_add.trans
    (Finset.union_subset_union Finsupp.support_single_subset
      (by simpa only [Finsupp.support_neg] using
        (Finsupp.support_single_subset (a := y) (b := b))))

private theorem effect_support (depth : Nat) (i : Fin (budget depth+1)) :
    (↑(effect depth i).support : Set (Option (Registered.Point depth))) ⊆ Set.range (actor depth) ∧
      (restrict depth (effect depth i)).support.card ≤ 2 := by
  classical
  let old : Site depth := ⟨(actorTable depth).get i.castSucc,actual_in_inventory depth i.castSucc⟩
  let new : Site depth := ⟨(actorTable depth).get i.succ,actual_in_inventory depth i.succ⟩
  have same : effect depth i =
      Finsupp.single (actor depth new) 1 - Finsupp.single (actor depth old) 1 :=
    (congrArg (fun pair : Material depth × Material depth => pair.2-pair.1)
      (actor_material_adjacent depth i)).symm
  rw [same]
  refine ⟨?_,?_⟩
  · intro point active
    rcases Finset.mem_union.mp (support_pair _ _ _ _ active) with h | h
    · exact ⟨new,(Finset.mem_singleton.mp h).symm⟩
    · exact ⟨old,(Finset.mem_singleton.mp h).symm⟩
  · rw [map_sub,restrict_single,restrict_single]
    exact (Finset.card_le_card (support_pair new old _ _)).trans
      (by simpa only [Finset.card_singleton] using
        (Finset.card_union_le ({new} : Finset (Site depth)) ({old} : Finset (Site depth))))

/-- These four measurements are generated by the actual adjacent integer effect. -/
def effectRows (depth : Nat) (i : Fin (budget depth+1)) : Fin 4 → ℚ :=
  SparseMoment.measure (clock depth) (restrict depth (effect depth i)) 2

def decode (depth : Nat) (data : Fin 4 → ℚ) : Material depth :=
  restore depth (SparseMoment.recover (bound := 2) (clock depth) Finset.univ data)

theorem decoded_effect (depth : Nat) (i : Fin (budget depth+1)) :
    decode depth (effectRows depth i) = effect depth i := by
  have support := effect_support depth i
  unfold decode effectRows
  rw [SparseMoment.recover_prefix (clock depth) (clock_injective depth) Finset.univ
    (restrict depth (effect depth i)) (Finset.subset_univ _) support.2]
  exact restore_restricted depth _ support.1

/-- The decoded word supplies the original increment environment and its stored activation. -/
theorem actual_increment (depth : Nat) (i : Fin (budget depth+1)) :
    environment depth (decode depth (effectRows depth i)) =
      storedIncrementEnvironment (readMaterial depth) (environment depth) (fullHistory depth) i ∧
    type_of% (stored_whole_and_next depth i) := by
  rw [decoded_effect]
  exact ⟨rfl,stored_whole_and_next depth i⟩

/-- A held pulse decodes to the zero actual effect. -/
theorem held_decodes_zero (depth : Nat) (i : Fin (budget depth+1))
    (after : firstComplete depth ≤ i.castSucc) :
    decode depth (effectRows depth i) = 0 :=
  (decoded_effect depth i).trans (effect_held depth i after)

/-- The independent completion consumer receives the decoded material of the same full actor. -/
def terminalRows (depth : Nat) : Fin 4 → ℚ :=
  SparseMoment.measure (clock depth) (restrict depth (storedFinal depth)) 2

theorem actual_terminal (depth : Nat) :
    decode depth (terminalRows depth) = storedFinal depth ∧
      type_of% (stored_consumes_original_disposition depth) := by
  let endSlot := Fin.last (budget depth+1)
  let j : Site depth := ⟨(actorTable depth).get endSlot,actual_in_inventory depth endSlot⟩
  let last := Fin.last (budget depth)
  have address : last.succ = endSlot := Fin.ext rfl
  have final : storedFinal depth = Finsupp.single (actor depth j) 1 := by
    have actual := congrArg Prod.snd (actor_material_adjacent depth last)
    change Finsupp.single ((actorTable depth).get last.succ) 1 = storedFinal depth at actual
    rw [address] at actual
    exact actual.symm
  have covered : (↑(storedFinal depth).support : Set (Option (Registered.Point depth))) ⊆ Set.range (actor depth) := by
    intro point present
    have only : point ∈ ({actor depth j} : Finset _) :=
      Finsupp.support_single_subset (final ▸ present)
    exact ⟨j,(Finset.mem_singleton.mp only).symm⟩
  have within : (restrict depth (storedFinal depth)).support.card ≤ 2 := by
    rw [final,restrict_single]
    change (Finsupp.single j (1 : ℚ)).support.card ≤ 2
    rw [Finsupp.support_single _ one_ne_zero,Finset.card_singleton]
    omega
  have recovered : decode depth (terminalRows depth) = storedFinal depth := by
    unfold decode terminalRows
    rw [SparseMoment.recover_prefix (clock depth) (clock_injective depth) Finset.univ
      (restrict depth (storedFinal depth)) (Finset.subset_univ _) within]
    exact restore_restricted depth _ covered
  exact ⟨recovered,stored_consumes_original_disposition depth⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentPulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
