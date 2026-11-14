import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.NativeMomentPulse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SparseMomentCertificate

open SourceGeneratedFiniteGram
open scoped BigOperators
open private support_hankel_nonzero from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.SparseMoment

private def rationalClock (i : Nat) : ℚ := (i : ℚ)

private theorem rationalClock_injective : Function.Injective rationalClock :=
  Nat.cast_injective (R := ℚ)

private def balanced : Nat →₀ ℚ := Finsupp.single 2 1 - Finsupp.single 9 1

private theorem balanced_support : balanced.support = ({2,9} : Finset Nat) := by
  ext site
  rw [Finsupp.mem_support_iff]
  by_cases atFirst : site = 2
  · subst site
    norm_num [balanced,Finsupp.sub_apply,Finsupp.single_apply]
  by_cases atSecond : site = 9
  · subst site
    norm_num [balanced,Finsupp.sub_apply,Finsupp.single_apply]
  · simp only [balanced,Finsupp.sub_apply,Finsupp.single_eq_of_ne atFirst,
      Finsupp.single_eq_of_ne atSecond,sub_self,ne_self_iff_false,
      Finset.mem_insert,Finset.mem_singleton,atFirst,atSecond,or_self]

private theorem balanced_card : balanced.support.card = 2 := by
  rw [balanced_support]
  decide

private theorem balanced_bound : balanced.support.card ≤ 2 := balanced_card.le

set_option cleanup.letToHave false in
private theorem signed_zero_mass_still_has_two_live_hankel_columns :
    let data := SparseMoment.measure rationalClock balanced 2
    SparseMoment.moments rationalClock balanced 0 = 0 ∧
    SparseMoment.order (bound := 2) data = 2 ∧
    (SparseMoment.hankel (SparseMoment.moments rationalClock balanced) 2).det ≠ 0 := by
  have mass : SparseMoment.moments rationalClock balanced 0 = 0 := by
    rw [SparseMoment.moments,Finsupp.sum,balanced_support]
    norm_num [balanced,Finsupp.sub_apply,Finsupp.single_apply,Finset.sum_insert]
  have rank := SparseMoment.order_from_source rationalClock rationalClock_injective balanced balanced_bound
  have live := support_hankel_nonzero rationalClock rationalClock_injective balanced
  rw [balanced_card] at live
  exact ⟨mass,rank.trans balanced_card,live⟩

#eval IO.println "CP614_CONTROL + signed_zero_mass_still_has_two_live_hankel_columns"

private def available : Finset Nat := {2,5,9}

set_option cleanup.letToHave false in
private theorem actual_recurrence_finds_the_two_roots_and_excludes_an_available_extra_site :
    let data := SparseMoment.measure rationalClock balanced 2
    let polynomial := SparseMoment.recurrence (bound := 2) data
    polynomial.eval (rationalClock 2) = 0 ∧ polynomial.eval (rationalClock 9) = 0 ∧
    polynomial.eval (rationalClock 5) ≠ 0 ∧
    SparseMoment.recoverSupport (bound := 2) rationalClock available data = balanced.support ∧
    SparseMoment.recover (bound := 2) rationalClock available data = balanced := by
  classical
  let data := SparseMoment.measure rationalClock balanced 2
  have cover : balanced.support ⊆ available := by
    rw [balanced_support]
    decide
  have first : 2 ∈ balanced.support := by rw [balanced_support]; decide
  have second : 9 ∈ balanced.support := by rw [balanced_support]; decide
  have support := SparseMoment.recover_support rationalClock rationalClock_injective available balanced cover balanced_bound
  have excluded : 5 ∉ SparseMoment.recoverSupport (bound := 2) rationalClock available data := by
    rw [support,balanced_support]
    decide
  have extra : (SparseMoment.recurrence (bound := 2) data).eval (rationalClock 5) ≠ 0 := by
    intro vanishes
    apply excluded
    change 5 ∈ available.filter (fun site => (SparseMoment.recurrence (bound := 2) data).eval (rationalClock site) = 0)
    exact Finset.mem_filter.mpr ⟨by decide,vanishes⟩
  exact ⟨SparseMoment.recurrence_vanishes rationalClock rationalClock_injective balanced balanced_bound first,
    SparseMoment.recurrence_vanishes rationalClock rationalClock_injective balanced balanced_bound second,
    extra,support,SparseMoment.recover_prefix rationalClock rationalClock_injective available balanced cover balanced_bound⟩

#eval IO.println "CP614_CONTROL + actual_recurrence_finds_the_two_roots_and_excludes_an_available_extra_site"

end SparseMomentCertificate

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentPulseCertificate

open SourceOperationRuntime SourceOperationEffects SourceOperationScalarRelations
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.FirstCompletion
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.ActionMatrix
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActuality
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirect
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open private inventory actual_in_inventory effect_held from
  SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.NativeMomentPulse

set_option cleanup.letToHave false in
private theorem actual_pulse_reads_the_complete_actor_and_the_two_stored_adjacent_states
    (depth : Nat) (i : Fin (budget depth+1)) :
    let states := (fullHistory depth).storedPairAt i
    let decoded := NativeMomentPulse.decode depth (NativeMomentPulse.effectRows depth i)
    (∀ j : Fin (budget depth+2), (actorTable depth).get j ∈ inventory depth) ∧
    decoded = readMaterial depth states.2-readMaterial depth states.1 ∧
    environment depth decoded =
      storedIncrementEnvironment (readMaterial depth) (environment depth) (fullHistory depth) i ∧
    type_of% (stored_whole_and_next depth i) := by
  let states := (fullHistory depth).storedPairAt i
  have adjacent : NativeMomentPulse.decode depth (NativeMomentPulse.effectRows depth i) =
      readMaterial depth states.2-readMaterial depth states.1 := NativeMomentPulse.decoded_effect depth i
  have paid := NativeMomentPulse.actual_increment depth i
  exact ⟨actual_in_inventory depth,adjacent,paid.1,paid.2⟩

#eval IO.println "CP614_CONTROL + actual_pulse_reads_the_complete_actor_and_the_two_stored_adjacent_states"

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

set_option cleanup.letToHave false in
private theorem the_same_terminal_moments_supply_original_reached_or_exhausted_and_receipt (depth : Nat) :
    let terminal := NativeMomentPulse.decode depth (NativeMomentPulse.terminalRows depth)
    OriginalDisposition depth terminal ∧ type_of% (Registered.receipt depth) := by
  let terminal := NativeMomentPulse.decode depth (NativeMomentPulse.terminalRows depth)
  have paid := NativeMomentPulse.actual_terminal depth
  have original : OriginalDisposition depth (storedFinal depth) := paid.2
  exact ⟨(congrArg (OriginalDisposition depth) paid.1.symm).mp original,Registered.receipt depth⟩

#eval IO.println "CP614_CONTROL + the_same_terminal_moments_supply_original_reached_or_exhausted_and_receipt"

private theorem an_actual_completed_hold_decodes_zero_increment
    (depth : Nat) (i : Fin (budget depth+1)) (after : firstComplete depth ≤ i.castSucc) :
    (actorTable depth).get i.succ = (actorTable depth).get i.castSucc ∧
    NativeMomentPulse.decode depth (NativeMomentPulse.effectRows depth i) = 0 ∧
    storedIncrementEnvironment (readMaterial depth) (environment depth) (fullHistory depth) i = 0 := by
  have later : i.castSucc ≤ i.succ := Nat.le_succ i.val
  exact ⟨(completed_suffix depth i.succ (after.trans later)).trans
    (completed_suffix depth i.castSucc after).symm,
    NativeMomentPulse.held_decodes_zero depth i after,hold_environment depth i after⟩

#eval IO.println "CP614_CONTROL - an_actual_completed_hold_decodes_zero_increment"
#eval IO.println "CP614_GATE_PASS positive=4 negative=1"

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.NativeMomentPulseCertificate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
