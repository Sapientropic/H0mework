import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Replay

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend

open Institutions.Capitalism.Universal
open Source.Program Instances.OpenReplication Root

private theorem unit_valid (n : Nat) (fuel : ℚ) (shared : Bool) (enough : 1 ≤ fuel) :
    (law n).Valid (state fuel 0 0 shared) maintain := by
  simpa [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    NonnegativeBundle, flowAt, amount, locate, law, state, maintain] using enough

private theorem unit_step (n : Nat) (fuel : ℚ) (shared : Bool) (enough : 1 ≤ fuel) :
    (law n).step (state fuel 0 0 shared) maintain = state (fuel - 1) 0 0 shared := by
  rw [RawLaw.step, if_pos (unit_valid n fuel shared enough)]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;>
      simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, maintain,
        state, flowAt, amount, locate]
  all_goals rfl

/-- Every additional payment is individually legal and leaves the reserve
floor intact, including the last intermediate cut. -/
theorem unit_run (n count index : Nat) (fuel : ℚ) (shared : Bool)
    (enough : (count : ℚ) + 1 ≤ fuel) :
    ((law n).execute (state fuel 0 0 shared) index (List.replicate count maintain)).final =
        state (fuel - count) 0 0 shared ∧
      ∀ item ∈ ((law n).execute (state fuel 0 0 shared) index (List.replicate count maintain)).items,
        (law n).Valid item.before item.request ∧
        1 ≤ item.before.stock false false ∧
        1 ≤ ((law n).step item.before item.request).stock false false ∧
        item.request = maintain := by
  induction count generalizing fuel index with
  | zero => simp [RawLaw.execute]
  | succ count ih =>
    have fuelEnough : 1 ≤ fuel := by have h := Nat.cast_nonneg (α := ℚ) count; push_cast at enough; linarith
    have restEnough : (count : ℚ) + 1 ≤ fuel - 1 := by push_cast at enough; linarith
    have rest := ih (index + 1) (fuel - 1) restEnough
    simp only [List.replicate_succ, RawLaw.execute, unit_step n fuel shared fuelEnough]
    constructor
    · rw [rest.1]
      congr 1
      push_cast
      ring
    · intro item member
      simp only [List.mem_cons] at member
      rcases member with front | back
      · subst item
        exact ⟨unit_valid n fuel shared fuelEnough, fuelEnough,
          by rw [unit_step n fuel shared fuelEnough]; exact restEnough.trans' (by have h := Nat.cast_nonneg (α := ℚ) count; linarith), rfl⟩
      · exact rest.2 item back

theorem reinvested_current (n : Nat) (shared : Bool) :
    currentAt n shared 3 = (state 1 0 0 shared).retime 3 3 := by
  rw [← actual_next n shared 2]
  change (law n).next (currentAt n shared 2) (execution n shared 2).submitted = _
  rw [task_current, reinvestment_word]
  simp only [RawLaw.next, (law n).execute_retime (time_independent n)]
  cases shared
  · simp only [Bool.false_eq_true, ↓reduceIte, List.replicate_zero, RawLaw.execute]
    norm_num [RawCurrent.retime, state, law]
  · simp only [↓reduceIte]
    rw [(unit_run n (n + 1) 0 ((n : ℚ) + 2) true (by push_cast; linarith)).1]
    have cancel : (n : ℚ) + 2 - ↑(n + 1) = 1 := by push_cast; ring
    simp only [cancel]
    norm_num [RawCurrent.retime, state, law]

theorem every_reinvestment_cut_is_paid_and_keeps_the_reserve (n : Nat) (shared : Bool) :
    ∀ item ∈ (execution n shared 2).interpreted.items,
      (law n).Valid item.before item.request ∧
      1 ≤ item.before.stock false false ∧
      1 ≤ ((law n).step item.before item.request).stock false false ∧
      item.request = maintain := by
  change ∀ item ∈ ((law n).execute (currentAt n shared 2) 0 (execution n shared 2).submitted).items, _
  rw [task_current, reinvestment_word]
  cases shared
  · simp [RawLaw.execute]
  · intro item member
    rw [Replay.items] at member
    obtain ⟨original, inside, same⟩ := List.mem_map.mp member
    subst item
    have facts := (unit_run n (n + 1) 0 ((n : ℚ) + 2) true (by push_cast; linarith)).2 original inside
    refine ⟨((law n).valid_retime (time_independent n) _ _ _ _).mpr facts.1,
      facts.2.1, ?_, facts.2.2.2⟩
    change 1 ≤ ((law n).step (original.before.retime 2 2) original.request).stock false false
    rw [(law n).step_retime (time_independent n)]
    exact facts.2.2.1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend
