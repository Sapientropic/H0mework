import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Erasure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Coupling

universe u v w x y z

variable {Left : Type u} {Right : Type v} {Input : Type w} {Reply : Type x}
  {Bill : Type y} {Ordinary : Type z}

variable (advanceL : Left → Input → Left × Reply) (advanceR : Right → Input → Right × Reply)
  (paidL : Left → Input → Option Bill) (paidR : Right → Input → Option Bill)
  (ordinaryL : Left → Input → Ordinary) (ordinaryR : Right → Input → Ordinary)
  (openingL : Left) (openingR : Right) (strategy : Nat → List Reply → Input)

local notation "leftRun" => Erasure.run advanceL openingL strategy
local notation "rightRun" => Erasure.run advanceR openingR strategy
local notation "leftPaid" => (fun n => paidL (Prod.fst (leftRun n)) (strategy n (Prod.snd (leftRun n))))
local notation "rightPaid" => (fun n => paidR (Prod.fst (rightRun n)) (strategy n (Prod.snd (rightRun n))))

variable (matched : ∀ n,
    let l := Erasure.run advanceL openingL strategy n
    let r := Erasure.run advanceR openingR strategy n
    l.2 = r.2 →
      let input := strategy n l.2
      ordinaryL l.1 input = ordinaryR r.1 input ∧ paidL l.1 input = paidR r.1 input)
  (quiet : ∀ l r input, ordinaryL l input = ordinaryR r input →
    paidL l input = none → paidR r input = none →
    (advanceL l input).2 = (advanceR r input).2)

include matched quiet

private theorem quiet_cuts (n : Nat) (common : (leftRun n).2 = (rightRun n).2)
    (unpaid : leftPaid n = none) :
    (leftRun (n + 1)).2 = (rightRun (n + 1)).2 ∧ rightPaid n = none := by
  have aligned := matched n common
  have unpaidRight := aligned.2.symm.trans unpaid
  have reply := quiet _ _ _ aligned.1 unpaid unpaidRight
  refine ⟨?_, ?_⟩
  · change (advanceL (leftRun n).1 (strategy n (leftRun n).2)).2 :: (leftRun n).2 =
      (advanceR (rightRun n).1 (strategy n (rightRun n).2)).2 :: (rightRun n).2
    rw [← common, reply]
  · change paidR (rightRun n).1 (strategy n (rightRun n).2) = none
    rw [← common]
    exact unpaidRight

/-- Couple the observed runs from any common transcript. The choices
at each reached cut come from the same adaptive strategy. -/
theorem before_payment (start limit : Nat) (common : (leftRun start).2 = (rightRun start).2)
    (unpaid : ∀ i, start ≤ i → i < limit → leftPaid i = none) :
    (∀ i, start ≤ i → i ≤ limit → (leftRun i).2 = (rightRun i).2) ∧
    (∀ i, start ≤ i → i < limit → rightPaid i = none) := by
  have byDistance : ∀ d, start + d ≤ limit → (leftRun (start + d)).2 = (rightRun (start + d)).2 := by
    intro d
    induction d with
    | zero => exact fun _ => common
    | succ d previous =>
      intro reached
      have step : start + d < limit := reached
      have before := previous (Nat.le_of_lt step)
      exact (quiet_cuts advanceL advanceR paidL paidR ordinaryL ordinaryR openingL openingR
        strategy matched quiet (start + d) before (unpaid _ (Nat.le_add_right start d) step)).1
  have shared : ∀ i, start ≤ i → i ≤ limit → (leftRun i).2 = (rightRun i).2 := by
    intro i afterStart through
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le afterStart
    exact byDistance d through
  refine ⟨shared, fun i afterStart through => ?_⟩
  exact (quiet_cuts advanceL advanceR paidL paidR ordinaryL ordinaryR openingL openingR
    strategy matched quiet i (shared i afterStart (Nat.le_of_lt through)) (unpaid i afterStart through)).2

theorem forever_without_payment (start : Nat) (common : (leftRun start).2 = (rightRun start).2)
    (unpaid : ∀ i, start ≤ i → leftPaid i = none) :
    ∀ i, start ≤ i → (leftRun i).2 = (rightRun i).2 ∧ rightPaid i = none := by
  intro i afterStart
  have bounded := before_payment advanceL advanceR paidL paidR ordinaryL ordinaryR openingL openingR
    strategy matched quiet start (i + 1) common (fun j reached _ => unpaid j reached)
  exact ⟨bounded.1 i afterStart (Nat.le_succ _), bounded.2 i afterStart (Nat.lt_succ_self _)⟩

/-- A first distinct reply at the same ordinary due coordinate has an
actual, identical bill selected on each side of the public fibre. -/
theorem first_divergence_pays_on_both (n : Nat) (common : (leftRun n).2 = (rightRun n).2)
    (different : (leftRun (n + 1)).2 ≠ (rightRun (n + 1)).2) :
    ∃ bill, leftPaid n = some bill ∧ rightPaid n = some bill := by
  have notQuiet : leftPaid n ≠ none := fun unpaid =>
    different (quiet_cuts advanceL advanceR paidL paidR ordinaryL ordinaryR openingL openingR
      strategy matched quiet n common unpaid).1
  obtain ⟨bill, charged⟩ := Option.ne_none_iff_exists'.mp notQuiet
  refine ⟨bill, charged, ?_⟩
  change paidR (rightRun n).1 (strategy n (rightRun n).2) = some bill
  rw [← common]
  exact (matched n common).2.symm.trans charged

omit matched quiet in
private theorem common_through (limit : Nat) (common : (leftRun limit).2 = (rightRun limit).2)
    {n : Nat} (earlier : n ≤ limit) : (leftRun n).2 = (rightRun n).2 := by
  induction limit with
  | zero =>
    rw [Nat.eq_zero_of_le_zero earlier]
    exact common
  | succ limit previous =>
    rcases Nat.eq_or_lt_of_le earlier with same | before
    · rw [same]
      exact common
    · apply previous ?_ (Nat.le_of_lt_succ before)
      change _ :: (leftRun limit).2 = _ :: (rightRun limit).2 at common
      exact (List.cons.inj common).2

/-- Locate the first actual divergence within a changed finite
transcript, even when the comparison starts after earlier paid history. -/
theorem locate_first_divergence (start limit : Nat) (within : start ≤ limit)
    (common : (leftRun start).2 = (rightRun start).2) (different : (leftRun limit).2 ≠ (rightRun limit).2) :
    ∃ n, start ≤ n ∧ n < limit ∧
      (∀ i, start ≤ i → i ≤ n → (leftRun i).2 = (rightRun i).2) ∧
      (leftRun (n + 1)).2 ≠ (rightRun (n + 1)).2 ∧
      ∃ bill, leftPaid n = some bill ∧ rightPaid n = some bill := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le within
  induction d with
  | zero => exact (different common).elim
  | succ d previous =>
    classical
    by_cases same : (leftRun (start + d)).2 = (rightRun (start + d)).2
    · refine ⟨start + d, Nat.le_add_right _ _, Nat.lt_succ_self _, ?_, different, ?_⟩
      · intro i _ through
        exact common_through advanceL advanceR openingL openingR strategy _ same through
      · exact first_divergence_pays_on_both advanceL advanceR paidL paidR ordinaryL ordinaryR
          openingL openingR strategy matched quiet _ same different
    · obtain ⟨n, reached, bounded, prefixAgreement, atNext, paid⟩ := previous (Nat.le_add_right _ _) same
      exact ⟨n, reached, Nat.lt_succ_of_lt bounded, prefixAgreement, atNext, paid⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Coupling
