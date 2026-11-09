import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalRecipe
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Closure

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OriginalReview

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open Conflict.Consumers.Evolving (levy)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open OriginalRecipe (programme originalRecipe exact_gain)
open Supply.Consumers (refillWord)

noncomputable section

abbrev origin := originalRaw Original.occurrence
abbrev State := Current (seed := Original.seed) (cut := Settlement.settledCut) (community := Original.community)
  origin [false, true] 1

def initial : State :=
  ⟨Settlement.settled, Settlement.settledCut.state, programme, originalRecipe origin,
    ⟨fun _ _ => le_rfl, rfl, rfl⟩⟩

def bid : ReviewBid Bool Bool Bool Unit Unit :=
  ⟨true, [levy], false, ⟨[(true, 1/6)], [(true, 1/6)], [(true, 1/6)]⟩⟩

def freeBid : ReviewBid Bool Bool Bool Unit Unit :=
  { bid with parts := ⟨[], [], []⟩ }

def personalReplies (payerApproves : Bool) : Replies Bool Bool Bool Unit Unit :=
  ⟨fun _ _ _ person => person && payerApproves, fun _ _ _ _ => false⟩

private theorem fee_exact (person good : Bool) :
    bid.fee person good = if person && good then (1/2 : ℚ) else 0 := by
  cases person <;> cases good <;> decide +kernel

private theorem own_charge_is_legal (raw : Original.Raw) (enough : (1/2 : ℚ) ≤ raw.stock true true) :
    programme.law.Valid raw (reviewRequest bid.payer bid.port bid.expenses) := by
  unfold RawLaw.Valid
  refine ⟨⟨trivial, rfl⟩, ?_, trivial, ?_, ?_, ?_⟩
  · intro port _
    cases port <;> exact Or.inl rfl
  · intro lot present
    change lot ∈ [((true, true), (1/6 : ℚ)), ((true, true), 1/6), ((true, true), 1/6)] at present
    have same : lot = ((true, true), (1/6 : ℚ)) := by simpa using present
    rw [same]
    norm_num
  · intro lot present
    exact (List.not_mem_nil present).elim
  · intro lot present
    change lot ∈ [((true, true), (1/6 : ℚ)), ((true, true), 1/6), ((true, true), 1/6)] at present
    have same : lot = ((true, true), (1/6 : ℚ)) := by simpa using present
    rw [same]
    exact (show flowAt (locate true [(true, 1/6), (true, 1/6), (true, 1/6)]) true true = (1/2 : ℚ)
      by decide +kernel).le.trans enough

variable (current : State)

private theorem unchanged_gain (same : current.programme = programme) (word : current.move.word = refillWord)
    (person good : Bool) : current.recipe.gain person good = if good then 1 else 0 := by
  have literal := (current.recipe.moveAt_word current.physical.raw current.reserved).symm.trans word
  change Balance.gain current.programme.law OriginalRecipe.opening current.recipe.move.word person good = _
  rw [literal, same]
  exact exact_gain origin person good

private theorem accountable (same : current.programme = programme) (word : current.move.word = refillWord) :
    AccountableReview (personalReplies true) current bid := by
  have gain := unchanged_gain current same word
  refine ⟨by decide, ?_, rfl, ?_, ⟨true, by decide +kernel⟩, ?_, ⟨true, true, ?_⟩⟩
  · let item : Original.Item := ⟨0, current.physical.raw, levy⟩
    have notConsent : false ∉ levy.consents := by decide +kernel
    refine ⟨item, List.mem_cons_self, rfl, false, false, by decide, notConsent, ?_⟩
    change flowAt (locate true [(false, 6)]) false false < flowAt (locate false [(false, 6)]) false false
    decide +kernel
  · unfold ReviewLegal
    rw [word, same]
    apply own_charge_is_legal
    have stock := current.reserved.stock true true
    have initialFood : OriginalRecipe.opening.stock true true = 1 := by
      change Settlement.settledCut.raw.stock true true = _
      rw [Settlement.settled_raw]
      rfl
    have kept := current.recipe.next_material current.physical.raw current.reserved true true
    rw [gain true true] at kept
    change (current.programme.law.next current.physical.raw current.move.word).stock true true = _ at kept
    rw [word, same] at kept
    change (programme.law.next current.physical.raw refillWord).stock true true =
      current.physical.raw.stock true true + 1 at kept
    change OriginalRecipe.opening.stock true true ≤ _ at stock
    rw [initialFood] at stock
    change (1/2 : ℚ) ≤ (programme.law.next current.physical.raw refillWord).stock true true
    linarith only [stock, kept]
  · refine ⟨?_, ?_⟩
    · intro person good
      rw [fee_exact]
      cases person <;> cases good <;> decide +kernel
    · intro person good
      rw [fee_exact, gain]
      cases person <;> cases good <;> decide +kernel
  · rw [fee_exact, gain]
    norm_num

/-- A paid proposal on any protected current using the original growth
recipe costs its own payer exactly half a food unit. The original ledger
and its next visit are those of the dispatched round. -/
theorem the_original_review_costs_half_and_still_grows
    (same : current.programme = programme) (word : current.move.word = refillWord) :
    let round := dispatch (personalReplies true) current (.review bid)
    round.visit.read.disposition = .reviewed ∧
      round.next.programme = current.programme ∧ round.next.recipe.move.word = current.recipe.move.word ∧
      round.next.physical.raw.stock true true = current.physical.raw.stock true true + (1/2 : ℚ) ∧
      round.next.ledger.stack.balances = current.ledger.stack.balances ∧
      round.visit.read.effect.execution.items[6]? =
        some (reviewItem programme current.physical.raw refillWord bid.payer bid.port bid.expenses) ∧
      (∀ weight : Bool → ℚ, (∀ good, 0 < weight good) →
        materialPayoff bid round.next.physical.raw current.move.next weight < 0) := by
  let round := dispatch (personalReplies true) current (.review bid)
  have paid := accountable current same word
  have result := every_accountable_attack_is_strictly_costly (personalReplies true) current bid paid (fun _ => 1)
    (fun _ => by norm_num)
  have finished : round = paidReviewRound current bid paid.legal paid.fits paid.surplus := by
    simp only [round, dispatch, dif_pos paid]
  have unchanged : round.next.recipe.move.word = current.recipe.move.word := by
    rw [finished]
    rfl
  refine ⟨result.1, result.2.1, unchanged, ?_, round.rows, ?_, fun weight positive => ?_⟩
  · have stock := (paidReviewRound_reads_the_payers_whole_cost current bid paid.legal paid.fits paid.surplus).2.2.2.2.2.2 true true
    rw [← finished, fee_exact] at stock
    have peaceful := current.recipe.next_material current.physical.raw current.reserved true true
    rw [unchanged_gain current same word] at peaceful
    change round.next.physical.raw.stock true true - current.move.next.stock true true = -(1/2 : ℚ) at stock
    change current.move.next.stock true true = current.physical.raw.stock true true + 1 at peaceful
    linarith only [stock, peaceful]
  · have actual := accountable_review_posts_cost_at_the_actual_position (personalReplies true) current bid paid
    rw [word, same] at actual
    exact actual
  · exact (every_accountable_attack_is_strictly_costly (personalReplies true) current bid paid weight positive).2.2.2.2.2.2.2

/-- Keeping the hostile proposal and withholding its original signature
selects only the uncharged production word. -/
theorem refusal_keeps_the_same_unpaid_presentation :
    let round := dispatch (personalReplies false) current (.review bid)
    round.visit.read.disposition = .presentation ∧ round.next.physical.raw = current.move.next ∧
      (∀ weight : Bool → ℚ, materialPayoff bid round.next.physical.raw current.move.next weight = 0) ∧
      round.next.ledger.stack.balances = current.ledger.stack.balances := by
  let round := dispatch (personalReplies false) current (.review bid)
  have refused : ¬ AccountableReview (personalReplies false) current bid := fun paid => by
    have impossible : false = true := paid.signed
    cases impossible
  have result := an_unfunded_presentation_leaves_no_material_windfall (personalReplies false) current bid refused
  exact ⟨(result (fun _ => 1)).1, (result (fun _ => 1)).2.2.1, fun weight => (result weight).2.2.2, round.rows⟩

/-- A signed request with no positive physical cost is a presentation.
Its surviving living word is exactly the uncharged one. -/
theorem a_signed_zero_fee_never_writes_a_charge :
    let round := dispatch (personalReplies true) current (.review freeBid)
    round.visit.read.disposition = .presentation ∧ round.visit.read.commands = current.move.word ∧
      round.next.physical.raw = current.move.next ∧
      round.next.ledger.stack.balances = current.ledger.stack.balances := by
  let round := dispatch (personalReplies true) current (.review freeBid)
  have exact := zero_fee_submissions_have_the_same_production_effect
    (personalReplies true) current freeBid (fun _ => rfl)
  exact ⟨exact.1, exact.2.1, exact.2.2, round.rows⟩

def reviewOrRenew (requests : Nat → AnyAuthoritativeRootCurrent.{0} → Original.Raw → Bool) :
    Policy Bool Bool Bool Unit Unit :=
  fun n resident raw => if requests n resident raw then .review bid else .renew

/-- Arbitrary observation-dependent selection of the paid original review
and uncharged renewal leaves at least half a food unit per actual round. -/
theorem every_original_review_schedule_retains_half_per_round
    (requests : Nat → AnyAuthoritativeRootCurrent.{0} → Original.Raw → Bool) (n : Nat) :
    let actual := history (personalReplies true) initial (reviewOrRenew requests) n
    actual.ledger.stack.balances = Settlement.settled.stack.balances ∧
    initial.physical.raw.stock true true + (n : ℚ) / 2 ≤ actual.physical.raw.stock true true := by
  have invariant (n : Nat) :
      let actual := history (personalReplies true) initial (reviewOrRenew requests) n
      actual.programme = programme ∧ actual.recipe.move.word = refillWord ∧
        initial.physical.raw.stock true true + (n : ℚ) / 2 ≤ actual.physical.raw.stock true true := by
    induction n with
    | zero =>
      refine ⟨rfl, rfl, ?_⟩
      change initial.physical.raw.stock true true + (0 : ℚ) / 2 ≤ initial.physical.raw.stock true true
      simp
    | succ n earlier =>
      let before := history (personalReplies true) initial (reviewOrRenew requests) n
      obtain ⟨same, literal, stock⟩ := earlier
      have word : before.move.word = refillWord :=
        (before.recipe.moveAt_word before.physical.raw before.reserved).trans literal
      let submitted := reviewOrRenew requests n before.ledger.resident.erase before.physical.raw
      let next := (dispatch (personalReplies true) before submitted).next
      change next.programme = programme ∧ next.recipe.move.word = refillWord ∧
        initial.physical.raw.stock true true + ((n+1 : Nat) : ℚ) / 2 ≤ next.physical.raw.stock true true
      by_cases chosen : requests n before.ledger.resident.erase before.physical.raw = true
      · have selected : submitted = .review bid := if_pos chosen
        dsimp only [next]
        rw [selected]
        obtain ⟨_, sameProgramme, sameWord, actual, _, _, _⟩ :=
          the_original_review_costs_half_and_still_grows before same word
        refine ⟨sameProgramme.trans same, sameWord.trans literal, ?_⟩
        rw [actual, Nat.cast_succ]
        linarith only [stock]
      · have selected : submitted = .renew := if_neg chosen
        dsimp only [next]
        rw [selected]
        have read := productiveRound_reads_selected_production before .renew .renewed before.programme before.recipe
        have increment := before.recipe.next_material before.physical.raw before.reserved true true
        rw [unchanged_gain before same word] at increment
        change before.move.next.stock true true = before.physical.raw.stock true true + 1 at increment
        refine ⟨same, literal, ?_⟩
        change _ ≤ (productiveRound before .renew .renewed before.programme before.recipe).next.physical.raw.stock true true
        rw [read.2.1, increment, Nat.cast_succ]
        linarith only [stock]
  exact ⟨history_keeps_every_original_balance (personalReplies true) initial (reviewOrRenew requests) n,
    (invariant n).2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OriginalReview
