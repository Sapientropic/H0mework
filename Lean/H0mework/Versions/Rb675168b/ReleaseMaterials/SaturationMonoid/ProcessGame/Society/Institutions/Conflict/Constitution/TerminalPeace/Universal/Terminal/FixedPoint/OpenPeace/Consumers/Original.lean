import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Repair
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Original

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Migration (sourceAlphabet)
open Conflict.Consumers.Evolving (compact)
open NoFreeProbe
open NoFreeProbe.Prepayment (BaseBudget CanPrepay PaymentOrders registeredTerms)
open TerminalPeace.Supply (grow personalWord)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open private current tariff wireFor harmless harmless_has_no_foreign_debit admits_one renewal_word from
  H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original
open private signedOrder own_literal_order original_budget from
  H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Consumers.Original
open private personal_registered from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalRecipe
open private AdaptivePeace.State.start from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch
open private State.start from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch

noncomputable section

private abbrev exitWord := personalWord false
private abbrev rawBase := Settlement.settledCut.raw

private def locked : ProgrammeSource.Input Bool Bool Bool Unit Unit :=
  { current.programme with law := { current.programme.law with policy := .opaque (fun _ _ => false) } }

private theorem original_exit_at (raw : TerminalPeace.Original.Raw) (reserved : InReserve rawBase raw) :
    Supply.Registered current.programme raw exitWord ∧
      Supply.Period current.programme OriginalReview.origin raw [false] exitWord := by
  refine ⟨personal_registered raw false, ?_⟩
  have base := OriginalRecipe.paidAt OriginalReview.origin rawBase [false] exitWord (by
    change OriginalRecipe.periodPasses [false] exitWord Settlement.settledCut.raw = true
    rw [Settlement.settled_raw]
    decide +kernel)
  let extra := InReserve.extra rawBase raw
  have duration := current.recipe.law.positive.trans_le
    (current.recipe.law.duration extra reserved.extra_nonnegative raw.clock raw.round)
  have later := base.after_reserve_and_clock current.recipe.law.timing current.recipe.law.reserve
    extra reserved.extra_nonnegative raw.clock raw.round duration
  rwa [← reserved.exact_raw] at later

private theorem candidate_keeps_the_literal_registration (raw : TerminalPeace.Original.Raw) :
    Supply.Registered locked raw exitWord := by
  intro request listed
  change request ∈ locked.localAttempts raw ++ ProgrammeSource.wordAt locked raw
  apply List.mem_append_left _
  change request ∈ compact.localAttempts raw ++ (OriginalRecipe.offer.pilot ++ OriginalRecipe.offer.attempts)
  apply List.mem_append_right _
  apply List.mem_append_left _
  change request ∈ Supply.Consumers.refillWord
  simp [personalWord] at listed
  rcases listed with rfl | rfl
  all_goals simp [Supply.Consumers.refillWord]

private theorem candidate_denies_the_exact_original_exit (raw : TerminalPeace.Original.Raw) :
    ¬ Supply.Period locked OriginalReview.origin raw [false] exitWord := by
  intro paid
  let first : ExecutionItem Bool Bool Bool Unit Unit := ⟨0, raw, grow false⟩
  have listed : first ∈ locked.law.rawItems raw exitWord := List.mem_cons_self
  have blocked : false = true := (paid.own first listed).valid.1.2
  contradiction

private abbrev inertWire := wireFor harmless

private theorem the_old_readout_has_no_aggression :
    ¬ DemandsAggression (community := TerminalPeace.Original.community)
      current.programme.law current.physical.raw (bill tariff inertWire) :=
  harmless_has_no_foreign_debit

private abbrev exitClaim : Claim Bool Bool Bool Unit Unit := ([false], exitWord)

private theorem the_live_original_claim : nativeContinuation current current.programme exitClaim :=
  original_exit_at current.physical.raw current.reserved

private theorem the_missing_claim : exitClaim ∈ losses current locked :=
  ⟨the_live_original_claim, fun kept => candidate_denies_the_exact_original_exit _ kept.2⟩

theorem a_new_policy_removes_an_exact_paid_exit_from_the_same_word :
    Supply.Registered locked current.physical.raw exitWord ∧
      exitClaim ∈ losses current locked ∧
      ¬ DemandsAggression (community := TerminalPeace.Original.community)
        current.programme.law current.physical.raw (bill tariff inertWire) :=
  ⟨candidate_keeps_the_literal_registration current.physical.raw, the_missing_claim, the_old_readout_has_no_aggression⟩

private def candidate (changePolicy : Bool) : ProgrammeSource.Input Bool Bool Bool Unit Unit :=
  if changePolicy then locked else current.programme

private def oldBill (_changePolicy : Bool) : ReviewBid Bool Bool Bool Unit Unit :=
  bill tariff inertWire

/-- The same harmless filing and tariff cannot decide whether its new
programme would take away the original actor's paid continuation. -/
theorem the_old_quote_does_not_classify_the_new_continuation_loss :
    ¬ ∃ classify : ReviewBid Bool Bool Bool Unit Unit → Set (Claim Bool Bool Bool Unit Unit),
      ∀ changePolicy, classify (oldBill changePolicy) = losses current (candidate changePolicy) :=
  no_exact_loss_classifier current oldBill candidate
    (hiddenContinuationLoss current oldBill candidate false true rfl exitClaim
      the_live_original_claim the_missing_claim)

private abbrev lockedProposal : OpenPeace.Proposal Bool Bool Bool Unit Unit := ⟨inertWire, locked⟩
private abbrev safeProposal : OpenPeace.Proposal Bool Bool Bool Unit Unit := ⟨inertWire, current.programme⟩
private abbrev lockedInput : Input Bool Bool Bool Unit Unit := .proposal lockedProposal
private def shifted : ProgrammeSource.Input Bool Bool Bool Unit Unit :=
  { current.programme with initial := { current.programme.initial with clock := current.programme.initial.clock + 1 } }

private def nextWire : Wire Bool Bool Bool Unit Unit := { inertWire with clock := current.move.next.clock }
private abbrev shiftedProposal : OpenPeace.Proposal Bool Bool Bool Unit Unit := ⟨nextWire, shifted⟩
private abbrev shiftedInput : Input Bool Bool Bool Unit Unit := .proposal shiftedProposal

private def billOrders : PaymentOrders Bool Bool Bool Unit Unit := fun clock bid actor =>
  signedOrder inertWire clock bid actor || signedOrder nextWire clock bid actor

private abbrev home := current.ledger.resident.erase
private abbrev replies := OriginalReview.personalReplies false
private abbrev Terms := RawLaw Bool Bool Bool Unit Unit × RawEvent Bool Bool Bool Unit Unit
private abbrev see : OriginalReview.State → Terms := registeredTerms

private def programmeOrder (proposal : OpenPeace.Proposal Bool Bool Bool Unit Unit) :
    OpenOrders Bool Bool Bool Unit Unit := by
  classical
  exact fun clock bid programme person =>
    decide (clock = proposal.wire.clock ∧ bid = bill tariff proposal.wire ∧
      programme = proposal.programme ∧ person = proposal.wire.payer)

private def opens : OpenOrders Bool Bool Bool Unit Unit := fun clock bid programme actor =>
  programmeOrder lockedProposal clock bid programme actor ||
    programmeOrder shiftedProposal clock bid programme actor

private abbrev selectedOrders := lockedInput.orders billOrders opens

private theorem old_and_new_orders_agree :
    selectedOrders current.physical.raw.clock (bill tariff inertWire) inertWire.payer = true := by
  have exactOrder : programmeOrder lockedProposal inertWire.clock (bill tariff inertWire) locked inertWire.payer = true := by
    simp [programmeOrder]
  exact Bool.and_eq_true_iff.mpr ⟨Bool.or_eq_true_iff.mpr (.inl (own_literal_order inertWire)),
    Bool.or_eq_true_iff.mpr (.inl exactOrder)⟩

private theorem lockedCanPay :
    CanPrepay see tariff home selectedOrders (see current) current.physical.raw.clock inertWire :=
  ⟨rfl, rfl, (admits_one harmless).passes_public_screen, (admits_one harmless).standing,
    old_and_new_orders_agree, (Prepayment.uniform_registered_budget_iff current _).mpr
      ⟨original_budget.legal, original_budget.nonnegative, original_budget.fits, original_budget.surplus⟩⟩

private abbrev charged :=
  (lockedCanPay.budget current rfl rfl).write (tariff.positive inertWire.attempted)

private theorem shifted_is_different : current.programme ≠ shifted := by
  intro same
  have clock := congrArg (fun programme : ProgrammeSource.Input Bool Bool Bool Unit Unit =>
    programme.initial.clock) same
  change current.programme.initial.clock = current.programme.initial.clock + 1 at clock
  linarith only [clock]

/-- The old material quote stays the same when the programme changes,
but the source's actual consent binds the submitted programme. -/
theorem identical_old_bills_do_not_share_the_exact_programme_order :
    bill tariff safeProposal.wire = bill tariff lockedProposal.wire ∧
      selectedOrders current.physical.raw.clock (bill tariff inertWire) inertWire.payer = true ∧
      (Input.proposal safeProposal).orders billOrders opens current.physical.raw.clock
        (bill tariff inertWire) inertWire.payer = false := by
  have distinct : current.programme ≠ locked := by
    intro same
    have live := (original_exit_at current.physical.raw current.reserved).2
    rw [same] at live
    exact candidate_denies_the_exact_original_exit _ live
  refine ⟨rfl, old_and_new_orders_agree, ?_⟩
  change (billOrders _ _ _ && opens _ _ current.programme _) = false
  simp [opens, programmeOrder, distinct, shifted_is_different]

private abbrev initial := State.start (AdaptivePeace.State.start current)
private abbrev actual := OpenPeace.source tariff home billOrders opens replies initial lockedInput
private abbrev proposedScope := scope tariff home billOrders opens replies initial lockedInput
private abbrev arrived := next tariff home billOrders opens replies initial lockedInput
private abbrev installed := languageWrite tariff home billOrders opens replies initial lockedInput
private abbrev exitEffect : Effect Bool Bool Bool Unit Unit := .inl exitClaim
private abbrev termsEffect : Effect Bool Bool Bool Unit Unit := .inr ()

private theorem original_receipt : actual.source = .prepaid inertWire lockedCanPay charged :=
  proposal_source_paid tariff home billOrders opens replies initial lockedProposal lockedCanPay

private theorem exact_scope : proposedScope = paidEffects charged locked :=
  paid_proposal_scope tariff home billOrders opens replies initial lockedProposal original_receipt

private theorem original_effect : exitEffect ∈ proposedScope := by
  rw [exact_scope]
  change Sum.inl exitClaim ∈ paidEffects charged locked
  rw [paidEffects_loss, paidLosses_eq]
  exact the_missing_claim

private theorem original_novel : ¬ proposedScope ⊆ initial.language.covered := by
  intro covered
  have already := covered original_effect
  change exitEffect ∈ (Language.initial : Language (RawEvent Bool Bool Bool Unit Unit)
    (Effect Bool Bool Bool Unit Unit)).covered at already
  rw [Language.covered_initial] at already
  exact already

private theorem original_programme_survives : arrived.adaptive.native.programme = current.programme := by
  have programme : actual.source.next.programme = current.programme := by
    rw [original_receipt]
    exact charged.programme
  exact (same_programme tariff home billOrders opens replies initial lockedInput).trans
    (actual.same_programme.trans programme)

private theorem first_lands_at : arrived.adaptive.native.physical.raw.clock = current.move.next.clock := by
  rw [same_physical_successor, actual.same_physical_successor, original_receipt]
  exact charged.settledClock

/-- The old bill pays at original material position 6. The paid visit
preserves the native programme and settles a new language direction. -/
theorem the_original_paid_proposal_generates_a_new_exit_refusal :
    amendment tariff home billOrders opens replies initial lockedInput = some installed ∧
      exitEffect ∈ arrived.language.covered ∧
      arrived.adaptive.native.programme = current.programme ∧
      HEq arrived.adaptive.native.ledger.stack current.ledger.stack ∧
      (OpenPeace.observe tariff home billOrders opens replies initial lockedInput).landsAt = current.move.next.clock ∧
      (OpenPeace.observe tariff home billOrders opens replies initial lockedInput).reply =
        .ordinary (.prepaid .ineligible) ∧
      (⟨actual.next.native.ledger.world,
        (Installation.Live.action actual.next.native.ledger installed.read true).target.targetAnswerAndNext.nextCurrent⟩ :
          AnyAuthoritativeRootCurrent) = arrived.adaptive.native.ledger.resident.erase ∧
      ∃ item, actual.source.round.visit.read.effect.execution.items[6]? = some item ∧
        item.request.signer = true ∧
        actual.source.round.visit.read.programme.law.actualDebit item.before item.request =
          locate true [(true, 1/6), (true, 1/6), (true, 1/6)] ∧
        actual.source.round.visit.read.programme.law.actualCredit item.before item.request = [] := by
  obtain ⟨posted, _, _, wholeNext⟩ :=
    language_first_write tariff home billOrders opens replies initial lockedInput original_novel
  have stack : HEq actual.source.next.ledger.stack current.ledger.stack := by
    rw [original_receipt]
    rfl
  refine ⟨posted, seals_scope tariff home billOrders opens replies initial lockedInput original_effect,
    original_programme_survives,
    (same_stack tariff home billOrders opens replies initial lockedInput).trans (actual.same_stack.trans stack),
    (observation_lands_at_the_original_successor tariff home billOrders opens replies initial lockedInput).trans first_lands_at,
    a_paid_proposal_gets_the_fixed_refusal tariff home billOrders opens replies initial lockedProposal original_receipt,
    wholeNext, ?_⟩
  have expense := charged.original_expense
  rw [renewal_word] at expense
  rw [original_receipt]
  exact expense

private theorem the_initial_policy_breaks_public_terms : ¬ KeepsPublicTerms current.programme locked := by
  intro kept
  have same : locked = current.programme := kept
  have lost := the_missing_claim
  rw [same, original_programme_has_no_losses] at lost
  exact lost

private theorem terms_effect_is_covered : termsEffect ∈ arrived.language.covered := by
  apply seals_scope tariff home billOrders opens replies initial lockedInput
  change termsEffect ∈ proposedScope
  rw [exact_scope]
  change Sum.inr () ∈ paidEffects charged locked
  exact (paidEffects_public_terms charged locked).mpr the_initial_policy_breaks_public_terms

private abbrev afterNative := arrived.adaptive.native
private abbrev laterOrders := shiftedInput.orders billOrders opens
private abbrev later := OpenPeace.source tariff home billOrders opens replies arrived shiftedInput

private theorem the_first_recipe_word_survives : afterNative.recipe.move.word = current.recipe.move.word := by
  have landed : afterNative.recipe.move.word = actual.next.native.recipe.move.word := by
    unfold afterNative arrived next
    split <;> rfl
  have kept : actual.next.native.recipe.move.word = actual.source.next.recipe.move.word := by
    generalize actual = step
    cases step <;> rfl
  rw [landed, kept, original_receipt]
  rfl

private theorem shiftedCanPay :
    CanPrepay see tariff home laterOrders (see afterNative) afterNative.physical.raw.clock nextWire := by
  refine ⟨rfl, first_lands_at.symm, (admits_one harmless).passes_public_screen, (admits_one harmless).standing,
    ?_, (Prepayment.uniform_registered_budget_iff afterNative _).mpr ?_⟩
  · rw [first_lands_at]
    have exactOrder : programmeOrder shiftedProposal nextWire.clock (bill tariff nextWire) shifted
        nextWire.payer = true := by
      simp [programmeOrder]
    exact Bool.and_eq_true_iff.mpr ⟨Bool.or_eq_true_iff.mpr (.inr (own_literal_order nextWire)),
      Bool.or_eq_true_iff.mpr (.inr exactOrder)⟩
  · have law := congrArg ProgrammeSource.Input.law original_programme_survives
    rw [law, the_first_recipe_word_survives]
    exact ⟨original_budget.legal, original_budget.nonnegative, original_budget.fits, original_budget.surplus⟩

private abbrev laterPaid :=
  (shiftedCanPay.budget afterNative rfl rfl).write (tariff.positive nextWire.attempted)

private theorem later_receipt : later.source = .prepaid nextWire shiftedCanPay laterPaid :=
  proposal_source_paid tariff home billOrders opens replies arrived shiftedProposal shiftedCanPay

private theorem shifted_has_no_material_losses : paidLosses laterPaid shifted = ∅ := by
  rw [paidLosses_eq]
  apply no_rewrite_of_existing_alphabet_has_no_losses
  · exact (congrArg ProgrammeSource.Input.law original_programme_survives).symm
  · intro request registered
    change request ∈ sourceAlphabet current.programme afterNative.physical.raw
    rwa [original_programme_survives] at registered

private theorem the_later_scope_is_the_old_public_term :
    scope tariff home billOrders opens replies arrived shiftedInput = {termsEffect} := by
  rw [paid_proposal_scope tariff home billOrders opens replies arrived shiftedProposal later_receipt]
  ext effect
  cases effect with
  | inl claim => simp only [paidEffects_loss, shifted_has_no_material_losses, Set.mem_empty_iff_false,
      Set.mem_singleton_iff, Sum.inl_ne_inr]
  | inr term =>
    cases term
    have changes : ¬ KeepsPublicTerms afterNative.programme shifted := by
      rw [original_programme_survives]
      intro same
      exact shifted_is_different (show shifted = current.programme from same).symm
    exact (paidEffects_public_terms laterPaid shifted).trans
      ⟨fun _ => rfl, fun _ => changes⟩

/-- The next signed proposal changes a protected term while preserving
all actual continuations. That effect has an old refusal expression. -/
theorem a_fresh_paid_proposal_in_the_old_scope_has_no_new_epoch :
    inertWire.clock < nextWire.clock ∧ later.source.paidWire = some nextWire ∧
      (OpenPeace.observe tariff home billOrders opens replies arrived shiftedInput).reply =
        .ordinary (.prepaid .ineligible) ∧
      amendment tariff home billOrders opens replies arrived shiftedInput = none ∧
      (next tariff home billOrders opens replies arrived shiftedInput).language = arrived.language := by
  have covered : scope tariff home billOrders opens replies arrived shiftedInput ⊆ arrived.language.covered := by
    rw [the_later_scope_is_the_old_public_term]
    exact Set.singleton_subset_iff.mpr terms_effect_is_covered
  have noRepair := (no_repair_iff tariff home billOrders opens replies arrived shiftedInput).mpr covered
  have ticks := charged.round.clock
  rw [charged.settledClock] at ticks
  have laterClock := (lt_add_of_pos_right _ current.recipe.law.positive).trans_le ticks
  exact ⟨laterClock, congrArg Prepayment.Step.paidWire later_receipt,
    a_paid_proposal_gets_the_fixed_refusal tariff home billOrders opens replies arrived shiftedProposal later_receipt,
    noRepair, by rw [next, noRepair]; rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Original
