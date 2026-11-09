import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Contract
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Original

open Capitalism.Universal.Source.Program
open Conflict.Consumers.Evolving (levy)
open NoFreeProbe
open NoFreeProbe.Prepayment (BaseBudget CanPrepay PaymentOrders registeredTerms)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open private current tariff wireFor admits_one renewal_word harmless from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original
open private signedOrder own_literal_order original_budget consented from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Consumers.Original
open private itemDemands from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Exposure
open private State.start from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

noncomputable section

private abbrev Packet := Wire Bool Bool Bool Unit Unit
private abbrev Instruction := Request Bool Bool Bool Unit Unit
private abbrev Terms := RawLaw Bool Bool Bool Unit Unit × RawEvent Bool Bool Bool Unit Unit
private abbrev see : OriginalReview.State → Terms := registeredTerms
private abbrev home := current.ledger.resident.erase
private abbrev replies := OriginalReview.personalReplies false
private abbrev originalWire := wireFor levy
private abbrev initial := State.start current
private abbrev cell : Bool × Bool := (false, false)

private def levyAt (quantity : ℚ) : Instruction :=
  { levy with operation := .transfer false true [(false, quantity)] }

private def nextWire (instruction : Instruction) : Packet :=
  { wireFor instruction with clock := current.move.next.clock }

private abbrev smaller := nextWire (levyAt 3)
private abbrev safeWire := nextWire harmless
private def delegated : Packet := { nextWire levy with sender := false, payer := false }

private abbrev signedWires : List Packet := [originalWire, smaller, safeWire, delegated]

private def orders : PaymentOrders Bool Bool Bool Unit Unit := fun now bid person =>
  signedWires.any fun wire => signedOrder wire now bid person

private theorem own_order (wire : Packet) (listed : wire ∈ signedWires) :
    orders wire.clock (bill tariff wire) wire.payer = true :=
  List.any_eq_true.mpr ⟨wire, listed, own_literal_order wire⟩

private theorem levy_scope (law : RawLaw Bool Bool Bool Unit Unit) (raw : TerminalPeace.Original.Raw)
    (wire : Packet) (quantity : ℚ) (positive : 0 < quantity)
    (word : wire.attempted = [levyAt quantity]) :
    demanded TerminalPeace.Original.community law raw (bill tariff wire) = {cell} := by
  ext key
  rw [mem_demanded_iff, Finset.mem_singleton]
  rcases key with ⟨person, good⟩
  have items : law.rawItems raw (bill tariff wire).attempted = [⟨0, raw, levyAt quantity⟩] := by
    change law.rawItems raw wire.attempted = _
    rw [word]
    rfl
  rw [demandsAt, items]
  simp only [List.mem_singleton, exists_eq_left]
  cases person <;> cases good <;>
    simp [itemDemands, levyAt, levy, RawLaw.credit, RawLaw.debit, flowAt, locate, amount, positive]

private theorem a_single_order_posts (before : OriginalReview.State) (wire : Packet)
    (allowed : CanPrepay see tariff home orders (see before) before.physical.raw.clock wire) :
    Prepayment.advanceRegistered tariff home orders before replies ⟨none, [wire]⟩ =
      .prepaid wire allowed ((allowed.budget before rfl rfl).write (tariff.positive wire.attempted)) := by
  have checked : Prepayment.inspectOrder see tariff home orders (see before) before.physical.raw.clock wire =
      some ⟨wire, allowed⟩ := by
    simp [Prepayment.inspectOrder, allowed, allowed.screened]
  have renews : (Prepayment.ordinary tariff replies before none).reply = .renewed := rfl
  have picked : Prepayment.selected tariff replies before see home orders ⟨none, [wire]⟩ =
      some ⟨wire, allowed⟩ := by
    simp [Prepayment.selected, Prepayment.selectInAgenda, Prepayment.selectOrder, renews, checked]
  rw [Prepayment.registered_dispatch_is_the_exact_private_dispatch, Prepayment.advance, picked]
  rfl

private theorem firstOrder :
    CanPrepay see tariff home orders (see initial.native) initial.native.physical.raw.clock originalWire :=
  ⟨consented.scope, consented.stamp, consented.screened, consented.standing,
    own_order originalWire List.mem_cons_self, consented.budget⟩

private abbrev debitAt {before : OriginalReview.State} {wire : Packet}
    (allowed : CanPrepay see tariff home orders (see before) before.physical.raw.clock wire) :=
  (allowed.budget before rfl rfl).write (tariff.positive wire.attempted)

private abbrev first := advance tariff home orders replies initial ⟨none, [originalWire]⟩

private theorem firstWitness : witnessed (debitAt firstOrder) = {cell} :=
  levy_scope _ _ originalWire 6 (by norm_num) rfl

private theorem firstNovel : ¬ witnessed (debitAt firstOrder) ⊆ initial.covered := by
  rw [firstWitness]
  simp [State.covered, State.start]

private theorem firstWrite : first = .amended originalWire firstOrder (debitAt firstOrder) firstNovel := by
  have charged := a_single_order_posts initial.native originalWire firstOrder
  have amended := a_novel_attack_lands_its_amendment tariff home orders replies initial originalWire firstOrder
    (debitAt firstOrder) firstNovel
  exact (congrArg (resolve tariff home orders replies initial) charged).trans
    amended

private theorem firstCovered : first.next.covered = {cell} := by
  rw [first.coverage_eq, firstWrite]
  change ∅ ∪ witnessed (debitAt firstOrder) = _
  rw [Finset.empty_union, firstWitness]

/-- The repaired coordinate is read after the original half-unit debit,
with the old settled balance and its address retained. -/
theorem the_original_paid_levy_repairs_its_exposed_cell :
    first.reply = .amended ∧ first.observe.reply = .ordinary (.prepaid .ineligible) ∧
      first.next.covered = {cell} ∧
      first.next.native.ledger.stack.balances = current.ledger.stack.balances ∧
      first.next.native.physical.raw.stock true true - current.move.next.stock true true = -(1/2 : ℚ) ∧
      ∃ item, first.source.round.visit.read.effect.execution.items[6]? = some item ∧
        item.request.signer = true ∧
        first.source.round.visit.read.programme.law.actualDebit item.before item.request =
          locate true [(true, 1/6), (true, 1/6), (true, 1/6)] ∧
        first.source.round.visit.read.programme.law.actualCredit item.before item.request = [] := by
  have covered := firstCovered
  have stock := (debitAt firstOrder).stock true true
  have half : (bill tariff originalWire).fee true true = (1/2 : ℚ) := by decide +kernel
  rw [half] at stock
  have expense := (debitAt firstOrder).original_expense
  have word : initial.native.move.word = Supply.Consumers.refillWord := renewal_word
  rw [word] at expense
  rw [firstWrite] at covered ⊢
  exact ⟨rfl, rfl, covered, repair_rows _ _, stock, expense⟩

theorem the_original_levy_lands_the_canonical_strict_successor :
    ∃ amendment : AmendmentAt first,
      first.amendment = some amendment.write ∧
      (⟨amendment.paid.round.next.ledger.world,
        (Installation.Core.action amendment.paid.round.next.ledger amendment.write.read
          true).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
        first.next.native.ledger.resident.erase ∧
      amendment.write.read = {cell} ∧ unsealed first.next ⊂ unsealed initial ∧
      (∀ weight : Bool → ℚ, (∀ good, 0 < weight good) →
        materialPayoff (bill tariff amendment.wire) first.next.native.physical.raw initial.native.move.next weight < 0) := by
  have novel : ¬ paidExposure tariff home orders replies initial first.source ⊆ initial.covered := by
    rw [firstWrite]
    exact firstNovel
  obtain ⟨amendment, written, installed, successor, _, smaller, costly, _⟩ :=
    every_novel_attack_generates_stronger_peace first novel
  have read : amendment.write.read = first.next.covered := by
    unfold State.covered
    rw [installed]
    rfl
  exact ⟨amendment, written, successor, read.trans firstCovered, smaller, costly⟩

private theorem firstClock : first.next.native.physical.raw.clock = current.move.next.clock := by
  rw [firstWrite]
  exact (debitAt firstOrder).settledClock

private theorem nextOrder (instruction : Instruction)
    (signed : orders (nextWire instruction).clock (bill tariff (nextWire instruction)) true = true) :
    CanPrepay see tariff home orders (see first.next.native) first.next.native.physical.raw.clock
      (nextWire instruction) := by
  refine ⟨rfl, firstClock.symm, (admits_one instruction).passes_public_screen, consented.standing,
    ?_, (Prepayment.uniform_registered_budget_iff _ _).mpr ?_⟩
  · rw [firstClock]
    exact signed
  · rw [firstWrite]
    exact ⟨original_budget.legal, original_budget.nonnegative, original_budget.fits, original_budget.surplus⟩

private theorem smallerOrder :
    CanPrepay see tariff home orders (see first.next.native) first.next.native.physical.raw.clock smaller :=
  nextOrder (levyAt 3) (own_order smaller (List.mem_cons_of_mem _ List.mem_cons_self))

private abbrev later := advance tariff home orders replies first.next ⟨none, [smaller]⟩

private theorem refusal_at (wire : Packet)
    (order : CanPrepay see tariff home orders (see first.next.native) first.next.native.physical.raw.clock wire)
    (scope : witnessed (debitAt order) = {cell}) :
    let visit := advance tariff home orders replies first.next ⟨none, [wire]⟩
    visit.source.paidWire = some wire ∧ visit.reply = .refused ∧
      visit.observe.reply = .ordinary (.prepaid .ineligible) ∧
      visit.amendment = none ∧ visit.next.covered = {cell} ∧
      ∀ person good, visit.next.native.physical.raw.stock person good - first.next.native.move.next.stock person good =
        -(bill tariff wire).fee person good := by
  have stays : witnessed (debitAt order) ⊆ first.next.covered := by rw [scope, firstCovered]
  have nonempty : witnessed (debitAt order) ≠ ∅ := by rw [scope]; simp
  have landed : advance tariff home orders replies first.next ⟨none, [wire]⟩ =
      .refused wire order (debitAt order) nonempty stays :=
    (congrArg (resolve tariff home orders replies first.next)
      (a_single_order_posts first.next.native wire order)).trans
      (a_covered_attack_gets_the_fixed_refusal tariff home orders replies first.next wire order
        (debitAt order) nonempty stays)
  dsimp only
  rw [landed]
  exact ⟨rfl, rfl, rfl, rfl, firstCovered, (debitAt order).stock⟩

/-- A newly signed, smaller levy at a later physical clock meets the
same original scope and lands the fixed refusal. -/
theorem a_fresh_smaller_levy_is_refused_in_the_same_scope :
    smaller.clock > originalWire.clock ∧ smaller.attempted ≠ originalWire.attempted ∧
      later.source.paidWire = some smaller ∧ later.reply = .refused ∧
      later.observe.reply = .ordinary (.prepaid .ineligible) ∧
      later.amendment = none ∧ later.next.covered = {cell} ∧
      later.next.native.physical.raw.stock true true - first.next.native.move.next.stock true true = -(1/2 : ℚ) := by
  have ticks := (debitAt firstOrder).round.clock
  rw [(debitAt firstOrder).settledClock] at ticks
  have clock : current.physical.raw.clock < current.move.next.clock :=
    (lt_add_of_pos_right _ current.recipe.law.positive).trans_le ticks
  have scope : witnessed (debitAt smallerOrder) = {cell} :=
    levy_scope _ _ smaller 3 (by norm_num) rfl
  obtain ⟨paid, denied, observed, noRepair, known, changed⟩ := refusal_at smaller smallerOrder scope
  have stock := changed true true
  have half : (bill tariff smaller).fee true true = (1/2 : ℚ) := by decide +kernel
  rw [half] at stock
  exact ⟨clock, by decide +kernel, paid, denied, observed, noRepair, known, stock⟩

private theorem safeOrder :
    CanPrepay see tariff home orders (see first.next.native) first.next.native.physical.raw.clock safeWire :=
  nextOrder harmless (own_order safeWire (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
private abbrev safeVisit := advance tariff home orders replies first.next ⟨none, [safeWire]⟩

/-- The same amended current still admits the signed harmless word
with the original prepayment, reply, and productive successor. -/
theorem the_harmless_paid_visit_is_unchanged :
    safeVisit.source.paidWire = some safeWire ∧
      safeVisit.reply = .ordinary safeVisit.source.reply ∧
      safeVisit.observe.reply = .ordinary safeVisit.source.reply ∧
      safeVisit.amendment = none ∧ safeVisit.next.covered = {cell} := by
  let base := Prepayment.advanceRegistered tariff home orders first.next.native replies ⟨none, [safeWire]⟩
  have picked := a_single_order_posts first.next.native safeWire safeOrder
  have safe : paidExposure tariff home orders replies first.next base = ∅ := by
    change paidExposure tariff home orders replies first.next
      (Prepayment.advanceRegistered tariff home orders first.next.native replies ⟨none, [safeWire]⟩) = ∅
    rw [picked]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro key listed
    change key ∈ witnessed (debitAt safeOrder) at listed
    obtain ⟨item, original, claim⟩ := (mem_witnessed_iff _ _).mp listed
    change item ∈ [⟨0, first.next.native.physical.raw, harmless⟩] at original
    rcases List.mem_singleton.mp original with rfl
    exact (lt_irrefl (0 : ℚ)) claim.2.2
  have original : safeVisit = .ordinary base safe := a_safe_original_visit_is_unchanged _ _ _ _ _ _ safe
  rw [original]
  exact ⟨congrArg Prepayment.Step.paidWire picked, rfl, rfl, rfl, firstCovered⟩

private theorem delegatedOrder :
    CanPrepay see tariff home orders (see first.next.native) first.next.native.physical.raw.clock delegated := by
  refine ⟨rfl, firstClock.symm, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · rw [firstClock]
    exact own_order delegated (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · apply (Prepayment.uniform_registered_budget_iff _ _).mpr
    rw [firstWrite]
    change BaseBudget current.programme.law Settlement.settledCut.raw current.recipe.move.word (bill tariff delegated)
    apply (Prepayment.budgetCheck_iff _ _ _ _).mp
    have word : current.recipe.move.word = Supply.Consumers.refillWord :=
      (current.recipe.moveAt_word current.physical.raw current.reserved).symm.trans renewal_word
    rw [word, Settlement.settled_raw]
    decide +kernel

/-- A different filer pays its own bill. The literal signer and the
victim's exposed coordinate still determine the same fixed refusal. -/
theorem a_different_filer_cannot_reopen_the_same_scope :
    delegated.payer ≠ levy.signer ∧
      let visit := advance tariff home orders replies first.next ⟨none, [delegated]⟩
      visit.source.paidWire = some delegated ∧ visit.reply = .refused ∧ visit.amendment = none ∧
        visit.next.native.physical.raw.stock false true - first.next.native.move.next.stock false true = -(1/2 : ℚ) := by
  have scope : witnessed (debitAt delegatedOrder) = {cell} :=
    levy_scope _ _ delegated 6 (by norm_num) rfl
  obtain ⟨paid, denied, _, noRepair, _, changed⟩ := refusal_at delegated delegatedOrder scope
  have stock := changed false true
  have half : (bill tariff delegated).fee false true = (1/2 : ℚ) := by decide +kernel
  rw [half] at stock
  exact ⟨by decide +kernel, paid, denied, noRepair, stock⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Original
