import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact (originalWord)
open Conflict.Consumers.Evolving (compact)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint (InReserve)
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open TerminalPeace.Supply (grow personalWord)
open Supply.Consumers (refillWord)
open private paidAt from H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalSource
open private home start packet submit visit turn scope debit paid_scope paid_wire termsEffect first first_scope
  first_novel first_ready first_reads initial_reads initial_ready schedule from H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision

noncomputable section

private abbrev exitClaim : Claim Bool Bool Bool Unit Unit := ([true], personalWord true)
private abbrev exitEffect : Effect Bool Bool Bool Unit Unit := .inl exitClaim

private theorem the_personal_word_still_pays_on_the_first_successor :
    nativeContinuation first.current first.current.programme exitClaim := by
  unfold nativeContinuation
  rw [first_ready.1]
  constructor
  · intro request listed
    apply FixedPoint.revision_registers_its_pilot compact offer first.current.physical.raw
    change request ∈ refillWord
    simp [refillWord, personalWord] at listed ⊢
    grind
  · let base := actualNetwork.paid.next.physical.raw
    have original : Supply.Period revised (originalRaw loss) base [true] (personalWord true) := by
      apply paidAt
      rw [show base = afterClear from payment_lands_at_the_actual_stock actualNetwork.paid]
      decide +kernel
    let code := codeFor revised rfl base
    let now := first.current.physical.raw
    let extra := InReserve.extra base now
    have positive : 0 < revised.law.duration ((base.addReserve extra).retime now.clock now.round) :=
      (code.duration extra first.current.reserved.extra_nonnegative now.clock now.round).symm ▸ original.positiveClock
    have live := original.after_reserve_and_clock code.timing code.reserve extra
      first.current.reserved.extra_nonnegative now.clock now.round positive
    rwa [← first.current.reserved.exact_raw] at live

private theorem the_removed_word_has_no_registration :
    ¬ Supply.Registered RevisedOrders.dropLocal first.current.physical.raw (personalWord true) := by
  intro registered
  have absent : grow true ∉ originalWord := by decide +kernel
  exact absent (registered (grow true) List.mem_cons_self)

private theorem second_novel : ¬ scope first 1 ⊆ first.base.language.covered := by
  have exposed : exitEffect ∈ scope first 1 := by
    rw [paid_scope first_reads first_ready]
    apply (paidEffects_loss _ _ exitClaim).mpr
    rw [paidLosses_eq]
    exact ⟨the_personal_word_still_pays_on_the_first_successor,
      fun kept => the_removed_word_has_no_registration kept.1⟩
  intro already
  have falseRead := already exposed
  rw [Runtime.coverage_eq, actualNetwork.network.initialLanguage, Set.empty_union] at falseRead
  change exitEffect ∈ scope start 0 at falseRead
  rw [first_scope] at falseRead
  cases Set.mem_singleton_iff.mp falseRead

/-- Both amendments first spend at the actual lower-stock opening.
The second whole-network revision starts at the first generated resident. -/
theorem lower_reserve_generates_two_paid_u8_writes :
    (visit start 0).source.paidWire = some (packet 0).wire ∧
    (visit first 1).source.paidWire = some (packet 1).wire ∧
    (turn start 0).write.isSome = true ∧ (turn first 1).write.isSome = true ∧
    let revision := (Runtime.revision home namedReplies first (submit 1) second_novel).generate
    (⟨revision.NewN, revision.newLivingRoot.generatedNextCurrentAt
      (.finite revision.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      (liveHistory schedule 2).1.current.ledger.resident.erase ∧
    (liveHistory schedule 2).1.current.ledger.stack.balances = actualNetwork.paid.next.ledger.stack.balances := by
  refine ⟨paid_wire initial_reads initial_ready, paid_wire first_reads first_ready,
    (Runtime.write_iff home namedReplies start (submit 0)).mpr first_novel,
    (Runtime.write_iff home namedReplies first (submit 1)).mpr second_novel,
    Runtime.next_reads_generated_first_write home namedReplies first (submit 1) second_novel,
    (Runtime.history_keeps_rows home namedReplies start schedule 2).trans actualNetwork.network.rows⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
