import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.Checks
import Mathlib.Algebra.BigOperators.Group.List.Defs
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.SourceFamily
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Discovery

/-! Self-supply derives absence of a local capital relation from actual
operations.  Original material routes cannot move to a different party;
required private exclusion therefore contradicts the paid access itself. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction

open Source.Program Source.ProgrammeControl

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem self_supply_has_no_other_party_flow (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) (party : Party) (good : Good) (different : party ≠ item.request.signer) :
    flowAt (law.actualDebit item.before item.request) party good = 0 ∧
      flowAt (law.actualCredit item.before item.request) party good = 0 := by
  have kind := self.1
  have accepted := self.2.2.1
  cases operation : item.request.operation with
  | produce operator =>
      simp only [SelfOperation, operation] at kind
      rw [kind] at different
      simp [RawLaw.actualDebit, RawLaw.actualCredit, accepted, RawLaw.debit, RawLaw.credit,
        operation, flowAt, locate, amount, List.map_map, Function.comp_def, Prod.mk.injEq,
        different, Ne.symm, List.sum_replicate]
  | use bearer goods purpose =>
      simp only [SelfOperation, operation] at kind
      rw [kind.1] at different
      simp [RawLaw.actualDebit, RawLaw.actualCredit, accepted, RawLaw.debit, RawLaw.credit,
        operation, flowAt, locate, amount, List.map_map, Function.comp_def, Prod.mk.injEq,
        different, Ne.symm, List.sum_replicate]
  | _ => simp only [SelfOperation, operation] at kind

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem positive_self_debit_is_signer (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) (party : Party) (good : Good)
    (positive : 0 < flowAt (law.actualDebit item.before item.request) party good) :
    party = item.request.signer := by
  by_contra different
  rw [(self_supply_has_no_other_party_flow law item self party good different).1] at positive
  exact (lt_irrefl 0 positive)

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem positive_self_credit_is_signer (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) (party : Party) (good : Good)
    (positive : 0 < flowAt (law.actualCredit item.before item.request) party good) :
    party = item.request.signer := by
  by_contra different
  rw [(self_supply_has_no_other_party_flow law item self party good different).2] at positive
  exact (lt_irrefl 0 positive)

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem self_credit_member_is_signer (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) (lot : (Party × Good) × ℚ)
    (member : lot ∈ law.actualCredit item.before item.request) : lot.1.1 = item.request.signer := by
  have kind := self.1
  have accepted := self.2.2.1
  cases operation : item.request.operation with
  | produce operator =>
      simp only [SelfOperation, operation] at kind
      simp only [RawLaw.actualCredit, if_pos accepted, RawLaw.credit, operation, locate] at member
      obtain ⟨piece, _present, same⟩ := List.mem_map.mp member
      exact (congrArg (fun value : (Party × Good) × ℚ => value.1.1) same).symm.trans kind.symm
  | use bearer goods purpose =>
      simp only [RawLaw.actualCredit, if_pos accepted, RawLaw.credit, operation, List.not_mem_nil] at member
  | _ => simp only [SelfOperation, operation] at kind

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem self_required_port_is_allowed (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) (port : Port)
    (required : port ∈ law.requiredPorts item.before item.request) :
    law.allowed item.before.technology port item.request.signer = true := by
  rcases self.2.2.1.2.1 port required with allowed | consent
  · exact allowed
  · rw [self.2.1] at consent
    exact (List.not_mem_nil consent).elim

variable (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (allSelf : ∀ item ∈ law.rawItems current word, At law item)

include allSelf

omit [DecidableEq Port] in
theorem self_supply_route_preserves_party (origin target : Party × Good) (lower upper : Nat)
    (route : List (RouteLeg law current word))
    (follows : Follows law current word origin lower route target upper) : origin.1 = target.1 := by
  induction route generalizing origin lower with
  | nil => exact congrArg Prod.fst follows.1
  | cons leg tail ih =>
      have self := allSelf leg.item.val leg.item.property
      have debit := positive_self_debit_is_signer law leg.item.val self origin.1 origin.2 follows.2.2.1
      have credit := positive_self_credit_is_signer law leg.item.val self
        leg.destination.1 leg.destination.2 follows.2.2.2.1
      exact debit.trans (credit.symm.trans (ih leg.destination (leg.item.val.index + 1) follows.2.2.2.2))

omit [DecidableEq Port] in
theorem self_supply_excludes_checked_access (proposal : Kernel.AccessProposal law current word) :
    ¬ proposal.Checks law current word := by
  intro checked
  have self := allSelf proposal.access.val proposal.access.property
  have allowed := self_required_port_is_allowed law proposal.access.val self proposal.port checked.2.1
  have accessed := checked.2.2.2.2.1
  have sameRecipient : proposal.recipient = proposal.access.val.request.signer := by
    cases mode : proposal.mode with
    | acquired =>
        simp only [Kernel.AccessProposal.Accessed, mode] at accessed
        have holder := positive_self_credit_is_signer law proposal.access.val self
          proposal.accessHolder proposal.accessGood accessed.1
        have route := self_supply_route_preserves_party law current word allSelf
          (proposal.accessHolder, proposal.accessGood) (proposal.recipient, proposal.necessityGood)
          (proposal.access.val.index + 1) proposal.necessity.val.index proposal.delivery accessed.2
        exact route.symm.trans holder
    | used =>
        simp only [Kernel.AccessProposal.Accessed, mode] at accessed
        exact positive_self_debit_is_signer law proposal.access.val self proposal.recipient
          proposal.necessityGood accessed.2.2.2.2
  have denied := checked.2.2.1.2
  rw [sameRecipient] at denied
  exact Bool.noConfusion (allowed.symm.trans denied)

omit [DecidableEq Port] in
theorem self_supply_has_no_capital_kernel : ¬ Nonempty (Kernel.CapitalRelationKernel law current word) := by
  rintro ⟨kernel⟩
  exact self_supply_excludes_checked_access law current word allSelf kernel.proposal.access kernel.checked.1

theorem self_supply_title_family_empty
    (localAttempts : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (item : OriginalItem law current word) :
    Kernel.AssetAuthority.generatedFamily law current word localAttempts item = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro port member
  obtain ⟨capital, _source, _port, _phase⟩ :=
    Kernel.AssetAuthority.generatedFamily_original_provenance law current word localAttempts item port member
  exact self_supply_has_no_capital_kernel law current word allSelf ⟨capital.dependency⟩

theorem self_supply_actual_surplus_family_empty (item : OriginalItem law current word) :
    Kernel.ActualSurplus.familyAt law current word item = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro port member
  obtain ⟨capital, _source, _port, _phase⟩ :=
    Kernel.ActualSurplus.familyAt_has_original_witness law current word item port member
  exact self_supply_has_no_capital_kernel law current word allSelf ⟨capital.dependency⟩

#print axioms self_supply_route_preserves_party
#print axioms self_supply_has_no_capital_kernel
#print axioms self_supply_title_family_empty
#print axioms self_supply_actual_surplus_family_empty

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction
