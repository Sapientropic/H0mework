import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Preparation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Inherited
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Actual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Payment.Actual

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Bindings

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

abbrev Account := (Epoch.Finance.process input 0 count).GeneratedState
abbrev Claim := Epoch.Finance.NewClaim input 0 count
abbrev Item := Epoch.Finance.ActualItem input 0 count
abbrev base := Epoch.Finance.Future.Installed.initial input 0 count 0 count

def beforePayments (version : Nat) :=
  submittedInputs (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past
    (Control.Scenario.discovery version) ++ [.primitive (riskLiability version),.execute Control.Scenario.commonWork]

theorem the_actual_work_cut_generates_its_two_original_native_claims
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    ∃ loan risk : Claim,
      loan.instrument = () ∧ loan.debtor = 0 ∧ loan.holder = 1 ∧ loan.quantity = 3 ∧
      risk.instrument = () ∧ risk.debtor = Preparation.riskDebtor version ∧
        risk.holder = Preparation.riskHolder version ∧ risk.quantity = Preparation.riskUnits version ∧
      (actualPublicVisit (Control.Scenario.discovery version) 9).account.current.slots =
        [.live Inherited.originalOwner,
         .live (Epoch.Finance.admission input 0 count (.inr loan)).toObligation,
         .live (Epoch.Finance.admission input 0 count (.inr risk)).toObligation] := by
  let nature := Control.Scenario.discovery version
  let actualOrigin := firstOrigin nature
  have contextReflexive : actualOrigin = actualOrigin := rfl
  generalize contextEq : actualOrigin = origin at contextReflexive
  let oldPast := actualOrigin.germ.snapshot.past
  have seedReflexive : (base : Account) = base := rfl
  generalize seedEq : (base : Account) = seed at seedReflexive
  have snapshot : (actualPublicVisit nature 9).snapshot = Physical.Prefix.cursor (beforePayments version) :=
    the_original_actual_trial_executes_its_real_all_member_work version tested
  have original := every_actual_public_visit_is_its_original_source_account nature 9
  have seeded := congrArg (fun account : Account => Epoch.Finance.PublicPast.account input 0 count 0 0 oldPast
    (actualPublicVisit nature 9).snapshot.past account) seedEq
  have source := congrArg (fun cursor : CursorAt => Epoch.Finance.PublicPast.account input 0 count 0 0 oldPast cursor.past seed) snapshot
  have literal := congrArg (fun past : List InputAt => Epoch.Finance.PublicPast.account input 0 count 0 0 oldPast past seed)
    (Physical.Prefix.past_readback (beforePayments version))
  let sourceAt (context : Functions.Revision.Context (input := input) (review := none) 0 count 0 0 0 count) :=
    Epoch.Finance.PublicPast.account input 0 count 0 0 context.germ.snapshot.past
      (submittedInputs context.germ.snapshot.past nature ++
        [.primitive (riskLiability version),.execute Control.Scenario.commonWork]) seed
  have transported : sourceAt actualOrigin = sourceAt origin := congrArg sourceAt contextEq
  obtain ⟨loan,risk,loanInstrument,loanDebtor,loanHolder,loanQuantity,
    riskInstrument,riskDebtor,riskHolder,riskQuantity,generated⟩ :=
      Preparation.the_original_preparation_generates_its_two_exact_native_claims origin version seed
  have account : (actualPublicVisit nature 9).account =
      (seed.step (Epoch.Finance.process input 0 count) (.admit (.inr loan))).step
        (Epoch.Finance.process input 0 count) (.admit (.inr risk)) :=
    original.trans (seeded.trans (source.trans (literal.trans (transported.trans generated))))
  refine ⟨loan,risk,loanInstrument,loanDebtor,loanHolder,loanQuantity,
    riskInstrument,riskDebtor,riskHolder,riskQuantity,?_⟩
  have slots := congrArg (fun account : Account => account.current.slots) account
  have seedSlots : seed.current.slots = [.live Inherited.originalOwner] :=
    (congrArg (fun account : Account => account.current.slots) seedEq).symm.trans
      (the_original_macro_base_slots_are_the_same_pure_source_financial_cursor.trans
        Inherited.the_original_inherited_slot_is_the_same_live_owner_debt)
  exact slots.trans (by
    change (seed.current.slots ++ [.live (Epoch.Finance.admission input 0 count (.inr loan)).toObligation]) ++
      [.live (Epoch.Finance.admission input 0 count (.inr risk)).toObligation] = _
    rw [seedSlots]
    rfl)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Bindings
