import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Effects
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {base : WorldRelationNetwork.{0}} {anchor : (Epoch.Finance.process input depth count).GeneratedState}

private def fixedFamily (baseFamily : Epoch.Finance.Future.Continuation.AccountFamily input depth count base anchor)
    (law : DebtActivationLaw.{0}) (state : law.DebtState) (identity : law.TransportAt state state) :
    Epoch.Finance.Future.Continuation.AccountFamily input depth count (ExtendedNetwork base law) anchor where
  support := fun account tail => ⟨baseFamily.support account tail,some state⟩
  owner := fun account tail => oldEntry (baseFamily.owner account tail)
  itemEvolution := fun account tail item => Financial.Installation.wholeTransport
    (baseFamily.itemEvolution account tail item) (baseFamily.owner account tail) identity
  item_keys := fun account tail item => Financial.Installation.wholeTransport_keeps_keys _ _ _
    (baseFamily.item_keys account tail item)
  entries_finite := fun account tail => Epoch.Finance.Future.Finiteness.active_finite _ (baseFamily.entries_finite account tail)
  open_fibres := Epoch.Finance.Future.Structure.extended_subsingleton _ baseFamily.open_fibres
  entry := fun support => oldEntry (state? := support.2) (baseFamily.entry support.1)
  entry_key := fun left right => congrArg Sum.inl (baseFamily.entry_key left.1 right.1)
  disposition := fun support kind => match kind with
    | .supportSettlement => by
        change (match law.supportTerminalLaw? with
          | none => base.DispositionAt support.1 .supportSettlement
          | some terminal => base.DispositionAt support.1 .supportSettlement ⊕ ActiveAt law support.2 terminal.EventAt)
        cases terminal : law.supportTerminalLaw? with
        | none => exact baseFamily.disposition support.1 .supportSettlement
        | some terminal => exact .inl (baseFamily.disposition support.1 .supportSettlement)
    | .transfer => .inl (baseFamily.disposition support.1 .transfer)
    | .lawSurfaceExtension => .inl (baseFamily.disposition support.1 .lawSurfaceExtension)

variable [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def paidState := Planning.actualNext seed claim (Material.shared seed claim)

def family (_enough : Planning.Enough seed claim (Material.shared seed claim)) :
    Epoch.Finance.Future.Continuation.AccountFamily seed.input seed.depth seed.count
      (Admission.N seed claim) (Background.nativeAccount seed) :=
  fixedFamily (fixedFamily (Background.family seed) (Productive.law seed claim) (.current (paidState seed claim))
    (Productive.Transport.identity (.current (paidState seed claim))))
    (Gross.law seed claim) (paidState seed claim) (Gross.Carry.identity (paidState seed claim))

theorem the_resumption_family_retains_the_actual_original_account
    (enough : Planning.Enough seed claim (Material.shared seed claim)) :
    (family seed claim enough).initial = Background.nativeAccount seed := rfl

theorem the_fixed_historical_rows_have_no_remaining_budget
    (enough : Planning.Enough seed claim (Material.shared seed claim)) :
    (Productive.law seed claim).budget (.current (paidState seed claim)) = 0 ∧
      (Gross.law seed claim).budget (paidState seed claim) = 0 := by
  have actual := Planning.sufficient_source_resources_force_the_actual_shared_payment seed claim _ enough
  have productiveDeclared : (paidState seed claim).productiveDeclared = true := seed.declared
  have grossDeclared : (paidState seed claim).grossDeclared = true := rfl
  exact ⟨(Productive.law seed claim).settlement_budget_zero ⟨productiveDeclared,actual.productivePaid⟩,
    (Gross.law seed claim).settlement_budget_zero ⟨grossDeclared,actual.grossPaid⟩⟩

theorem each_financial_item_keeps_the_same_paid_historical_snapshots
    (enough : Planning.Enough seed claim (Material.shared seed claim))
    (account : (Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState)
    (tail : Epoch.Finance.Future.Continuation.NativeTail seed.input seed.depth seed.count
      (Background.nativeAccount seed) account) :
    ((family seed claim enough).support account tail).1.2 = some (.current (paidState seed claim)) ∧
      ((family seed claim enough).support account tail).2 = some (paidState seed claim) := ⟨rfl,rfl⟩

theorem family_support_is_the_literal_paid_extension
    (enough : Planning.Enough seed claim (Material.shared seed claim))
    (account : (Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState)
    (tail : Epoch.Finance.Future.Continuation.NativeTail seed.input seed.depth seed.count
      (Background.nativeAccount seed) account) :
    (family seed claim enough).support account tail =
      Material.support seed claim ((Background.family seed).support account tail) (paidState seed claim) := rfl

theorem family_items_are_the_same_original_finance_and_paid_row_transports
    (enough : Planning.Enough seed claim (Material.shared seed claim))
    (account : (Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState)
    (tail : Epoch.Finance.Future.Continuation.NativeTail seed.input seed.depth seed.count
      (Background.nativeAccount seed) account)
    (item : Epoch.Finance.ActualItem seed.input seed.depth seed.count) :
    (family seed claim enough).itemEvolution account tail item =
      Material.identityTransport seed claim ((Background.family seed).itemEvolution account tail item)
        ((Background.family seed).owner account tail) (paidState seed claim) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
