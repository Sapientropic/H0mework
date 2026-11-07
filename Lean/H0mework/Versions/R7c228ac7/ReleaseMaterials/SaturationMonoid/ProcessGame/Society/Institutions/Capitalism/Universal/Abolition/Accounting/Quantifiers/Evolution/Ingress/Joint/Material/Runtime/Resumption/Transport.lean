import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Authority
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.NativeFrame
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Tactics
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Elimination
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Cast

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

attribute [local irreducible] Planning.selected Planning.actualNext Current.advance Execution.Selected.items Runtime.cursor

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))

theorem the_actual_paid_destination_is_the_literal_native_financial_destination
    (actual : FinancialCurrent seed) (paid : actual.bodyPaid = true) :
    HEq (Runtime.evolution seed claim actual).destination
      (Public.Accounting.nativeEvolution seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)
        (family seed claim enough) actual).destination := by
  let original := actual
  rcases actual with ⟨progress⟩
  cases progress with
  | none => cases paid
  | some financial =>
      cases head : Public.Accounting.item? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) original with
      | none =>
          dsimp only [original] at head
          simp [Runtime.evolution,Runtime.withKeys,Public.Accounting.nativeEvolution,
            Public.Accounting.nativeEvolutionWithKeys,Public.Accounting.Current.bodyPaid,head,
            Runtime.next,Public.Accounting.next,Public.Accounting.nativeNext,Runtime.sharedAt,Runtime.support,
            Public.Accounting.support,family_support_is_the_literal_paid_extension,paidState]
          simp only [option_with_equation_none _ _ _ head]
          simp only [rec_with_equation _ _ _ _ head]
          joint_paid_peel_rhs
          refine HEq.trans (keyed_destination_cast_heq ?_ _ _) ?_
          · simp [head]
          · rfl
      | some item =>
          dsimp only [original] at head
          have originalItem : item ∈ Public.Accounting.items seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) :=
            List.mem_of_getElem? (by simpa [Public.Accounting.item?,Public.Accounting.Current.bodyPaid] using head)
          have absent := Drain.no_original_position_requests_another_loan seed claim item originalItem
          simp [Runtime.evolution,Runtime.withKeys,Public.Accounting.nativeEvolution,
            Public.Accounting.nativeEvolutionWithKeys,Public.Accounting.Current.bodyPaid,head,
            Runtime.baseEvolution,Runtime.baseOwner,Public.Accounting.wholeEvolution,
            Public.Accounting.evolutionWithKeys,absent,family_items_are_the_same_original_finance_and_paid_row_transports,
            Runtime.next,Public.Accounting.next,Public.Accounting.nativeNext,Runtime.sharedAt,Runtime.support,
            Public.Accounting.support,family_support_is_the_literal_paid_extension,paidState,
            Public.Accounting.Current.afterItem]
          simp only [option_with_equation_some _ _ _ item head]
          simp only [rec_with_equation _ _ _ _ head,option_with_equation_none _ _ _ absent,
            ]
          joint_paid_peel_rhs
          refine HEq.trans (keyed_destination_cast_heq ?_ _ _) ?_
          · simp [head,absent]
          · joint_paid_peel_lhs_wrapped
            joint_paid_peel_lhs_wrapped
            rfl


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
