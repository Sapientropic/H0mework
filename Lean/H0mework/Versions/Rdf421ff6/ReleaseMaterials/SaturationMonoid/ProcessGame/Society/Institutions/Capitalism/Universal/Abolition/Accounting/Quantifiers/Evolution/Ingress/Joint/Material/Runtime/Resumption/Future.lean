import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Completed
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

attribute [local irreducible] Execution.Selected.items Planning.selected Planning.actualNext Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))

local notation "F" => nativeFrame seed claim enough
local notation "visit" => completedVisit seed claim
local notation "actual" => completedActual seed claim enough
local notation "authority" => completedAuthority seed claim enough

def resumptionPresentation (reader : Macro.Raw.Reader seed.input seed.depth seed.count) :=
  Factory.Resumption.Action.presentation F visit actual authority reader

def nextActual (reader : Macro.Raw.Reader seed.input seed.depth seed.count) :=
  Factory.Resumption.Action.nextActual F visit actual authority reader

theorem source_resumption_keeps_the_same_completed_account_and_original_pending_work
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count) :
    (nextActual seed claim enough reader).actual = (actual).actual ∧
      (nextActual seed claim enough reader).actual.account = (actual).actual.account ∧
      Public.Accounting.registration? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)
        (nextActual seed claim enough reader).actual =
      Public.Accounting.registration? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) (actual).actual :=
  ⟨rfl,rfl,rfl⟩

variable {sourceDepth sourceCount : Nat} {review : Option (ReviewPhase.ContextAt seed.input)}
  (origin : Abolition.Functions.Revision.Context (input := seed.input) (review := review)
    seed.depth seed.count 0 0 sourceDepth sourceCount)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
  (reader : Macro.Raw.Reader seed.input seed.depth seed.count)

def nextInquiry := Factory.Resumption.Action.nativeInquiry F visit actual authority reader origin admission

theorem the_actual_joint_root_returns_the_original_dynamic_native_inquiry :
    (RootInquiryProcessNode.answered (resumptionPresentation seed claim enough reader) PUnit.unit).erase =
      (nextInquiry seed claim enough origin admission reader).erase :=
  Factory.Resumption.Action.actual_process_resumes_with_the_original_native_query F visit actual authority reader origin admission

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
