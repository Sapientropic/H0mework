import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

open Evolution.Ingress.Joint.Material

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

def contextFace (n : Nat) : SourceNativeRootSemanticFaceAt
    (Runtime.Inquiry.root seed claim) (Runtime.temporalAt seed claim n) :=
  { projection := .component Runtime.Inquiry.Projection.context,active := PUnit.unit,classifier_eq := rfl }

theorem every_native_root_reads_the_original_enacted_context (n : Nat) :
    (contextFace seed claim n).rootRead = (seed.current.actualLaw,seed.current.members) := rfl

theorem every_actual_native_root_excludes_all_capital (n : Nat) :
    Global.NoCapital (contextFace seed claim n).rootRead.1 := seed.noCapital

theorem joint_payment_and_all_capital_exclusion_have_the_same_actual_root :
    Runtime.RootedJointPaymentAt seed claim ∧
      ∀ n, Global.NoCapital (contextFace seed claim n).rootRead.1 :=
  ⟨Runtime.the_original_root_executes_its_joint_payment_and_complete_native_account seed claim,
    every_actual_native_root_excludes_all_capital seed claim⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
