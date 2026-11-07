import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive.Prefixes

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity

open Source.Program Innovation
open Exit.Necessity

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Finite raw recipe tests. Affordability and successful execution are absent. -/
def RecipeFacts (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) : Prop :=
  ∀ item ∈ items, RawLaw.SignerMatches item.request ∧ law.operationAllowed item.before item.request = true ∧
    (∀ port ∈ law.requiredPorts item.before item.request,
      law.allowed item.before.technology port item.request.signer = true ∨
      law.controller item.before.technology port ∈ item.request.consents) ∧
    law.ClaimGuard item.before item.request ∧
    NonnegativeBundle (Party × Good) (law.debit item.before item.request) ∧
    NonnegativeBundle (Party × Good) (law.credit item.before item.request)

instance (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) : Decidable (RecipeFacts law items) := by
  unfold RecipeFacts
  letI : DecidablePred (fun item : ExecutionItem Party Good Port Technology Instrument =>
    RawLaw.SignerMatches item.request ∧ law.operationAllowed item.before item.request = true ∧
    (∀ port ∈ law.requiredPorts item.before item.request,
      law.allowed item.before.technology port item.request.signer = true ∨
      law.controller item.before.technology port ∈ item.request.consents) ∧
    law.ClaimGuard item.before item.request ∧
    NonnegativeBundle (Party × Good) (law.debit item.before item.request) ∧
    NonnegativeBundle (Party × Good) (law.credit item.before item.request)) := fun item => by
      rcases item with ⟨index,before,signer,consents,purpose,gates,operation⟩
      dsimp only
      unfold RawLaw.SignerMatches RawLaw.ClaimGuard
      cases operation with
      | use _ _ purpose => cases purpose <;> infer_instance
      | _ => infer_instance
  infer_instance

/-- The resource test inspects original debit keys, including duplicate lots'
aggregate cost, and the symbolic prefix envelope before any rejection. -/
def Startup (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ item ∈ (Primitive.execute law initial 0 word).items, ∀ entry ∈ law.debit item.before item.request,
    Primitive.requiredStock law initial (Primitive.execute law initial 0 word).items entry.1.1 entry.1.2 ≤
      initial.stock entry.1.1 entry.1.2

instance (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Startup law initial word) := by unfold Startup; infer_instance

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
def Bill (word : RawEvent Party Good Port Technology Instrument) (actor : Party) (goods : Bundle Good) (purpose : Use) : Prop :=
  goods = [] ∨ ∃ request ∈ word, UseMatches request.operation actor goods purpose

instance [DecidableEq Technology] [DecidableEq Port]
    (word : RawEvent Party Good Port Technology Instrument) (actor : Party) (goods : Bundle Good) (purpose : Use) :
    Decidable (Bill word actor goods purpose) := by unfold Bill; infer_instance

def Needs (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (members : List Party)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ actor ∈ members, Bill word actor (law.necessities initial actor) .necessity ∧
    Bill word actor (law.mandatoryMaintenance initial actor) .maintenance

instance [DecidableEq Technology] [DecidableEq Port]
    (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (members : List Party)
    (word : RawEvent Party Good Port Technology Instrument) : Decidable (Needs law initial members word) := by
  unfold Needs; infer_instance

theorem primitive_resources_generate_the_complete_conditions
    (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (recipe : RecipeFacts law (Primitive.execute law initial 0 word).items)
    (startup : Startup law initial word) : Primitive.Conditions law (Primitive.execute law initial 0 word).items := by
  refine ⟨fun item member => (recipe item member).1,fun item member => (recipe item member).2.1,
    fun item member => (recipe item member).2.2.1,fun item member => (recipe item member).2.2.2.1,
    fun item member => (recipe item member).2.2.2.2.1,fun item member => (recipe item member).2.2.2.2.2,?_⟩
  intro item member entry debited
  have bound := Primitive.each_primitive_prefix_requirement_is_in_the_source_envelope
    law initial _ item member entry.1.1 entry.1.2
  have resource := startup item member entry debited
  linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity
