import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

def execution (current : Cursor Party Good Port Technology Instrument) :=
  Compile.execution input depth count prefixLimit renewalLimit
    (stateAt input depth count prefixLimit renewalLimit current.past) current.incoming

def body (current : Cursor Party Good Port Technology Instrument) :
    Source.ProgrammeFace.Origin Party Good Port Technology Instrument :=
  ⟨(stateAt input depth count prefixLimit renewalLimit current.past).raw,
    (execution input depth count prefixLimit renewalLimit current).items.map ExecutionItem.request⟩

theorem body_is_the_same_actual_inventory (current : Cursor Party Good Port Technology Instrument) :
    input.law.rawItems (body input depth count prefixLimit renewalLimit current).1
        (body input depth count prefixLimit renewalLimit current).2 =
      (execution input depth count prefixLimit renewalLimit current).items := by
  dsimp only [body, execution, Compile.execution, Compile.Result.execution]
  rw [RawLaw.inventory_requests_exact]
  rfl

theorem whole_material_balance (current : Cursor Party Good Port Technology Instrument) (person : Party) (good : Good) :
    (stateAt input depth count prefixLimit renewalLimit (next current).past).raw.stock person good +
        input.law.totalDebit (execution input depth count prefixLimit renewalLimit current).items person good =
      (stateAt input depth count prefixLimit renewalLimit current.past).raw.stock person good +
        input.law.totalCredit (execution input depth count prefixLimit renewalLimit current).items person good := by
  rw [consumed_input_generates_its_own_after]
  exact Compile.Result.whole_material_balance input depth count prefixLimit renewalLimit _ _ person good

theorem refusal_keeps_the_original_physical_current (current : Cursor Party Good Port Technology Instrument)
    (reason : Compile.RefusalAt input depth count prefixLimit renewalLimit
      (stateAt input depth count prefixLimit renewalLimit current.past) current.incoming)
    (produced : resultAt input depth count prefixLimit renewalLimit current = .refused reason) :
    stateAt input depth count prefixLimit renewalLimit (next current).past =
      stateAt input depth count prefixLimit renewalLimit current.past := by
  rw [consumed_input_generates_its_own_after]
  change (resultAt input depth count prefixLimit renewalLimit current).next input depth count prefixLimit renewalLimit _ = _
  rw [produced]
  rfl

#print axioms consumed_input_generates_its_own_after
#print axioms body_is_the_same_actual_inventory
#print axioms whole_material_balance
#print axioms refusal_keeps_the_original_physical_current

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical
