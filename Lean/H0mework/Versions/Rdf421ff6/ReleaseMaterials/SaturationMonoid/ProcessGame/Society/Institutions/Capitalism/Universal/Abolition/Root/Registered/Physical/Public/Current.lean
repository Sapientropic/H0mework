import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Result

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))

/-- The old consumed cut is interpreted once by its original law. Only
subsequent actual syntax is read under the generated public interpreter. -/
def stateAt (past : List (Compile.RawInput Party Good Port Technology Instrument)) : Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  past.foldl (fun before raw => (compile input before raw).next)
    (Physical.stateAt input depth count prefixLimit renewalLimit oldPast)

def resultAt (current : Physical.Cursor Party Good Port Technology Instrument) :=
  compile input (stateAt input depth count prefixLimit renewalLimit oldPast current.past) current.incoming

def execution (current : Physical.Cursor Party Good Port Technology Instrument) :=
  (resultAt input depth count prefixLimit renewalLimit oldPast current).execution

def body (current : Physical.Cursor Party Good Port Technology Instrument) : Source.ProgrammeFace.Origin Party Good Port Technology Instrument :=
  ⟨(stateAt input depth count prefixLimit renewalLimit oldPast current.past).raw,
    (execution input depth count prefixLimit renewalLimit oldPast current).items.map ExecutionItem.request⟩

theorem the_new_epoch_starts_at_the_literal_original_current :
    stateAt input depth count prefixLimit renewalLimit oldPast [] =
      Physical.stateAt input depth count prefixLimit renewalLimit oldPast := rfl

theorem consumed_input_generates_its_own_after (current : Physical.Cursor Party Good Port Technology Instrument) :
    stateAt input depth count prefixLimit renewalLimit oldPast (Physical.next current).past =
      (resultAt input depth count prefixLimit renewalLimit oldPast current).next := by
  simp only [stateAt, Physical.next, List.foldl_append, List.foldl_cons, List.foldl_nil, resultAt]

theorem body_is_the_same_actual_inventory (current : Physical.Cursor Party Good Port Technology Instrument) :
    (interpreter input).rawItems (body input depth count prefixLimit renewalLimit oldPast current).1
      (body input depth count prefixLimit renewalLimit oldPast current).2 =
      (execution input depth count prefixLimit renewalLimit oldPast current).items := by
  cases produced : resultAt input depth count prefixLimit renewalLimit oldPast current with
  | accepted word selected checked =>
      simp only [body, execution, produced, ResultAt.execution]
      rw [RawLaw.inventory_requests_exact]
      rfl
  | refused word selected item listed failed =>
      simp only [body, execution, produced, ResultAt.execution, List.map_nil, RawLaw.rawItems, RawLaw.execute]
  | metadata selected =>
      simp only [body, execution, produced, ResultAt.execution, List.map_nil, RawLaw.rawItems, RawLaw.execute]

#print axioms the_new_epoch_starts_at_the_literal_original_current
#print axioms consumed_input_generates_its_own_after
#print axioms body_is_the_same_actual_inventory

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public
