import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu.Routing
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Inspection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution.Inspection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)

inductive Failures : List (RawEvent Party Good Port Technology Instrument) → Type
  | nil : Failures []
  | cons {word : RawEvent Party Good Port Technology Instrument} {rest : List (RawEvent Party Good Port Technology Instrument)}
      (first : ResourceIssue seed claim current word) (later : Failures rest) : Failures (word :: rest)

inductive SelectionFrom (available : List (RawEvent Party Good Port Technology Instrument)) : Type
  | ready (word : RawEvent Party Good Port Technology Instrument) (original : word ∈ available)
      (resources : Resources seed claim current word)
  | blocked (issues : Failures seed claim current available)

def selectFrom : (available : List (RawEvent Party Good Port Technology Instrument)) → SelectionFrom seed claim current available
  | [] => .blocked .nil
  | word :: rest =>
      match inspectResources seed claim current word with
      | .ready resources => .ready word List.mem_cons_self resources
      | .blocked issue =>
          match selectFrom rest with
          | .ready next original resources => .ready next (List.mem_cons_of_mem _ original) resources
          | .blocked issues => .blocked (.cons issue issues)

def selection := selectFrom seed claim current (Menu.plans seed claim current)

def chosen : RawEvent Party Good Port Technology Instrument :=
  match selection seed claim current with
  | .ready word _ _ => word
  | .blocked _ => (Menu.plans seed claim current).headD (Menu.needsWord seed claim current ++ Menu.settlements seed)

def selected := Entitlement.Execution.payable (actualLaw seed) current.raw (chosen seed claim current)

def actualInspection := Entitlement.Execution.inspectWord (actualLaw seed) current.raw (chosen seed claim current)

def actualNext := Current.advance seed claim current (selected seed claim current)

def Enough : Prop := ∃ word ∈ Menu.plans seed claim current, Resources seed claim current word

omit [DecidableEq Technology] in
theorem failure_inventory_retains_each_original_plan
    {available : List (RawEvent Party Good Port Technology Instrument)}
    (issues : Failures seed claim current available) :
    ∀ word ∈ available, ¬ Resources seed claim current word := by
  induction issues with
  | nil => intro word original; cases original
  | @cons word rest first later inherited =>
      intro next original resources
      rcases List.mem_cons.mp original with same | inside
      · cases same
        exact blocked_resources_expose_the_same_original_source_obligation seed claim current _ first resources
      · exact inherited next inside resources

theorem sufficient_source_resources_are_selected (enough : Enough seed claim current) :
    Resources seed claim current (chosen seed claim current) := by
  unfold chosen
  cases selected : selection seed claim current with
  | ready word original resources => exact resources
  | blocked issues =>
      obtain ⟨word,original,resources⟩ := enough
      exact (failure_inventory_retains_each_original_plan seed claim current issues word original resources).elim

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem all_original_items_give_validity (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (index : Nat)
    (word : RawEvent Party Good Port Technology Instrument)
    (valid : ∀ item ∈ (law.execute before index word).items, law.Valid item.before item.request) :
    Entitlement.Execution.ValidAt law before word := by
  induction word generalizing before index with
  | nil => trivial
  | cons request rest inherited =>
      exact ⟨valid ⟨index,before,request⟩ List.mem_cons_self,
        inherited (law.step before request) (index + 1) (fun item original => valid item (List.mem_cons_of_mem _ original))⟩

theorem sufficient_source_resources_execute_the_whole_selected_programme (enough : Enough seed claim current) :
    selected seed claim current = chosen seed claim current := by
  have success := primitive_resources_generate_one_actual_payment_of_both_original_obligations seed claim current
    (chosen seed claim current) (sufficient_source_resources_are_selected seed claim current enough)
  exact Entitlement.Execution.a_fully_funded_original_word_is_selected_whole _ _ _
    (all_original_items_give_validity _ _ 0 _ success.originalAccepted)

theorem sufficient_source_resources_force_the_actual_shared_payment (enough : Enough seed claim current) :
    ActualSuccess seed claim current (selected seed claim current) := by
  rw [sufficient_source_resources_execute_the_whole_selected_programme seed claim current enough]
  exact primitive_resources_generate_one_actual_payment_of_both_original_obligations seed claim current _
    (sufficient_source_resources_are_selected seed claim current enough)

theorem the_selected_next_is_the_one_original_live_material_next :
    (actualNext seed claim current).raw = (actualLaw seed).next current.raw (selected seed claim current) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning
