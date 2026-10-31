import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Conservation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Facts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning

open Source.Program Innovation
namespace Primitive
export Priority.Adequacy.Primitive (execute Conditions all_primitive_effects_become_the_same_actual_execution)
end Primitive

noncomputable section

attribute [local irreducible] actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

def primitiveReadings : Allocation.Readings Party Good Port Technology Instrument :=
  ⟨fun item => (actualLaw seed).debit item.before item.request,
    fun item => (actualLaw seed).credit item.before item.request⟩

def primitiveAfter (current : Current seed claim) :=
  Allocation.Kernel.after (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response) (Entitlement.Duty.scope (window seed))
    (primitiveReadings seed) current.productive current.productiveDeclared current.grossDeclared

def primitiveItems (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :=
  (Primitive.execute (actualLaw seed) current.raw 0 word).items

def initialWork (current : Current seed claim) : Allocation.Working Party Good :=
  ⟨fun _ => 0,current.gross,current.gross_nonnegative⟩

def primitiveAnalysis (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :=
  (primitiveItems seed claim current word).foldl (primitiveAfter seed claim current) (initialWork seed claim current)

def grossCredits (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) : ℚ :=
  Allocation.Kernel.grossCharged (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response) (Entitlement.Duty.scope (window seed))
    (primitiveReadings seed) current.productive current.productiveDeclared current.grossDeclared key
    (initialWork seed claim current) (primitiveItems seed claim current word)

theorem primitive_gross_account_is_exact (current : Current seed claim)
    (word : RawEvent Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    (primitiveAnalysis seed claim current word).gross key + grossCredits seed claim current word key = current.gross key :=
  Allocation.Kernel.every_original_cell_has_exact_material_conservation _ _ _ _ _ _ _ _ _ _

private theorem one_actual_step_is_the_same_primitive_allocation (current : Current seed claim)
    (work : Allocation.Working Party Good) (item : ExecutionItem Party Good Port Technology Instrument)
    (valid : (actualLaw seed).Valid item.before item.request) :
    Allocation.afterItem seed current.productive current.productiveDeclared current.grossDeclared work item =
      primitiveAfter seed claim current work item := by
  simp only [Allocation.afterItem,primitiveAfter,Allocation.Kernel.after,Allocation.Kernel.net,
    Allocation.Kernel.productiveCredit,Allocation.Kernel.gross,Allocation.Kernel.reservation,Allocation.Kernel.incoming,
    Allocation.actualReadings,primitiveReadings,RawLaw.actualDebit,RawLaw.actualCredit,if_pos valid]

theorem primitive_resources_generate_the_same_single_actual_allocation (current : Current seed claim)
    (word : RawEvent Party Good Port Technology Instrument)
    (conditions : Primitive.Conditions (actualLaw seed) (primitiveItems seed claim current word)) :
    Current.analysis seed claim current word = primitiveAnalysis seed claim current word := by
  have execution := Primitive.all_primitive_effects_become_the_same_actual_execution
    (actualLaw seed) current.raw 0 word conditions
  unfold Current.analysis Allocation.run RawLaw.rawItems primitiveAnalysis primitiveItems
  rw [execution]
  have same (items : List (ExecutionItem Party Good Port Technology Instrument))
      (valid : ∀ item ∈ items, (actualLaw seed).Valid item.before item.request)
      (work : Allocation.Working Party Good) :
      items.foldl (Allocation.afterItem seed current.productive current.productiveDeclared current.grossDeclared) work =
        items.foldl (primitiveAfter seed claim current) work := by
    induction items generalizing work with
    | nil => rfl
    | cons item tail inherited =>
        simp only [List.foldl_cons]
        rw [one_actual_step_is_the_same_primitive_allocation seed claim current work item (valid item List.mem_cons_self)]
        exact inherited (fun next member => valid next (List.mem_cons_of_mem _ member)) _
  exact same _ conditions.actual_validity_is_generated _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning
