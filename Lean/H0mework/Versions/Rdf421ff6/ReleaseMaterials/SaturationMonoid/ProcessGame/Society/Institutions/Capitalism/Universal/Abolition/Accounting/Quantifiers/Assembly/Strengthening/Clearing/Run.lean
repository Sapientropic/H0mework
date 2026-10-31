import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Schedule
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Schedule

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count boundary : Nat}
  {plan : RawEvent Party Good Port Technology Instrument} {fallback : Macro.Raw.Reader input depth count}

def run : (remaining : RawEvent Party Good Port Technology Instrument) →
    Schedule input depth count boundary plan fallback remaining → Position input depth count (reader boundary plan fallback)
  | [], source => source.position
  | _ :: tail, source => run tail source.next

theorem run_keeps_the_same_actual_original_native_fold
    (remaining : RawEvent Party Good Port Technology Instrument)
    (source : Schedule input depth count boundary plan fallback remaining) :
    (run remaining source).actual.actual.account =
      Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.accountAfter input depth count
        source.position.past remaining source.position.actual.actual.account := by
  induction remaining with
  | nil => rfl
  | cons request tail ih =>
      change (run tail source.next).actual.actual.account = _
      rw [ih source.next]
      change Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.accountAfter input depth count
        source.nextPosition.past tail source.nextPosition.actual.actual.account = _
      unfold nextPosition
      rw [Position.step_records_exactly_this_original_primitive,Position.step_consumes_the_same_original_native_inventory]
      rfl

theorem run_keeps_the_same_actual_submitted_past
    (remaining : RawEvent Party Good Port Technology Instrument)
    (source : Schedule input depth count boundary plan fallback remaining) :
    (run remaining source).past = source.position.past ++
      Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.submitted remaining := by
  induction remaining with
  | nil => simp only [run,Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.submitted,List.map_nil,List.append_nil]
  | cons request tail ih =>
      change (run tail source.next).past = _
      rw [ih source.next]
      change source.nextPosition.past ++ _ = _
      unfold nextPosition
      rw [Position.step_records_exactly_this_original_primitive]
      simp only [Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.submitted,List.map_cons,List.append_assoc,List.singleton_append]

private theorem currentAt_two_steps (current : Evolving.NativeCurrent
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (n : Nat) :
    Evolving.History.currentAt current.advance.advance n = Evolving.History.currentAt current (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Evolving.NativeCurrent.advance ih

theorem run_is_the_same_finite_actual_root_history
    (remaining : RawEvent Party Good Port Technology Instrument)
    (source : Schedule input depth count boundary plan fallback remaining)
    (payments : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.PaymentWord remaining) :
    (run remaining source).native = Evolving.History.currentAt source.position.native (2 * remaining.length) := by
  induction remaining with
  | nil => rfl
  | cons request tail ih =>
      obtain ⟨instrument,debtor,holder,quantity,operation,_⟩ := payments request List.mem_cons_self
      change (run tail source.next).native = _
      rw [ih source.next (fun item member => payments item (List.mem_cons_of_mem _ member))]
      change Evolving.History.currentAt source.nextPosition.native (2 * tail.length) = _
      unfold nextPosition
      rw [Position.step_of_a_payment_is_two_actual_source_advances _ _ _ _ _ instrument debtor holder quantity operation,
        currentAt_two_steps]
      congr 1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Schedule
