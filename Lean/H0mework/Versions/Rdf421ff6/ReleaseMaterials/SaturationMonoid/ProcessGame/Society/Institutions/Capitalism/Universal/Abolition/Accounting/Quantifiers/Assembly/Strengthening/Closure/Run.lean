import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure.Ready
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (shape : NativeShape source)

abbrev Resources := Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
  (drainedPosition source shape).native.input (drainedPosition source shape).native.depth
  (drainedPosition source shape).native.count (Clearing.Deployment.history (drainedPosition source shape))
  (Clearing.Deployment.before (drainedPosition source shape))

def sourceBudget : Nat := source.mass + 2 * (Clearing.Deployment.plan (drainedPosition source shape)).length

def actualSteps : Nat := source.drain.1 + 2 * (Clearing.Deployment.plan (drainedPosition source shape)).length

/-- Two actual segments joined at the same current. Installing the generated
clearing query is a source coface, not an extra physical replay or payment. -/
structure CompleteAt (resources : Resources source shape) : Prop where
  original_ready_current : (drainedPosition source shape).native = source.drained
  actual_prelude : source.drained = Evolving.History.currentAt source source.drain.1
  whole_prelude : Evolving.History.ClosedAt source source.drain.1
  original_source_bound : source.drain.1 ≤ source.mass
  total_source_bound : actualSteps source shape ≤ sourceBudget source shape
  actual_clearing : Clearing.Deployment.CompleteAt (drainedPosition source shape) resources

theorem the_original_source_drains_clears_and_resumes_in_its_own_finite_budget
    (resources : Resources source shape) : CompleteAt source shape resources where
  original_ready_current := ready_position_is_the_same_actual_native_current source.drained _ _
  actual_prelude := rfl
  whole_prelude := Evolving.History.the_source_generates_its_whole_ledger_evolving_closure _ _
  original_source_bound := source.drained_has_no_pending_source_work.1
  total_source_bound := Nat.add_le_add_right source.drained_has_no_pending_source_work.1 _
  actual_clearing := Clearing.Deployment.the_original_current_clears_its_entire_native_ledger_and_continues _ resources

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure
