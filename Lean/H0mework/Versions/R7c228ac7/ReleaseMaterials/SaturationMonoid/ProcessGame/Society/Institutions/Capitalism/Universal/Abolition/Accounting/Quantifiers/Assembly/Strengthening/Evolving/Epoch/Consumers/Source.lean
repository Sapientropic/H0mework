import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Snapshot
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.Execution

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
open Quantifiers.Joint.Consumers.Compact (seed grossClaim the_source_generates_its_own_sufficient_plan)

noncomputable section
attribute [local irreducible] Evolution.Ingress.Joint.Execution.Selected.items Evolution.Ingress.Joint.Execution.Selected.after
  Quantifiers.Joint.Planning.selected Quantifiers.Joint.Planning.actualNext

def repair : Request Bool Bool Bool Unit Unit := ⟨true,[],false,[],.transfer true false [(true,1)]⟩
def repairOther : Request Bool Bool Bool Unit Unit := ⟨true,[],false,[],.transfer true true [(true,1)]⟩
def submission : Actual.Submission Bool Bool Bool Unit Unit := ⟨[repair,repairOther]⟩
def base := Evolving.Source.initial seed grossClaim the_source_generates_its_own_sufficient_plan (fun _ _ => .advance)
def cutLength := base.actual.readerCursor.past.length

def reader : Macro.Raw.Reader seed.input seed.depth seed.count :=
  fun cursor _ => if cursor.past.length = cutLength then .code submission else .advance

def original := Evolving.Source.initial seed grossClaim the_source_generates_its_own_sufficient_plan reader
def current := Source.initial original

theorem original_complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual :=
  Evolving.Source.initial_has_no_pending_native_work seed grossClaim the_source_generates_its_own_sufficient_plan reader

theorem the_original_source_submits_code_at_this_actual_cut : current.proposal = .code submission := by
  change (if (original.actual.readerCursor.past.length = cutLength) then _ else _) = _
  have literal : original.actual.readerCursor.past.length = cutLength := rfl
  rw [if_pos literal]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers
