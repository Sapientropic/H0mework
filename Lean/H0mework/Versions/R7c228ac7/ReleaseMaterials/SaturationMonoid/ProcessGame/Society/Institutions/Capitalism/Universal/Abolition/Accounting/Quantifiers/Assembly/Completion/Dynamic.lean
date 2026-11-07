import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Core
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Selection
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Raw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Innovation
open Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))
  (enough : Joint.Planning.Enough seed claim (shared seed claim))
  {sourceDepth sourceCount : Nat} {review : Option (ReviewPhase.ContextAt seed.input)}
  (origin : Abolition.Functions.Revision.Context (input := seed.input) (review := review)
    seed.depth seed.count 0 0 sourceDepth sourceCount)
  (reader : Macro.Raw.Reader seed.input seed.depth seed.count)

structure AdmittedDynamicAt (admission : Abolition.Functions.Revision.InitialAdmissionAt origin) : Prop where
  same_root : (Runtime.Resumption.nativeFrame seed claim enough).root = Runtime.Inquiry.root seed claim
  same_vocabulary : (Runtime.Resumption.nativeFrame seed claim enough).V = Runtime.V seed claim
  complete_original_account : type_of% (Runtime.Resumption.the_returned_native_current_is_the_same_completed_original_account
    seed claim enough)
  live_actual_raw : type_of% (Runtime.Resumption.the_next_source_context_reads_this_same_actual_raw seed claim enough)
  no_original_pending_work : type_of% (Runtime.Resumption.the_resumed_native_cursor_has_no_pending_work seed claim enough reader)
  actual_inquiry_next : type_of% (Runtime.Resumption.the_actual_joint_root_returns_the_original_dynamic_native_inquiry
    seed claim enough origin admission reader)
  original_parser : type_of% (Runtime.Resumption.the_actual_next_compiler_is_the_original_native_selection
    seed claim enough reader origin admission)
  actual_new_source_action : type_of% (Runtime.Resumption.the_actual_next_compiler_selects_the_dynamic_source_action
    seed claim enough reader origin admission)

theorem an_admitted_source_has_the_same_actual_dynamic_continuation
    (admission : Abolition.Functions.Revision.InitialAdmissionAt origin) :
    AdmittedDynamicAt seed claim enough origin reader admission where
  same_root := rfl
  same_vocabulary := rfl
  complete_original_account := Runtime.Resumption.the_returned_native_current_is_the_same_completed_original_account seed claim enough
  live_actual_raw := Runtime.Resumption.the_next_source_context_reads_this_same_actual_raw seed claim enough
  no_original_pending_work := Runtime.Resumption.the_resumed_native_cursor_has_no_pending_work seed claim enough reader
  actual_inquiry_next := Runtime.Resumption.the_actual_joint_root_returns_the_original_dynamic_native_inquiry seed claim enough origin admission reader
  original_parser := Runtime.Resumption.the_actual_next_compiler_is_the_original_native_selection seed claim enough reader origin admission
  actual_new_source_action := Runtime.Resumption.the_actual_next_compiler_selects_the_dynamic_source_action seed claim enough reader origin admission

def DynamicDispositionAt : Abolition.Functions.Revision.InitialSelection origin → Prop
  | .admitted admission => AdmittedDynamicAt seed claim enough origin reader admission
  | .obstructed obstruction =>
      Abolition.Functions.Revision.InitialAdmission.select origin = .obstructed obstruction ∧
        Abolition.Functions.Revision.Trigger.select origin = obstruction.previous ∧
        Abolition.Functions.Revision.InitialAdmission.inspectPublic origin = .obstructed obstruction.publicObstruction ∧
        ¬ ∃ admission, Abolition.Functions.Revision.InitialAdmission.select origin = .admitted admission

theorem the_original_source_generates_its_actual_dynamic_disposition :
    DynamicDispositionAt seed claim enough origin reader (Abolition.Functions.Revision.InitialAdmission.select origin) := by
  cases selected : Abolition.Functions.Revision.InitialAdmission.select origin with
  | admitted admission => exact an_admitted_source_has_the_same_actual_dynamic_continuation seed claim enough origin reader admission
  | obstructed obstruction =>
      refine ⟨selected,obstruction.previous_source,obstruction.public_source,?_⟩
      rintro ⟨admission,accepted⟩
      rw [selected] at accepted
      cases accepted

theorem an_available_source_plan_forces_actual_dynamic_continuation
    (available : ∃ word ∈ Abolition.Functions.Revision.PublicPlan.candidates seed.input seed.depth seed.count 0 0
        (Abolition.Functions.Revision.InitialAdmission.sourceSnapshot origin),
      Abolition.Functions.Revision.PublicPlan.Checks seed.input seed.depth seed.count 0 0
        (Abolition.Functions.Revision.InitialAdmission.sourceSnapshot origin) word) :
    ∃ admission, Abolition.Functions.Revision.InitialAdmission.select origin = .admitted admission ∧
      AdmittedDynamicAt seed claim enough origin reader admission := by
  obtain ⟨admission,selected⟩ := Abolition.Functions.Revision.InitialAdmission.a_publicly_available_source_plan_forces_admission origin available
  exact ⟨admission,selected,an_admitted_source_has_the_same_actual_dynamic_continuation seed claim enough origin reader admission⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
