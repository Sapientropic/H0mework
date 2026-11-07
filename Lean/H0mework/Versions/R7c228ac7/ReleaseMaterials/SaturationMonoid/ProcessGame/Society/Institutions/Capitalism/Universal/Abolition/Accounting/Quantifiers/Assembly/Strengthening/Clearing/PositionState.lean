import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.PositionStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Position

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (position : Position input depth count reader)
  (request : Request Party Good Port Technology Instrument)
  (selected : position.actual.proposal reader = .primitive request)
  (noConsents : request.consents = [])
  (valid : (Physical.Public.interpreter input).Valid
    (Physical.Public.stateAt input depth count 0 0 [] position.past).raw request)

include selected noConsents valid

theorem step_reads_the_same_actual_material_successor :
    (Physical.Public.stateAt input depth count 0 0 [] (step position request selected noConsents valid).past).raw =
      (Physical.Public.interpreter input).step
        (Physical.Public.stateAt input depth count 0 0 [] position.past).raw request := by
  rw [step_records_exactly_this_original_primitive]
  rw [Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.the_source_history_extends_by_this_same_primitive]
  rw [(Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.one_checked_original_primitive_has_one_actual_material_step
    input (Physical.Public.stateAt input depth count 0 0 [] position.past) request noConsents valid).2.2]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Position
