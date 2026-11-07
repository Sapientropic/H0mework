import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Failure

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (failed : InitialObstructionAt context)

/-- The original source still generates its actual next. The same event's
receipt additionally carries every precise public-candidate failure. -/
def targetAt (event : ExactTemporalCausalRootEventAt (sourceRoot context).toAuthoritativeRoot.toLedgerRoot context.visit) :
    SourceNativeSequentialActualActionTargetAt (sourceRoot context) context.visit event
      (sourceEntry context) (sourceAuthority context) :=
  let original := Macro.Raw.Target.targetAt context.native context.data context.reader context.basis
    context.visit context.germ context.authority event
  { original with
    Receipt := fun answer => original.Receipt answer × ULift.{3, 0} (InitialObstructionAt context)
    receipt := ⟨original.receipt, ⟨failed⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt (sourceRoot context) context.visit
    (sourceEntry context) (sourceAuthority context) where
  targetAt := targetAt context failed

def sourceEvent := (sourceRoot context).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt context.visit

def generated := (program context failed).generate (sourceEvent context)

def publicObstruction : InitialObstructionAt context := (generated context failed).receipt.2.down

theorem the_real_kernel_receipt_contains_the_same_original_obstruction : publicObstruction context failed = failed := rfl

theorem the_original_answer_is_retained :
    (generated context failed).answer = Macro.Raw.reportAt context.native context.data context.reader context.germ := rfl

theorem the_original_actual_target_is_retained :
    (generated context failed).target.targetRoot =
      Macro.Raw.Target.targetRoot context.native context.data context.reader context.basis context.visit context.germ := rfl

def issueAt (word : Source.Program.RawEvent Party Good Port Technology Instrument)
    (present : word ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit (sourceSnapshot context)) :=
  (publicObstruction context failed).publicObstruction.failureAt word present

#print axioms program
#print axioms publicObstruction
#print axioms issueAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Failure
