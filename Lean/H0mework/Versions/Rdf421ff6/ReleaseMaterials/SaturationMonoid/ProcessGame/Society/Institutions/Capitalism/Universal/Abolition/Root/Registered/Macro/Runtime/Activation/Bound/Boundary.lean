import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Completion
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Successor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Compilation.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
local notation "O" => Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount

structure OriginalBoundary (frame : O) where
  germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current
  selected : frame.query = .raw germ

def originalBoundary (frame : O) (done : Bound.minor frame = 0) : OriginalBoundary frame := by
  cases selected : frame.query with
  | internal work =>
    have positive := Bound.work_has_pending_items frame work
    omega
  | raw germ => exact ⟨germ, selected⟩

inductive BoundaryAt : F → Type 4
  | original (frame : O) (raw : OriginalBoundary frame) : BoundaryAt (.original frame)
  | enacted
      (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
        depth count prefixLimit renewalLimit sourceDepth sourceCount)
      (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
      (frame : Public.Runtime.Frame origin admission) (done : ¬ frame.HasWork) :
      BoundaryAt (.enacted origin admission frame)

def boundaryOfZero (frame : F) (done : internalMass frame = 0) : BoundaryAt frame := by
  cases frame with
  | original current => exact .original current (originalBoundary current done)
  | enacted origin admission current =>
    change current.sourceMass = 0 at done
    exact .enacted origin admission current (fun work => by
      have positive := current.work_iff_positive_mass.mp work
      omega)

def boundary (frame : F) : BoundaryAt frame.completed :=
  boundaryOfZero frame.completed frame.complete.finished

/-- Both outputs are the already installed compiler's real actualAction.
Failure retains the precise failed source candidate and its original row. -/
theorem original_boundary_is_consumed_by_the_actual_compiler
    (frame : O) (raw : OriginalBoundary frame) :
    match Abolition.Functions.Revision.InitialAdmission.select (frame.controlOrigin raw.germ) with
    | .admitted admission =>
        (Abolition.Functions.Revision.InitialAdmission.Inquiry.state frame.package (.finite frame.visit)
          frame.authority).compileInquiry (.raw raw.germ) =
            .actualAction (Abolition.Functions.Revision.Enactment.Admitted.generated
              (frame.controlOrigin raw.germ) admission)
    | .obstructed failed =>
        (Abolition.Functions.Revision.InitialAdmission.Inquiry.state frame.package (.finite frame.visit)
          frame.authority).compileInquiry (.raw raw.germ) =
            .actualAction (Abolition.Functions.Revision.InitialAdmission.Failure.generated
              (frame.controlOrigin raw.germ) failed) ∧
          Abolition.Functions.Revision.InitialAdmission.Failure.publicObstruction
            (frame.controlOrigin raw.germ) failed = failed := by
  split
  · rename_i admission chosen
    exact Abolition.Functions.Revision.InitialAdmission.Inquiry.the_source_selected_enactment_is_the_actual_compiler_image
      frame.package (.finite frame.visit) frame.authority raw.germ admission chosen
  · rename_i failed chosen
    constructor
    · change Abolition.Functions.Revision.InitialAdmission.Inquiry.compilation
        frame.package (.finite frame.visit) frame.authority (.raw raw.germ) = _
      simp only [Abolition.Functions.Revision.InitialAdmission.Inquiry.compilation, chosen]
      rfl
    · rfl

theorem enacted_boundary_is_consumed_by_the_actual_compiler
    (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
      depth count prefixLimit renewalLimit sourceDepth sourceCount)
    (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
    (frame : Public.Runtime.Frame origin admission) (done : ¬ frame.HasWork) :
    Public.Inquiry.compileUnit origin admission frame.source frame.reader (.finite frame.visit) frame.actual frame.authority =
      .actualAction (Public.Inquiry.rawCore origin admission frame.source frame.reader (.finite frame.visit)
        frame.actual frame.authority done) := by
  exact dif_neg done

#print axioms boundary
#print axioms original_boundary_is_consumed_by_the_actual_compiler
#print axioms enacted_boundary_is_consumed_by_the_actual_compiler

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame
