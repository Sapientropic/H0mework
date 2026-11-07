import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Accounting.Current input depth count frame.anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start actual)

local notation "oldLaw" => frame.root.toAuthoritativeRoot.source.projectionLaw
local notation "oldOccurrence" => frame.root.emitted visit.current

/-- The complete previous inquiry remains a source coordinate, including
its inactive receipts and any earlier births or public-law cofaces. -/
def previousInquiry : SourceNativeProjectionLaw
    (Source.ledgerSource frame.family actual registered) where
  Projection := (oldLaw).Projection
  ActiveAt := fun projection {_} _ => (oldLaw).ActiveAt projection oldOccurrence
  InactiveAt := fun projection {_} _ => (oldLaw).InactiveAt projection oldOccurrence
  classify := fun projection {_} _ => (oldLaw).classify projection oldOccurrence
  PayloadAt := fun projection {_} _ active => (oldLaw).PayloadAt projection oldOccurrence active
  project := fun projection {_} _ active => (oldLaw).project projection oldOccurrence active

def targetFrame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start :=
  (Born.nativeFrame frame.family actual registered).withProjectionCoface
    (previousInquiry frame visit actual registered)

def oldProjection (projection : (oldLaw).Projection) :
    (targetFrame frame visit actual registered).root.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .component projection

theorem oldProjection_injective : Function.Injective (oldProjection frame visit actual registered) := by
  intro left right same
  injection same

theorem every_previous_inquiry_outcome_is_literal
    (projection : (oldLaw).Projection) :
    HEq ((targetFrame frame visit actual registered).root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (oldProjection frame visit actual registered projection)
        ((targetFrame frame visit actual registered).root.emitted none))
      ((oldLaw).outcomeAt projection oldOccurrence) := by
  dsimp only [targetFrame, Public.NativeFrame.withProjectionCoface,
    SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot,
    SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt, oldProjection, previousInquiry]
  cases frame.root.source.base.projectionLaw.classify projection (frame.root.emitted visit.current) <;> rfl

#print axioms targetFrame
#print axioms every_previous_inquiry_outcome_is_literal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action
