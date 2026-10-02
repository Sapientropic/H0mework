import H0mework.Versions.R2.Physics.MotherDeclarationsNative.PhysicalQueryConsumption
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision MotherJointCarrier

noncomputable section

abbrev source := SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.source
abbrev OccurrenceAt (current : SpinPair.Current) := source.source.toRootSource.actual.OccurrenceAt current
abbrev Anchor := Sigma OccurrenceAt
abbrev Key := Anchor × Query

def projectionLaw (typeLaw actionLaw : Law) : SourceNativeProjectionLaw source := by
  classical
  exact
    { Projection := Key × Fin 3
      ActiveAt := fun projection {current} occurrence => PLift (projection.1.1 = ⟨current, occurrence⟩)
      InactiveAt := fun projection {current} occurrence => PLift (projection.1.1 ≠ ⟨current, occurrence⟩)
      classify := fun projection {current} occurrence =>
        if same : projection.1.1 = ⟨current, occurrence⟩ then .inl ⟨same⟩ else .inr ⟨same⟩
      PayloadAt := fun projection {current} occurrence _ =>
        match projection.2 with
        | 0 => Answer
        | 1 => SourceNativeInquiryAnswerConsumerTokenAt projection.1.2
            (ULift.up.{1, 0} occurrence) (materialEntry (SpinPair.support current))
            (answer typeLaw actionLaw projection.1.2)
        | _ => SourceNativeInquiryCompilationTokenAt
            (U7 := materialU7) (calculus := materialInquiryCalculus)
            (oldTheory := TheoryState.rootSemantic MaterialN)
            (materialEntry (SpinPair.support current)) projection.1.2
            (ULift.up.{1, 0} occurrence) .answered Answer
      project := fun projection {_current} _occurrence _ => by
        rcases projection with ⟨key, tag⟩
        split
        · exact answer typeLaw actionLaw key.2
        · exact .canonical
        · exact .canonical (answer typeLaw actionLaw key.2) }

def historySource : SourceNativeAuthoritySource MaterialN SpinPair.V :=
  SpinPair.authoritativeRoot.source.withProjectionCoface ActualFormation.historyLaw.toProjectionLaw

/-- The original complete physics inventory is inherited; no raw-dynamics replacement is used. -/
def declarationSource (typeLaw actionLaw : Law) : SourceNativeAuthoritySource MaterialN SpinPair.V :=
  historySource.withProjectionCoface (projectionLaw typeLaw actionLaw)

def queryInstallation (typeLaw actionLaw : Law) :
    SourceNativeProjectionLaw.InstallationAt (projectionLaw typeLaw actionLaw)
      (declarationSource typeLaw actionLaw).projectionLaw :=
  .componentCoface historySource (projectionLaw typeLaw actionLaw)

def physicsInstallation (typeLaw actionLaw : Law) :
    SourceNativeProjectionLaw.InstallationAt SpinPair.authoritativeRoot.source.projectionLaw
      (declarationSource typeLaw actionLaw).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    SpinPair.authoritativeRoot.source ActualFormation.historyLaw.toProjectionLaw).trans
    (.inheritedCoface historySource (projectionLaw typeLaw actionLaw))

theorem original_history_preserved :
    historySource.restructuringSource.toLedgerSource = source := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery
