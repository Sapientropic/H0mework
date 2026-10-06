import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inquiry
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Source

/-! The original physical raw stays a complete installed restriction under
an occurrence-generated programme's optional coface and calculation faces.
The source transports its history; original value sorts and units remain. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
open RootInquiryCompletion SourceOperationEffects
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation
  (Programme optionalSourceRoot epoch)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base baseRoot baseInstallation datum queryRoot queryLaw resultRoot resultLaw consumerRoot consumerLaw
    compilationLaw root lower actualVisit root_flat visit)
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
end A
open A
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable (programme : A.Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

private def optionalFace {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (component : Option (SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource))
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (face : SourceNativeRootSemanticFaceAt root visit) :
    SourceNativeRootSemanticFaceAt (optionalSourceRoot root component) visit := by
  cases component with
  | none =>
      cases root with
      | mk source emitted commutes =>
          cases source with
          | mk base handoff =>
              cases base
              exact face
  | some law =>
      exact { projection := .inherited face.projection
              active := face.active
              classifier_eq := face.classifier_eq }

private def extendFace {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource)
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (face : SourceNativeRootSemanticFaceAt root visit) :
    SourceNativeRootSemanticFaceAt (root.withProjectionCoface component) visit :=
  ⟨.inherited face.projection, face.active, face.classifier_eq⟩

private def originalRawFace : SourceNativeRootSemanticFaceAt
    (base frame).root (actualVisit frame) where
  projection := ((RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly.rawInstallation
    frame.old frame.registered frame.packetAt).trans
      (SourceNativeProjectionLaw.InstallationAt.inheritedCoface frame.currentState.root.source.base
        (SourceOperationInquiry.Context.Installation.component (epoch frame)))).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def inheritedRawFace := optionalFace (base frame).root (datum frame programme).component (originalRawFace frame)
  |> extendFace (root := baseRoot frame programme) (queryLaw (epoch frame) programme)
  |> extendFace (root := queryRoot frame programme) (resultLaw (epoch frame) programme)
  |> extendFace (root := resultRoot frame programme) (consumerLaw (epoch frame) programme)
  |> extendFace (root := consumerRoot frame programme) (compilationLaw (epoch frame) programme)


private theorem optionalFace_read {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (component : Option (SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource))
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (face : SourceNativeRootSemanticFaceAt root visit) :
    HEq (optionalFace root component face).rootRead face.rootRead := by
  cases component with
  | none =>
      cases root with
      | mk source emitted commutes =>
          cases source with
          | mk base handoff =>
              cases base
              exact HEq.rfl
  | some law => exact HEq.rfl

private theorem extendFace_read {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource)
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (face : SourceNativeRootSemanticFaceAt root visit) :
    HEq (extendFace component face).rootRead face.rootRead := HEq.rfl

theorem physicalRaw_read : HEq (inheritedRawFace frame programme).rootRead frame.rawRead := by
  unfold inheritedRawFace
  exact (extendFace_read _ _).trans ((extendFace_read _ _).trans
    ((extendFace_read _ _).trans ((extendFace_read _ _).trans
      ((optionalFace_read _ _ _).trans HEq.rfl))))


private theorem historyVisit_heq {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {first second : SourceNativeLedgerRootClosure N V} (same : first = second)
    (actualVisit : SourceNativeTemporalVisitAt second) :
    HEq (show SourceNativeTemporalVisitAt first from
      ⟨actualVisit.current, Eq.mpr (congrArg (fun lower => SourceNativeTemporalReachableAt lower actualVisit.current) same)
        actualVisit.history⟩) actualVisit := by
  cases same
  rfl

theorem visit_original : visit frame programme = actualVisit frame :=
  eq_of_heq (historyVisit_heq (root_flat frame programme) (actualVisit frame))

private theorem face_transport_read {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {first second : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (same : first = second) (face : SourceNativeRootSemanticFaceAt root second) :
    HEq (Eq.mpr (congrArg (SourceNativeRootSemanticFaceAt root) same) face).rootRead face.rootRead := by
  cases same
  exact HEq.rfl

private def restrictionOfFace {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (face : SourceNativeRootSemanticFaceAt root visit)
    (raw : SourceOperationInquiry.Context.Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (same : HEq face.rootRead raw) : SourceOperationInquiry.Context.RawRestrictionAt
      (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
      (⟨N, ⟨V, root.toAuthoritativeRoot, visit⟩⟩ : AnyAuthoritativeRootCurrent.{u}) where
  projection := face.projection
  active := face.active
  classifier_eq := face.classifier_eq
  payload_eq := type_eq_of_heq same

def rawRestriction : SourceOperationInquiry.Context.RawRestrictionAt
    (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
    (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered,
      ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt,
        (root frame programme).toAuthoritativeRoot, visit frame programme⟩⟩ : AnyAuthoritativeRootCurrent) :=
  restrictionOfFace (root frame programme) (visit frame programme)
    (Eq.mpr (congrArg (SourceNativeRootSemanticFaceAt (root frame programme))
      (visit_original frame programme)) (inheritedRawFace frame programme)) frame.rawRead
    ((face_transport_read (visit_original frame programme) (inheritedRawFace frame programme)).trans
      (physicalRaw_read frame programme))


def readRaw (actual : AnyAuthoritativeRootCurrent.{u})
    (restriction : SourceOperationInquiry.Context.RawRestrictionAt
      (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) actual) :
    SourceOperationInquiry.Context.Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  Eq.mp restriction.payload_eq (actual.current.root.source.projectionLaw.project restriction.projection
    (actual.current.root.emitted actual.current.visit.current) restriction.active)

private theorem restrictionOfFace_read {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (face : SourceNativeRootSemanticFaceAt root visit)
    (raw : SourceOperationInquiry.Context.Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (same : HEq face.rootRead raw) :
    readRaw _ (restrictionOfFace root visit face raw same) = raw := by
  have cast : HEq (readRaw _ (restrictionOfFace root visit face raw same)) face.rootRead :=
    eqRec_heq_iff.mpr HEq.rfl
  exact eq_of_heq (cast.trans same)

theorem raw_restriction : readRaw _ (rawRestriction frame programme) = frame.rawRead :=
  restrictionOfFace_read _ _ _ _ _

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
