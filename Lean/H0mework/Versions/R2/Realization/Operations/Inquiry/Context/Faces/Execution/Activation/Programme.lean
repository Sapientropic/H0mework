import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Mother

/-! A source programme supplies only its low raw family and an optional
source coface. Query, result, authority, target and runtime are generated
by the existing calculation activation mechanism. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
section OptionalSource
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
private abbrev sourceUp (source : SourceNativeAuthoritySource N V)
    (component : Option (SourceNativeProjectionLaw source.restructuringSource.toLedgerSource)) : SourceNativeAuthoritySource N V where
  restructuringSource := source.restructuringSource
  eventInventoryAdmission := source.eventInventoryAdmission
  lawSurface := source.lawSurface
  observationAt := source.observationAt
  projectionLaw := match component with | none => source.projectionLaw | some law => (source.withProjectionCoface law).projectionLaw
private theorem sourceUp_none (source : SourceNativeAuthoritySource N V) : sourceUp source none = source := by
  cases source
  rfl
private theorem sourceUp_some (source : SourceNativeAuthoritySource N V) (law : SourceNativeProjectionLaw source.restructuringSource.toLedgerSource) :
 sourceUp source (some law) = source.withProjectionCoface law := rfl



abbrev optionalSourceRoot (root : SourceNativeLivingRootClosure N V)
    (component : Option (SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource)) :
    SourceNativeLivingRootClosure N V where
  source := { base := sourceUp root.source.base component
              terminalHandoff := by
                cases component with
                | none =>
                    have same : sourceUp root.source.base none = root.source.base := by cases root.source.base; rfl
                    exact same.symm ▸ root.source.terminalHandoff
                | some law => exact root.source.terminalHandoff.withProjectionCoface law }
  emitted := root.emitted
  compiler_commutes := root.compiler_commutes
theorem optionalSourceRoot_none (root : SourceNativeLivingRootClosure N V) : optionalSourceRoot root none = root := by
  cases root with
  | mk source emitted commutes =>
    cases source with
    | mk base law =>
      cases base
      rfl
theorem optionalSourceRoot_some (root : SourceNativeLivingRootClosure N V) (component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource) :
    optionalSourceRoot root (some component) = root.withProjectionCoface component := rfl
def optionalInstallation (root : SourceNativeLivingRootClosure N V)
    (component : Option (SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource)) :
    SourceNativeProjectionLaw.InstallationAt root.source.base.projectionLaw
      (optionalSourceRoot root component).source.base.projectionLaw := by
  cases component with
  | none =>
      change root.source.base.projectionLaw.InstallationAt root.source.base.projectionLaw
      exact .refl _
  | some component =>
      change root.source.base.projectionLaw.InstallationAt
        (root.source.base.withProjectionCoface component).projectionLaw
      exact .inheritedCoface _ component
def optionalAuthority (root : SourceNativeLivingRootClosure N V)
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))}
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry)
    (component : Option (SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource)) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt (optionalSourceRoot root component) visit entry := by
  cases component with
  | none =>
      cases root with
      | mk source emitted commutes =>
        cases source with
        | mk base law =>
          cases base
          exact authority
  | some component => exact authority.withProjectionCoface component
end OptionalSource

structure SourceDatum (LowVar : Sorts → Type u)
    (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) where
  component : Option (SourceNativeProjectionLaw
    (Mother.baseState { frame with depth := 0 }).root.source.base.restructuringSource.toLedgerSource)
  reader : {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered} →
    SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current) →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue) (Var:=LowVar) (sort:=sort)
structure Programme where
  LowVar : Sorts → Type u
  datum : (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) → SourceDatum LowVar frame
def originalProgramme : Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort) where
  LowVar := PhysicalVar
  datum frame := { component := none, reader := Mother.reader { frame with depth := 0 } }
end SourceOperationInquiry.Context.Faces.Execution.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
