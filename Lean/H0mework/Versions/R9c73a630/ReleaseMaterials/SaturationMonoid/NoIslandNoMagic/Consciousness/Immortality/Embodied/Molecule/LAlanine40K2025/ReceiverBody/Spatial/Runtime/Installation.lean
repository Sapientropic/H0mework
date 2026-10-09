import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.IQA

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open BasinRefinement.WholeBandBasin.Family.All
noncomputable section

abbrev ParentBase := ReceiverBody.Runtime.authoritySource
abbrev ParentLedger := ParentBase.restructuringSource.toLedgerSource

-- Only the already-generated joint result admits the static transport certificate.
def Ready : ReceiverBody.Runtime.BodyCurrent → Prop
  | .ingress => False
  | .ready result => result=ReceiverBody.Runtime.sourceOutput

inductive Component
  | material | certificate

abbrev Projection := SourceNativeProjectionCoface PreciseAtomicIQA.Runtime.Face Component

def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {current} _ => PLift (Ready current)
  InactiveAt := fun _ {current} _ => PLift (¬Ready current)
  classify := by
    classical
    exact fun _ {current} _ => if h : Ready current then .inl ⟨h⟩ else .inr ⟨h⟩
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .component .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence ×
        Spatial.Material
    | .component .certificate => PLift (Spatial.Closure
        (materialOf (ReceiverBody.Runtime.currentResult current)))
    | .inherited face => (type_of% (originalFace face)) × PLift (type_of% (original_face_factorizes face))
  project := by
    intro projection current occurrence active
    cases projection with
    | component component =>
      cases component with
      | material => exact (ParentLedger.ledgerCompiler.compile occurrence,
          materialOf (ReceiverBody.Runtime.currentResult current))
      | certificate =>
        cases current with
        | ingress => exact False.elim active.down
        | ready result =>
          have equal : result=ReceiverBody.Runtime.sourceOutput := active.down
          subst result
          exact ⟨sourceClosure⟩
    | inherited face => exact (originalFace face,⟨original_face_factorizes face⟩)

def authoritySource := ParentBase.withProjectionCoface projectionLaw

def componentInstallation : SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

def inheritedInstallation : SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN ReceiverBody.Runtime.BodyV where
  source := authoritySource
  emitted := ReceiverBody.Runtime.authoritativeRoot.emitted
  compiler_commutes := ReceiverBody.Runtime.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure RecoveryN ReceiverBody.Runtime.BodyV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem source_and_law_unchanged :
    authoritySource.restructuringSource=ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission=ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface=ParentBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem rootCompiler_unchanged (current : ReceiverBody.Runtime.BodyCurrent) :
    authoritativeRoot.toLedgerRoot.generatedLedgerAt current=
      ReceiverBody.Runtime.authoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime
