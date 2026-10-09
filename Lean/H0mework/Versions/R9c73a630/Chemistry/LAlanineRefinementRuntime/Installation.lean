import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementRuntime.Parent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementGeometry.Producer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementDensity.SourceGeneratedLaplacian
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

theorem continuousField_same_geometry : SourceFiniteData.boxCentre = Geometry.Source.center := by
  funext axis
  fin_cases axis <;> decide +kernel

def refinementSourceClosure : Prop :=
  Geometry.refinementClosure ∧ SourceLaplaceProducer.sourceLaplaceClosure ∧
  SourceFiniteData.boxCentre = Geometry.Source.center ∧
  type_of% (SourceGaussianModel.density_laplacian_exact SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix)

theorem sourceGeneratedRefinement : refinementSourceClosure :=
  ⟨Geometry.sourceGeneratedCurvedRefinement,
    SourceLaplaceProducer.sourceGeneratedContinuousLaplacianRefinement, continuousField_same_geometry,
    SourceGaussianModel.density_laplacian_exact SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix⟩

structure RefinementMaterial where
  parent : BasinPartition.Runtime.BasinMaterial
  geometry : Array Geometry.Data.RunReceipt
  centre : Fin 3 → ℚ
  transverseBasis : Fin 3 → Fin 2 → ℚ
  lowerBracket : Geometry.Data.Knot → ℚ
  upperBracket : Geometry.Data.Knot → ℚ
  density : SourceGaussianModel.Point → ℝ
  laplacian : SourceGaussianModel.Point → ℝ
  axisBound : Fin 3 → ℚ
  radius : ℚ
  geometrySource : String
  continuousSource : String

def generatedRefinementMaterial : RefinementMaterial where
  parent := refinementParentMaterial
  geometry := Geometry.Source.runs
  centre := SourceFiniteData.boxCentre
  transverseBasis := Geometry.Source.basis
  lowerBracket := Geometry.Source.lower
  upperBracket := Geometry.Source.upper
  density := SourceGaussianModel.density SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix
  laplacian := SourceGaussianModel.laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix
  axisBound := SourceLaplaceProducer.axisBound
  radius := SourceFiniteData.boxRadius
  geometrySource := Geometry.Source.sourcePacketText
  continuousSource := SourceFiniteData.sourceText

inductive RefinementProjection
  | material | certificate

def refinementProjectionLaw : SourceNativeProjectionLaw RefinementLedger where
  Projection := RefinementProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt RefinementLedger.source occurrence × RefinementMaterial
    | .certificate => PLift refinementSourceClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (RefinementLedger.ledgerCompiler.compile occurrence, generatedRefinementMaterial)
    | certificate => exact ⟨sourceGeneratedRefinement⟩

def refinementAuthoritySource := RefinementBase.withProjectionCoface refinementProjectionLaw

def refinementComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt refinementProjectionLaw refinementAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface RefinementBase refinementProjectionLaw

def refinementInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt RefinementBase.projectionLaw refinementAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface RefinementBase refinementProjectionLaw

def refinementAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := refinementAuthoritySource
  emitted := BasinPartition.Runtime.basinAuthoritativeRoot.emitted
  compiler_commutes := BasinPartition.Runtime.basinAuthoritativeRoot.compiler_commutes

def refinementLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  refinementAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem refinement_source_and_law_unchanged :
    refinementAuthoritySource.restructuringSource = RefinementBase.restructuringSource ∧
    refinementAuthoritySource.lawSurface = RefinementBase.lawSurface := ⟨rfl, rfl⟩

theorem refinement_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    refinementAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      BasinPartition.Runtime.basinAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
