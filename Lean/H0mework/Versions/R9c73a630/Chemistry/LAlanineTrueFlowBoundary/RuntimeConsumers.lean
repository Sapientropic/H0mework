import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowBoundary.RuntimeParentConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel TrueFlowDifferential TrueFlowGeometry TrueFlowBoundary TrueTubeWholeActual
open WholeCellBoundary WholeCellPartition Set Filter
open scoped Topology Matrix
noncomputable section

theorem trueBoundaryRuntime_local_charts :
    type_of% (trueBoundaryRuntimeFace_factorizes trueBoundaryRuntimeSeed (.component .certificate)) ∧
    (∀ p, HasStrictFDerivAt (generatedTrueBoundaryMaterial.localExtensions p)
      (generatedTrueBoundaryMaterial.parent.parent.jacobians p) p.val) ∧
    (∀ p, generatedTrueBoundaryMaterial.localExtensions p =ᶠ[𝓝[fullDomain] p.val]
      generatedTrueBoundaryMaterial.parent.parent.parameterMap) ∧
    (∀ p : BandPoint, ∃ e : OpenPartialHomeomorph Point Point, p.val ∈ e.source ∧
      EqOn e generatedTrueBoundaryMaterial.parent.parent.parameterMap (fullDomain ∩ e.source)) :=
  ⟨trueBoundaryRuntime_sourceCertificate.1, trueBoundaryRuntime_sourceCertificate.2.localDerivative,
    trueBoundaryRuntime_sourceCertificate.2.localAgreement, trueBoundaryRuntime_sourceCertificate.2.localCharts⟩

theorem trueBoundaryRuntime_exact_frontier :
    type_of% (trueBoundaryRuntimeFace_factorizes trueBoundaryRuntimeSeed (.component .certificate)) ∧
    frontier generatedTrueBoundaryMaterial.parent.spatialImage =
      generatedTrueBoundaryMaterial.parent.parent.parameterMap '' frontier fullDomain ∧
    frontier generatedTrueBoundaryMaterial.parent.spatialImage =
      ⋃ face : Face, generatedTrueBoundaryMaterial.spatialFaces face ∧
    (∀ face, (generatedTrueBoundaryMaterial.spatialFaces face).Nonempty) ∧
    (∀ face, generatedTrueBoundaryMaterial.spatialFaces face ⊆
      frontier generatedTrueBoundaryMaterial.parent.spatialImage) ∧
    (∀ face p, p ∈ faceDomain face.1 →
      generatedTrueBoundaryMaterial.parent.parent.faceMaps face p ∈
        frontier generatedTrueBoundaryMaterial.parent.spatialImage) ∧
    generatedTrueBoundaryMaterial.parent.parent.parameterMap fullLower ∈
      frontier generatedTrueBoundaryMaterial.parent.spatialImage ∧
    (∀ face p inside, face.1 ≠ 2 →
      generatedTrueBoundaryMaterial.parent.parent.faceMaps face p ∈
        frontier generatedTrueBoundaryMaterial.parent.spatialImage ∧
      generatedTrueBoundaryMaterial.parent.parent.faceFluxes face p inside = 0) :=
  ⟨trueBoundaryRuntime_sourceCertificate.1, trueBoundaryRuntime_sourceCertificate.2.frontierImage,
    trueBoundaryRuntime_sourceCertificate.2.sixFaces, trueBoundaryRuntime_sourceCertificate.2.facesNonempty,
    trueBoundaryRuntime_sourceCertificate.2.facesOnBoundary,
    trueBoundaryRuntime_sourceCertificate.2.facePointOnBoundary,
    trueBoundaryRuntime_sourceCertificate.2.sourceCorner, trueBoundaryRuntime_sourceCertificate.2.sideBoundaryFlux⟩

theorem trueBoundaryRuntime_regular_faces :
    type_of% (trueBoundaryRuntimeFace_factorizes trueBoundaryRuntimeSeed (.component .certificate)) ∧
    (∀ face p inside, Function.Injective
      (generatedTrueBoundaryMaterial.parent.parent.faceDerivatives face p inside)) ∧
    (∀ face p inside, LinearIndependent ℝ
      (generatedTrueBoundaryMaterial.parent.parent.faceTangents face p inside)) ∧
    (∀ face p inside, generatedTrueBoundaryMaterial.parent.parent.faceTangents face p inside 0 ⨯₃
      generatedTrueBoundaryMaterial.parent.parent.faceTangents face p inside 1 ≠ 0) ∧
    (∀ face p inside, generatedTrueBoundaryMaterial.parent.parent.orientedAreas face p inside ≠ 0) :=
  ⟨trueBoundaryRuntime_sourceCertificate.1, trueBoundaryRuntime_sourceCertificate.2.faceDerivativeInjective,
    trueBoundaryRuntime_sourceCertificate.2.tangentIndependent,
    trueBoundaryRuntime_sourceCertificate.2.tangentCrossNonzero,
    trueBoundaryRuntime_sourceCertificate.2.orientedAreaNonzero⟩

theorem trueBoundaryRuntime_flux_partition :
    type_of% (trueBoundaryRuntimeFace_factorizes trueBoundaryRuntimeSeed (.component .certificate)) ∧
    (∀ face p inside, face.1 ≠ 2 →
      generatedTrueBoundaryMaterial.parent.parent.faceFluxes face p inside = 0 ∧
      generatedTrueBoundaryMaterial.parent.parent.orientedAreas face p inside ≠ 0) ∧
    type_of% trueOrientedArea_eq_adjugate ∧
    (∀ face p inside, face.1 = 2 →
      generatedTrueBoundaryMaterial.parent.parent.faceFluxes face p inside =
        (if face.2 then 1 else -1 : ℝ) * LinearMap.det
          (generatedTrueBoundaryMaterial.parent.parent.jacobians
            (trueFaceParameter face p inside)).toLinearMap) ∧
    (∀ face p inside, face.1 = 2 →
      generatedTrueBoundaryMaterial.parent.parent.faceFluxes face p inside ≠ 0) :=
  ⟨trueBoundaryRuntime_sourceCertificate.1, trueBoundaryRuntime_sourceCertificate.2.sideFluxWithArea,
    trueBoundaryRuntime_sourceCertificate.2.orientedAreaAdjugate,
    trueBoundaryRuntime_sourceCertificate.2.capFluxDeterminant,
    trueBoundaryRuntime_sourceCertificate.2.capFluxNonzero⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
