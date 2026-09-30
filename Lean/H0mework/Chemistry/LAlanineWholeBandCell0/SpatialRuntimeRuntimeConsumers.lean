import H0mework.Chemistry.LAlanineWholeBandCell0.SpatialRuntimeRuntimeParentConsumers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialRuntime

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData WholeBandActual WholeBandGeometry WholeCellBoundary
open WholeBandCell0Spatial WholeBandCell0Boundary WholeBandCell0Conservation WholeBandCrossGeometry
open Set MeasureTheory
noncomputable section

theorem wholeBandCell0SpatialRuntime_image :
    type_of% (wholeBandCell0SpatialRuntimeFace_factorizes wholeBandCell0SpatialRuntimeSeed (.component .certificate)) ∧
    (∀ p, generatedWholeBandCell0SpatialMaterial.derivative p.val = generatedWholeBandCell0SpatialMaterial.parent.jacobians p) ∧
    (ContinuousOn generatedWholeBandCell0SpatialMaterial.parent.parent.parameterMap (cellDomain 0)) ∧
    (IsCompact generatedWholeBandCell0SpatialMaterial.image) ∧
    (generatedWholeBandCell0SpatialMaterial.image.Nonempty) ∧
    (MeasurableSet generatedWholeBandCell0SpatialMaterial.image) ∧
    (volume generatedWholeBandCell0SpatialMaterial.image < ⊤) ∧
    (0 < volume generatedWholeBandCell0SpatialMaterial.image) ∧
    (∀ g : Point → ℝ, (∫ x in generatedWholeBandCell0SpatialMaterial.image, g x) =
      ∫ p in cellDomain 0, |(generatedWholeBandCell0SpatialMaterial.derivative p).det| • g (generatedWholeBandCell0SpatialMaterial.parent.parent.parameterMap p)) ∧
    (∀ g : Point → ℝ, IntegrableOn g generatedWholeBandCell0SpatialMaterial.image ↔
      IntegrableOn (fun p => |(generatedWholeBandCell0SpatialMaterial.derivative p).det| • g (generatedWholeBandCell0SpatialMaterial.parent.parent.parameterMap p)) (cellDomain 0)) ∧
    (∀ g : Point → ENNReal, (∫⁻ x in generatedWholeBandCell0SpatialMaterial.image, g x) =
      ∫⁻ p in cellDomain 0, ENNReal.ofReal |(generatedWholeBandCell0SpatialMaterial.derivative p).det| * g (generatedWholeBandCell0SpatialMaterial.parent.parent.parameterMap p)) ∧
    (volume generatedWholeBandCell0SpatialMaterial.image = ∫⁻ p in cellDomain 0, ENNReal.ofReal |(generatedWholeBandCell0SpatialMaterial.derivative p).det|) :=
  ⟨wholeBandCell0SpatialRuntime_sourceCertificate.1,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.derivativeRecognition,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.mapContinuous,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.imageCompact,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.imageNonempty,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.imageMeasurable,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.volumeFinite,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.volumePositive,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.integral,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.integrability,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.nonnegativeIntegral,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.volumeJacobian⟩

theorem wholeBandCell0SpatialRuntime_boundary :
    type_of% (wholeBandCell0SpatialRuntimeFace_factorizes wholeBandCell0SpatialRuntimeSeed (.component .certificate)) ∧
    (∀ p : Cell0Point, ∃ e : OpenPartialHomeomorph Point Point,
      p.val ∈ e.source ∧ EqOn e generatedWholeBandCell0SpatialMaterial.parent.parent.parameterMap (cellDomain 0 ∩ e.source)) ∧
    (frontier generatedWholeBandCell0SpatialMaterial.image = generatedWholeBandCell0SpatialMaterial.parent.parent.parameterMap '' frontier (cellDomain 0)) ∧
    (frontier generatedWholeBandCell0SpatialMaterial.image = ⋃ face : Face, generatedWholeBandCell0SpatialMaterial.spatialFaces face) ∧
    (∀ face, (generatedWholeBandCell0SpatialMaterial.spatialFaces face).Nonempty) ∧
    (∀ face, generatedWholeBandCell0SpatialMaterial.spatialFaces face ⊆ frontier generatedWholeBandCell0SpatialMaterial.image) ∧
    (∀ face p inside, HasFDerivWithinAt (generatedWholeBandCell0SpatialMaterial.faceMaps face)
      (generatedWholeBandCell0SpatialMaterial.faceDerivatives face p inside) (generatedWholeBandCell0SpatialMaterial.faceDomains face.1) p) ∧
    (∀ face p inside, Module.finrank ℝ (LinearMap.range (generatedWholeBandCell0SpatialMaterial.faceDerivatives face p inside).toLinearMap) = 2) ∧
    type_of% cell0_trueFaceTangents_linearIndependent ∧
    (∀ face p inside, generatedWholeBandCell0SpatialMaterial.areas face p inside ≠ 0) ∧
    (∀ face p inside, face.1 ≠ 2 → generatedWholeBandCell0SpatialMaterial.fluxes face p inside = 0) ∧
    (∀ face p inside, generatedWholeBandCell0SpatialMaterial.areas face p inside = (if face.2 then 1 else -1 : ℝ) •
      (LinearMap.toMatrix' (generatedWholeBandCell0SpatialMaterial.parent.jacobians (cell0_trueFaceParameter face p inside)).toLinearMap).adjugate face.1) ∧
    (∀ face p inside, face.1 = 2 → generatedWholeBandCell0SpatialMaterial.fluxes face p inside = (if face.2 then 1 else -1 : ℝ) *
      LinearMap.det (generatedWholeBandCell0SpatialMaterial.parent.jacobians (cell0_trueFaceParameter face p inside)).toLinearMap) ∧
    (∀ face p inside, face.1 = 2 → generatedWholeBandCell0SpatialMaterial.fluxes face p inside ≠ 0) :=
  ⟨wholeBandCell0SpatialRuntime_sourceCertificate.1,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.localExtensions,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.boundaryImage,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.sixFaces,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.faceNonempty,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.faceBoundary,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.faceDerivative,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.faceRank,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.faceIndependent,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.areaNonzero,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.sideZero,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.areaCofactor,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.capDeterminant,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.capNonzero⟩

theorem wholeBandCell0SpatialRuntime_conservation :
    type_of% (wholeBandCell0SpatialRuntimeFace_factorizes wholeBandCell0SpatialRuntimeSeed (.component .certificate)) ∧
    (∀ p (s : Time), HasDerivWithinAt (fun t => (generatedWholeBandCell0SpatialMaterial.evolvingJacobian p t).det)
      (laplacian sourceTerms densityMatrix (generatedWholeBandCell0SpatialMaterial.parent.parent.fullFlows p s.val) * (generatedWholeBandCell0SpatialMaterial.evolvingJacobian p s).det)
      (Icc (-(1/2 : ℝ)) (1/2)) (s : ℝ)) ∧
    (∀ p (s : Time), generatedWholeBandCell0SpatialMaterial.evolvingJacobian p s =
      LinearMap.toMatrix' (generatedWholeBandCell0SpatialMaterial.parent.jacobians (cell0_retime p s)).toLinearMap) ∧
    (∀ p, generatedWholeBandCell0SpatialMaterial.evolvingJacobian p 0 = LinearMap.toMatrix' (generatedWholeBandCell0SpatialMaterial.parent.seedFrames p).toLinearMap) ∧
    (∀ p, (∫ t in (-(1/2 : ℝ))..(1/2), generatedWholeBandCell0SpatialMaterial.volumeRate p t) =
      (generatedWholeBandCell0SpatialMaterial.evolvingJacobian p (1/2)).det - (generatedWholeBandCell0SpatialMaterial.evolvingJacobian p (-(1/2))).det) ∧
    (∀ p, (∫ t in (-(1/2 : ℝ))..(1/2), generatedWholeBandCell0SpatialMaterial.volumeRate p t) =
      generatedWholeBandCell0SpatialMaterial.fluxes (2,true) (cell0_capBase p) (cell0_capBase_mem p) +
      generatedWholeBandCell0SpatialMaterial.fluxes (2,false) (cell0_capBase p) (cell0_capBase_mem p)) ∧
    type_of% cell0_seedFlowDerivative_det ∧
    (∀ p, 0 < LinearMap.det (generatedWholeBandCell0SpatialMaterial.parent.jacobians p).toLinearMap) ∧
    (∀ p inside, 0 < generatedWholeBandCell0SpatialMaterial.fluxes (2,true) p inside) ∧
    (∀ p inside, generatedWholeBandCell0SpatialMaterial.fluxes (2,false) p inside < 0) ∧
    (∀ g : Point → ℝ, (∫ x in generatedWholeBandCell0SpatialMaterial.image, g x) =
      ∫ p in cellDomain 0, (generatedWholeBandCell0SpatialMaterial.derivative p).det • g (generatedWholeBandCell0SpatialMaterial.parent.parent.parameterMap p)) ∧
    (∀ upper p inside, generatedWholeBandCell0SpatialMaterial.capFlux upper p = generatedWholeBandCell0SpatialMaterial.fluxes (2,upper) p inside) ∧
    (IntegrableOn generatedWholeBandCell0SpatialMaterial.laplacianPullback (cellDomain 0)) ∧
    (∀ p, p ∈ generatedWholeBandCell0SpatialMaterial.faceDomains 2 →
      (∫ t in Icc (-(1/2 : ℝ)) (1/2), generatedWholeBandCell0SpatialMaterial.laplacianPullback ((2 : Fin 3).insertNth t p)) =
        generatedWholeBandCell0SpatialMaterial.capFlux true p + generatedWholeBandCell0SpatialMaterial.capFlux false p) ∧
    (IntegrableOn (fun p => generatedWholeBandCell0SpatialMaterial.capFlux true p + generatedWholeBandCell0SpatialMaterial.capFlux false p) (generatedWholeBandCell0SpatialMaterial.faceDomains 2)) ∧
    ((∫ x in generatedWholeBandCell0SpatialMaterial.image, laplacian sourceTerms densityMatrix x) =
      ∫ p in generatedWholeBandCell0SpatialMaterial.faceDomains 2, generatedWholeBandCell0SpatialMaterial.capFlux true p + generatedWholeBandCell0SpatialMaterial.capFlux false p) :=
  ⟨wholeBandCell0SpatialRuntime_sourceCertificate.1,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.determinantEvolution,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.retimedActual,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.initialJacobian,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.timeFTC,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.trajectoryCaps,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.seedDeterminant,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.positiveJacobian,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.upperCapPositive,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.lowerCapNegative,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.orientedIntegral,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.capRecognition,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.pullbackIntegrability,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.sliceCaps,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.capIntegrability,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.spatialBalance⟩

theorem wholeBandCell0SpatialRuntime_cross :
    type_of% (wholeBandCell0SpatialRuntimeFace_factorizes wholeBandCell0SpatialRuntimeSeed (.component .certificate)) ∧
    type_of% cell16_domain_is_original ∧
    type_of% cell0_cell16_actual_meeting_classification ∧
    type_of% cell0_cell16_source_separation ∧
    (Disjoint generatedWholeBandCell0SpatialMaterial.image TrueFlowGeometry.truePatch) ∧
    (Function.Injective generatedWholeBandCell0SpatialMaterial.paidPair) ∧
    (Set.range generatedWholeBandCell0SpatialMaterial.paidPair = generatedWholeBandCell0SpatialMaterial.image ∪ TrueFlowGeometry.truePatch) :=
  ⟨wholeBandCell0SpatialRuntime_sourceCertificate.1,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.cell16Domain,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.actualMeeting,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.sourceSeparation,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.disjointImages,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.pairInjective,
    wholeBandCell0SpatialRuntime_sourceCertificate.2.pairRange⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
