import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowConservation.RuntimeParentConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation TrueTubeWholeActual WholeCellBoundary WholeCellPartition Set MeasureTheory
noncomputable section

theorem conservationRuntime_actual_evolution :
    type_of% (conservationRuntimeFace_factorizes conservationRuntimeSeed (.component .certificate)) ∧
    type_of% evolvingJacobian_variational ∧ type_of% sourceHessian_trace ∧
    (∀ p s, HasDerivWithinAt (fun t => (generatedConservationMaterial.evolvingJacobians p t).det)
      (laplacian sourceTerms densityMatrix (actualPath p s) *
        (generatedConservationMaterial.evolvingJacobians p s).det)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ)) ∧
    (∀ p, generatedConservationMaterial.evolvingJacobians p (actualParameterTime p) =
      LinearMap.toMatrix' (generatedConservationMaterial.parent.parent.parent.jacobians p).toLinearMap) ∧
    (∀ p, (generatedConservationMaterial.evolvingJacobians p (actualParameterTime p)).det =
      LinearMap.det (generatedConservationMaterial.parent.parent.parent.jacobians p).toLinearMap) ∧
    (∀ p, Continuous (fun t => (generatedConservationMaterial.evolvingJacobians p t).det)) ∧
    (∀ p, ContinuousOn (generatedConservationMaterial.signedVolumeRates p)
      (Icc (-(1 / 2) : ℝ) (1 / 2))) ∧
    (∀ p, (∫ t in (-(1 / 2) : ℝ)..(1 / 2), generatedConservationMaterial.signedVolumeRates p t) =
      (generatedConservationMaterial.evolvingJacobians p (1 / 2)).det -
      (generatedConservationMaterial.evolvingJacobians p (-(1 / 2))).det) :=
  ⟨conservationRuntime_sourceCertificate.1, conservationRuntime_sourceCertificate.2.entryEvolution,
    conservationRuntime_sourceCertificate.2.sourceTrace, conservationRuntime_sourceCertificate.2.determinantEvolution,
    conservationRuntime_sourceCertificate.2.actualMatrix, conservationRuntime_sourceCertificate.2.actualDeterminant,
    conservationRuntime_sourceCertificate.2.determinantContinuous,
    conservationRuntime_sourceCertificate.2.rateContinuous, conservationRuntime_sourceCertificate.2.timeDeterminantBalance⟩

theorem conservationRuntime_same_source_caps :
    type_of% (conservationRuntimeFace_factorizes conservationRuntimeSeed (.component .certificate)) ∧
    type_of% retime_seed ∧ type_of% retime_seedDerivative ∧ type_of% retime_initialDerivative ∧
    (∀ (p : BandPoint) (s : Time), generatedConservationMaterial.evolvingJacobians p s =
      LinearMap.toMatrix' (generatedConservationMaterial.parent.parent.parent.jacobians (retime p s)).toLinearMap) ∧
    type_of% retime_eq_cap ∧
    (∀ p upper, generatedConservationMaterial.parent.parent.parent.faceFluxes
      (2, upper) (capBase p) (capBase_mem p) = (if upper then 1 else -1 : ℝ) *
        (generatedConservationMaterial.evolvingJacobians p (capTime upper)).det) ∧
    (∀ p, (∫ t in (-(1 / 2) : ℝ)..(1 / 2), generatedConservationMaterial.signedVolumeRates p t) =
      generatedConservationMaterial.parent.parent.parent.faceFluxes (2, true) (capBase p) (capBase_mem p) +
      generatedConservationMaterial.parent.parent.parent.faceFluxes (2, false) (capBase p) (capBase_mem p)) :=
  ⟨conservationRuntime_sourceCertificate.1, conservationRuntime_sourceCertificate.2.retimedSeed,
    conservationRuntime_sourceCertificate.2.retimedSeedFrame, conservationRuntime_sourceCertificate.2.retimedResponse,
    conservationRuntime_sourceCertificate.2.retimedMatrix, conservationRuntime_sourceCertificate.2.capAddress,
    conservationRuntime_sourceCertificate.2.capDeterminant, conservationRuntime_sourceCertificate.2.timeCapBalance⟩

theorem conservationRuntime_positive_orientation :
    type_of% (conservationRuntimeFace_factorizes conservationRuntimeSeed (.component .certificate)) ∧
    type_of% seedFlowDerivative_det ∧ type_of% seedFlowDerivative_det_pos ∧
    (∀ p, generatedConservationMaterial.evolvingJacobians p 0 =
      LinearMap.toMatrix' (seedFlowDerivative p).toLinearMap) ∧
    (∀ (p : BandPoint) (s : Time), 0 < (generatedConservationMaterial.evolvingJacobians p s).det) ∧
    (∀ p, 0 < LinearMap.det (generatedConservationMaterial.parent.parent.parent.jacobians p).toLinearMap) ∧
    (∀ p inside, 0 < generatedConservationMaterial.parent.parent.parent.faceFluxes (2, true) p inside) ∧
    (∀ p inside, generatedConservationMaterial.parent.parent.parent.faceFluxes (2, false) p inside < 0) ∧
    (∀ p, p ∈ fullDomain → 0 < (generatedConservationMaterial.parent.parent.derivative p).det) ∧
    (∀ g : Point → ℝ, (∫ x in generatedConservationMaterial.parent.parent.spatialImage, g x) =
      ∫ p in fullDomain, (generatedConservationMaterial.parent.parent.derivative p).det •
        g (generatedConservationMaterial.parent.parent.parent.parameterMap p)) :=
  ⟨conservationRuntime_sourceCertificate.1, conservationRuntime_sourceCertificate.2.seedDeterminant,
    conservationRuntime_sourceCertificate.2.seedOrientation, conservationRuntime_sourceCertificate.2.initialMatrix,
    conservationRuntime_sourceCertificate.2.evolvingOrientation, conservationRuntime_sourceCertificate.2.jacobianOrientation,
    conservationRuntime_sourceCertificate.2.upperCapOrientation, conservationRuntime_sourceCertificate.2.lowerCapOrientation,
    conservationRuntime_sourceCertificate.2.canonicalOrientation,
    conservationRuntime_sourceCertificate.2.orientedChangeVariables⟩

theorem conservationRuntime_actual_spatial_balance :
    type_of% (conservationRuntimeFace_factorizes conservationRuntimeSeed (.component .certificate)) ∧
    (∀ upper p inside, generatedConservationMaterial.capFluxes upper p =
      generatedConservationMaterial.parent.parent.parent.faceFluxes (2, upper) p inside) ∧
    IntegrableOn generatedConservationMaterial.laplacianPullback fullDomain ∧
    (∀ p, p ∈ faceDomain 2 →
      (∫ t in Icc (-(1 / 2) : ℝ) (1 / 2),
        generatedConservationMaterial.laplacianPullback ((2 : Fin 3).insertNth t p)) =
      generatedConservationMaterial.capFluxes true p + generatedConservationMaterial.capFluxes false p) ∧
    IntegrableOn (fun p => generatedConservationMaterial.capFluxes true p +
      generatedConservationMaterial.capFluxes false p) (faceDomain 2) ∧
    (∫ x in generatedConservationMaterial.parent.parent.spatialImage, laplacian sourceTerms densityMatrix x) =
      ∫ p in faceDomain 2, generatedConservationMaterial.capFluxes true p +
        generatedConservationMaterial.capFluxes false p :=
  ⟨conservationRuntime_sourceCertificate.1, conservationRuntime_sourceCertificate.2.capRecognition,
    conservationRuntime_sourceCertificate.2.pullbackIntegrable, conservationRuntime_sourceCertificate.2.sliceBalance,
    conservationRuntime_sourceCertificate.2.capSumIntegrable, conservationRuntime_sourceCertificate.2.spatialBalance⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
