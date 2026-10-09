import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell2.RuntimeParentConsumers

/-! The actual field and original RHS consume this runtime's material and certificate;
the complete Gaussian and atomic-mass parents remain readable through their inherited faces. -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceExponential SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceRectangle SourceFields
open WholeBandSource WholeBandMatrix IntervalParameterMap ContinuousGradient
noncomputable section

def readMaterial (runtime : LivingRuntimeState initialFieldRuntimeProcess) : InitialFieldMaterial :=
  match initialFieldRuntimeFacade.readoutAt runtime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def readSaturationMaterial (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    WholeBandSaturation.Runtime.SaturationMaterial :=
  match initialFieldRuntimeFacade.readoutAt runtime (.inherited (.component .material)) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def readAtomicMassMaterial (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    LAlanine40K2025.AtomicMass.Runtime.AtomicMassMaterial :=
  match initialFieldRuntimeFacade.readoutAt runtime (.inherited (.inherited (.component .material))) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

theorem initialFieldRuntime_material_read (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    readMaterial runtime = generatedInitialFieldMaterial :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem initialFieldRuntime_parent_read (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.component .material))) ∧
    (readMaterial runtime).parent = readSaturationMaterial runtime ∧
    readSaturationMaterial runtime = WholeBandSaturation.Runtime.generatedSaturationMaterial :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.inherited (.component .material)), rfl, rfl⟩

theorem initialFieldRuntime_atomicMass_read (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.inherited (.component .material)))) ∧
    (readSaturationMaterial runtime).parent = readAtomicMassMaterial runtime ∧
    readAtomicMassMaterial runtime = LAlanine40K2025.AtomicMass.Runtime.generatedAtomicMassMaterial :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.inherited (.inherited (.component .material))), rfl, rfl⟩

theorem initialFieldRuntime_parent_certificate (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.component .certificate))) ∧
    WholeBandSaturation.Source.Cell2SaturationClosure := by
  refine ⟨initialFieldRuntimeFace_factorizes runtime (.inherited (.component .certificate)), ?_⟩
  rcases initialFieldRuntimeFacade.readoutAt runtime (.inherited (.component .certificate)) with
    ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem initialFieldRuntime_atomicMass_certificate (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.inherited (.component .certificate)))) ∧
    LAlanine40K2025.AtomicMass.AtomicMassClosure := by
  refine ⟨initialFieldRuntimeFace_factorizes runtime (.inherited (.inherited (.component .certificate))), ?_⟩
  rcases initialFieldRuntimeFacade.readoutAt runtime (.inherited (.inherited (.component .certificate))) with
    ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem initialFieldRuntime_source_material (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    (readMaterial runtime).calculation.calls = ![128,160] ∧
    (readMaterial runtime).calculation.box = callBox 128 ∧
    (readMaterial runtime).calculation.reductions = callReductions 128 ∧
    (readMaterial runtime).calculation.cache = Call128.material ∧
    (readMaterial runtime).calculation.ao = Call128.sourceAO ∧
    (readMaterial runtime).calculation.density = densityMatrix ∧
    (readMaterial runtime).calculation.rows = Call128.matrixRows ∧
    (readMaterial runtime).calculation.computed = calculatedField Call128.matrixRows ∧
    (readMaterial runtime).calculation.reported = (fun i => recordedCallField (![128,160] i)) ∧
    (readMaterial runtime).calculation.actualGradient = sourceGradient ∧
    (readMaterial runtime).calculation.actualHessian = sourceHessian :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem initialFieldRuntime_source_domain (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    (∀ i : Fin 2,
      callBox ((readMaterial runtime).calculation.calls i) = (readMaterial runtime).calculation.box ∧
      callReductions ((readMaterial runtime).calculation.calls i) = (readMaterial runtime).calculation.reductions ∧
      callReportedDensity ((readMaterial runtime).calculation.calls i) = callReportedDensity 128) ∧
    Function.Injective (readMaterial runtime).calculation.calls ∧
    ∃ x, InRectangle (readMaterial runtime).calculation.box x :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    initialFieldRuntimeFace_factorizes runtime (.component .certificate),
    (initialFieldRuntime_sourceCertificateAt runtime).2.restrictions,
    (initialFieldRuntime_sourceCertificateAt runtime).2.addresses,
    (initialFieldRuntime_sourceCertificateAt runtime).2.nonemptyBox⟩

theorem initialFieldRuntime_actual_orbitals (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    AOContains (readMaterial runtime).calculation.box (readMaterial runtime).calculation.ao :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    initialFieldRuntimeFace_factorizes runtime (.component .certificate),
    (initialFieldRuntime_sourceCertificateAt runtime).2.actualOrbitals⟩

theorem initialFieldRuntime_full_matrix (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    RowsCertificate (readMaterial runtime).calculation.rows (readMaterial runtime).calculation.ao ∧
    ∀ j k : LowJet,
      calculatedBilinear (readMaterial runtime).calculation.rows j k =
        bilinearPair ((readMaterial runtime).calculation.ao j) ((readMaterial runtime).calculation.ao k)
          (readMaterial runtime).calculation.density :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    initialFieldRuntimeFace_factorizes runtime (.component .certificate),
    (initialFieldRuntime_sourceCertificateAt runtime).2.matrixCalculation,
    (initialFieldRuntime_sourceCertificateAt runtime).2.fullBilinear⟩

theorem initialFieldRuntime_calculated_field (runtime : LivingRuntimeState initialFieldRuntimeProcess)
    (x : Point) (inside : InRectangle (readMaterial runtime).calculation.box x) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    FieldHolds (readMaterial runtime).calculation.computed x :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    initialFieldRuntimeFace_factorizes runtime (.component .certificate),
    (initialFieldRuntime_sourceCertificateAt runtime).2.calculatedField x inside⟩

theorem initialFieldRuntime_actual_values (runtime : LivingRuntimeState initialFieldRuntimeProcess)
    (x : Point) (inside : InRectangle (readMaterial runtime).calculation.box x) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    (∀ axis, Holds ((readMaterial runtime).calculation.computed.gradient axis)
      ((readMaterial runtime).calculation.actualGradient x axis)) ∧
    (∀ axis direction, Holds ((readMaterial runtime).calculation.computed.hessian axis direction)
      ((readMaterial runtime).calculation.actualHessian x axis direction)) :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    initialFieldRuntimeFace_factorizes runtime (.component .certificate),
    (initialFieldRuntime_sourceCertificateAt runtime).2.actualValues x inside⟩

theorem initialFieldRuntime_report_recognition (runtime : LivingRuntimeState initialFieldRuntimeProcess)
    (i : Fin 2) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    (∀ axis, (readMaterial runtime).calculation.computed.gradient axis =
      ((readMaterial runtime).calculation.reported i).gradient axis) ∧
    (∀ axis direction, (readMaterial runtime).calculation.computed.hessian axis direction =
      ((readMaterial runtime).calculation.reported i).hessian axis direction) :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    initialFieldRuntimeFace_factorizes runtime (.component .certificate),
    (initialFieldRuntime_sourceCertificateAt runtime).2.reportRecognition i⟩

theorem initialFieldRuntime_registered_field (runtime : LivingRuntimeState initialFieldRuntimeProcess)
    (i : Fin 2) (x : Point) (inside : InRectangle (readMaterial runtime).calculation.box x) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    FieldHolds ((readMaterial runtime).calculation.reported i) x :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    initialFieldRuntimeFace_factorizes runtime (.component .certificate),
    (initialFieldRuntime_sourceCertificateAt runtime).2.registeredField i x inside⟩

theorem initialFieldRuntime_parametric_rhs (runtime : LivingRuntimeState initialFieldRuntimeProcess)
    (state : JetBox) (x : Point) (J : Point →L[ℝ] Point)
    (inside : InRectangle (readMaterial runtime).calculation.box x) (input : JetHolds state x J) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    JetHolds (rhs (readMaterial runtime).calculation.computed state)
      ((readMaterial runtime).calculation.actualGradient x) ((sourceHessianLinear x).comp J) :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material),
    initialFieldRuntimeFace_factorizes runtime (.component .certificate),
    (initialFieldRuntime_sourceCertificateAt runtime).2.parametricRhs state x J inside input⟩

theorem initialFieldRuntime_inherited_gaussian (runtime : LivingRuntimeState initialFieldRuntimeProcess)
    (i : Fin 64) (g : WholeBandSaturation.SaturatedGroup) (x : Point)
    (inside : InRectangle ((readSaturationMaterial runtime).calculation.boxes i) x) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.component .material))) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.component .certificate))) ∧
    Holds ((readSaturationMaterial runtime).calculation.exponentialIntervals i g)
      ((readSaturationMaterial runtime).calculation.actualGaussians g x) :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.inherited (.component .material)),
    initialFieldRuntimeFace_factorizes runtime (.inherited (.component .certificate)),
    (initialFieldRuntime_parent_certificate runtime).2.actualGaussian i g x inside⟩

theorem initialFieldRuntime_original_cache_kernel (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.component .certificate))) ∧
    type_of% WholeBandSaturation.Source.original_groupComputed :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.inherited (.component .certificate)),
    (initialFieldRuntime_parent_certificate runtime).2.cacheKernel⟩

theorem initialFieldRuntime_actualMass (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.inherited (.component .material)))) ∧
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited (.inherited (.component .certificate)))) ∧
    (readAtomicMassMaterial runtime).reconstructedMasses =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.masses := by
  refine ⟨initialFieldRuntimeFace_factorizes runtime (.inherited (.inherited (.component .material))),
    initialFieldRuntimeFace_factorizes runtime (.inherited (.inherited (.component .certificate))), ?_⟩
  rw [initialFieldRuntime_response]
  exact (initialFieldRuntime_atomicMass_certificate runtime).2.reconstructedMass

end
end LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
