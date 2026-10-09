import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCache.SaturationRuntimeParentConsumers

/-! Read both the inherited AtomicMass material and the installed original Gaussian calculation. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceExponential SourceSignedEvaluator SourceGaussianModel SourceRectangle WholeBandSource
noncomputable section

/-- Extract the actual installed value from this runtime's material face. -/
def readMaterial (runtime : LivingRuntimeState saturationRuntimeProcess) : SaturationMaterial :=
  match saturationRuntimeFacade.readoutAt runtime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

/-- Read the inherited Root60 value through its retained face, with no replacement material. -/
def readAtomicMassMaterial (runtime : LivingRuntimeState saturationRuntimeProcess) :
    LAlanine40K2025.AtomicMass.Runtime.AtomicMassMaterial :=
  match saturationRuntimeFacade.readoutAt runtime (.inherited (.component .material)) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

theorem saturationRuntime_material_read (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.component .material)) ∧
    readMaterial runtime = generatedSaturationMaterial :=
  ⟨saturationRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem saturationRuntime_parent_read (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.inherited (.component .material))) ∧
    (readMaterial runtime).parent = readAtomicMassMaterial runtime ∧
    readAtomicMassMaterial runtime = LAlanine40K2025.AtomicMass.Runtime.generatedAtomicMassMaterial :=
  ⟨saturationRuntimeFace_factorizes runtime (.inherited (.component .material)), rfl, rfl⟩

/-- The whole original 21-field AtomicMass certificate is recovered from its inherited face. -/
theorem saturationRuntime_parent_certificate (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.inherited (.component .certificate))) ∧
    LAlanine40K2025.AtomicMass.AtomicMassClosure := by
  refine ⟨saturationRuntimeFace_factorizes runtime (.inherited (.component .certificate)), ?_⟩
  rcases saturationRuntimeFacade.readoutAt runtime (.inherited (.component .certificate)) with
    ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

/-- The material read exposes the original call, group, radial, reduction and exponent values. -/
theorem saturationRuntime_source_material (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.component .material)) ∧
    (readMaterial runtime).calculation.calls = cell2Call ∧
    (readMaterial runtime).calculation.groups = groupAt ∧
    (readMaterial runtime).calculation.boxes = (fun i => callBox (cell2Call i)) ∧
    (readMaterial runtime).calculation.terms = (fun g => groupTerm (groupAt g)) ∧
    (readMaterial runtime).calculation.relativeCoordinates =
      (fun i g => relative (groupTerm (groupAt g)) (callBox (cell2Call i))) ∧
    (readMaterial runtime).calculation.exponents = (fun g => (groupTerm (groupAt g)).exponent) ∧
    (readMaterial runtime).calculation.radialIntervals =
      (fun i g => radialPair (groupTerm (groupAt g)) (callBox (cell2Call i))) ∧
    (readMaterial runtime).calculation.reductions = (fun i g => callReductions (cell2Call i) (groupAt g)) ∧
    (readMaterial runtime).calculation.exponentialIntervals = (fun _ _ => (0,1/scale)) ∧
    (readMaterial runtime).calculation.actualGaussians =
      (fun g x => Real.exp (radialArgument (groupTerm (groupAt g)) x)) :=
  ⟨saturationRuntimeFace_factorizes runtime (.component .material),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The read output is the original evaluator at those same read inputs. -/
theorem saturationRuntime_original_evaluator (runtime : LivingRuntimeState saturationRuntimeProcess)
    (i : Fin 64) (g : SaturatedGroup) :
    type_of% (saturationRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (saturationRuntimeFace_factorizes runtime (.component .certificate)) ∧
    (readMaterial runtime).calculation.exponentialIntervals i g =
      exponential ((readMaterial runtime).calculation.radialIntervals i g)
        ((readMaterial runtime).calculation.reductions i g).1
        ((readMaterial runtime).calculation.reductions i g).2 :=
  ⟨saturationRuntimeFace_factorizes runtime (.component .material),
    saturationRuntimeFace_factorizes runtime (.component .certificate),
    (saturationRuntime_sourceCertificateAt runtime).2.originalEvaluator i g⟩

/-- Actual Gaussian containment consumes both installed faces at the same runtime occurrence. -/
theorem saturationRuntime_actual_gaussian (runtime : LivingRuntimeState saturationRuntimeProcess)
    (i : Fin 64) (g : SaturatedGroup) (x : Point)
    (inside : InRectangle ((readMaterial runtime).calculation.boxes i) x) :
    type_of% (saturationRuntimeFace_factorizes runtime (.component .material)) ∧
    type_of% (saturationRuntimeFace_factorizes runtime (.component .certificate)) ∧
    Holds ((readMaterial runtime).calculation.exponentialIntervals i g)
      ((readMaterial runtime).calculation.actualGaussians g x) :=
  ⟨saturationRuntimeFace_factorizes runtime (.component .material),
    saturationRuntimeFace_factorizes runtime (.component .certificate),
    (saturationRuntime_sourceCertificateAt runtime).2.actualGaussian i g x inside⟩

theorem saturationRuntime_original_cache_kernel (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.component .certificate)) ∧
    type_of% Source.original_groupComputed :=
  ⟨saturationRuntimeFace_factorizes runtime (.component .certificate),
    (saturationRuntime_sourceCertificateAt runtime).2.cacheKernel⟩

theorem saturationRuntime_source_census (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.component .certificate)) ∧
    Function.Injective (readMaterial runtime).calculation.calls ∧
    Function.Injective (readMaterial runtime).calculation.groups :=
  ⟨saturationRuntimeFace_factorizes runtime (.component .certificate),
    (saturationRuntime_sourceCertificateAt runtime).2.calls,
    (saturationRuntime_sourceCertificateAt runtime).2.groups⟩

/-- The inherited actual mass remains the mass in the same original M3 response. -/
theorem saturationRuntime_actualMass (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.inherited (.component .material))) ∧
    type_of% (saturationRuntimeFace_factorizes runtime (.inherited (.component .certificate))) ∧
    (readAtomicMassMaterial runtime).reconstructedMasses =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.masses := by
  refine ⟨saturationRuntimeFace_factorizes runtime (.inherited (.component .material)),
    saturationRuntimeFace_factorizes runtime (.inherited (.component .certificate)), ?_⟩
  rw [saturationRuntime_response]
  exact (saturationRuntime_parent_certificate runtime).2.reconstructedMass

end
end LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
