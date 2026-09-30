import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation
import H0mework.Chemistry.LAlaninePropagation.GeneratedDensityConsumers

/-! # The actual molecular source generates a nonstationary Schrödinger orbit -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.AffineRelaxation

noncomputable section

set_option maxRecDepth 4096 in
theorem firstCommutator_exact :
    integerCommutator electronicSource 0 1 = 4562554154385668873220 := by
  decide

theorem firstCommutator_nonzero : integerCommutator electronicSource 0 1 ≠ 0 := by
  rw [firstCommutator_exact]
  decide

theorem sourceDensity_not_constant :
    ¬ ∀ time : ℝ, densityEvolution electronicSource time = initialDensity electronicSource :=
  densityEvolution_not_constant electronicSource 0 1 firstCommutator_nonzero

theorem sourceDensityMatrix_changes :
    ∃ time : ℝ, densityMatrix electronicSource time ≠ densityMatrix electronicSource 0 := by
  by_contra unchanged
  push Not at unchanged
  apply sourceDensity_not_constant
  intro time
  have same := unchanged time
  unfold densityMatrix at same
  exact (Matrix.toEuclideanCLM (n := Basis) (𝕜 := ℂ)).symm.injective same |>.trans
    (densityEvolution_zero electronicSource)

def independentDensity : IndependentReadout ℝ := ⟨Matrix Basis Basis ℂ, densityMatrix electronicSource⟩

theorem electronCountKernelEscape :
    FaceKernelEscapeAt (probeRead electronicSource .electronTrace) independentDensity := by
  obtain ⟨time, different⟩ := sourceDensityMatrix_changes
  exact ⟨time, 0, electronTrace_preserved electronicSource time, different⟩

theorem electronCountCannotMintElectronicState :
    ¬ Function.FactorsThrough (densityMatrix electronicSource)
      (probeRead electronicSource .electronTrace) :=
  electronCountKernelEscape.not_factorsThrough

def fixedNuclearGeometry : ℝ → Force.Interface.NuclearCoordinates :=
  fun _ => Force.Source.updateReadout.recordedTargetPositions

theorem nuclearGeometryKernelEscape : FaceKernelEscapeAt fixedNuclearGeometry independentDensity := by
  obtain ⟨time, different⟩ := sourceDensityMatrix_changes
  exact ⟨time, 0, rfl, different⟩

theorem nuclearGeometryCannotMintElectronicState :
    ¬ Function.FactorsThrough (densityMatrix electronicSource) fixedNuclearGeometry :=
  nuclearGeometryKernelEscape.not_factorsThrough

set_option maxRecDepth 4096 in
theorem sourceTraceNumerator_exact :
    (∑ index : Basis, symmetricEntry electronicSource.d0Q index index) = 47999999999997 := by
  decide

theorem sourceElectronicTrace (time : ℝ) :
    Matrix.trace (densityMatrix electronicSource time) = (47999999999997 : ℂ) / 1000000000000 := by
  rw [densityTrace_preserved]
  calc
    Matrix.trace (initialDensityMatrix electronicSource) =
        ((∑ index : Basis, symmetricEntry electronicSource.d0Q index index : Int) : ℂ) /
          1000000000000 := by
      simp [Matrix.trace, Matrix.diag, initialDensityMatrix, Int.cast_sum, Finset.sum_div]
    _ = _ := by rw [sourceTraceNumerator_exact]; norm_num

/-- The source-fixed duration selects one slice of the generated law, not an input endpoint. -/
def nativeElectronicNext : ElectronicOperator := densityEvolution electronicSource 1

structure SourceGeneratedLAlanineElectronicPropagationCrown : Prop where
  sourceSelfAdjoint : IsSelfAdjoint (hamiltonian electronicSource)
  generatedFlow : BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate
    ElectronicSpace (hamiltonian electronicSource)
  normPreserved : ∀ time state, ‖propagator electronicSource time state‖ = ‖state‖
  sourceDerivative : HasDerivAt (densityEvolution electronicSource) (densityTangent electronicSource) 0
  nonzeroTangentSource : integerCommutator electronicSource 0 1 ≠ 0
  nonstationary : ¬ ∀ time, densityEvolution electronicSource time = initialDensity electronicSource
  densitySelfAdjoint : ∀ time, IsSelfAdjoint (densityEvolution electronicSource time)
  tracePreserved : ∀ time, Matrix.trace (densityMatrix electronicSource time) =
    (47999999999997 : ℂ) / 1000000000000
  exactKernel : FaceKernelExactAt (registeredConsumers electronicSource) (densityMatrix electronicSource)
  quotientRange : Nonempty ((registeredConsumers electronicSource).Quotient ≃
    Set.range (densityMatrix electronicSource))
  independentConsumers : ∀ probe : DensityProbe,
    ∃! factor : Set.range (densityMatrix electronicSource) → ℝ,
      ∀ time, factor ⟨densityMatrix electronicSource time, time, rfl⟩ =
        probeRead electronicSource probe time
  countEscape : ¬ Function.FactorsThrough (densityMatrix electronicSource)
    (probeRead electronicSource .electronTrace)
  geometryEscape : ¬ Function.FactorsThrough (densityMatrix electronicSource) fixedNuclearGeometry
  generatedNext : nativeElectronicNext = densityEvolution electronicSource 1

theorem sourceGeneratedLAlanineElectronicPropagation_crown :
    SourceGeneratedLAlanineElectronicPropagationCrown where
  sourceSelfAdjoint := hamiltonian_selfAdjoint electronicSource
  generatedFlow := schrodingerFlow electronicSource
  normPreserved := propagator_preserves_norm electronicSource
  sourceDerivative := densityEvolution_hasDerivAt_zero electronicSource
  nonzeroTangentSource := firstCommutator_nonzero
  nonstationary := sourceDensity_not_constant
  densitySelfAdjoint := densitySelfAdjoint_preserved electronicSource
  tracePreserved := sourceElectronicTrace
  exactKernel := densityKernelExact electronicSource
  quotientRange := ⟨densityQuotientEquivRange electronicSource⟩
  independentConsumers := everyDensityConsumer_uniqueFactorization electronicSource
  countEscape := electronCountCannotMintElectronicState
  geometryEscape := nuclearGeometryCannotMintElectronicState
  generatedNext := rfl

end

end LAlanine40K2025.Propagation.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
