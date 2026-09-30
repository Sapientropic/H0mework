import H0mework.Chemistry.LAlaninePropagation.GeneratedElectronicDynamics
import H0mework.Foundation.Relations.ConsumerFace
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Independent density probes of the same generated electronic orbit -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Consumer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

noncomputable section

def densityMatrix (source : ElectronicPropagationSource) (time : ℝ) : Matrix Basis Basis ℂ :=
  (Matrix.toEuclideanCLM (n := Basis) (𝕜 := ℂ)).symm (densityEvolution source time)

inductive DensityProbe where
  | realEntry (row column : Basis)
  | imaginaryEntry (row column : Basis)
  | electronTrace
  | effectiveHamiltonianExpectation
  deriving DecidableEq

/-- Coordinate tomography and conserved quantities read the generated occurrence.
The effective-Hamiltonian expectation is not the nonlinear DFT functional energy. -/
def probeRead (source : ElectronicPropagationSource) : DensityProbe → ℝ → ℝ
  | .realEntry row column, time => (densityMatrix source time row column).re
  | .imaginaryEntry row column, time => (densityMatrix source time row column).im
  | .electronTrace, time => (Matrix.trace (densityMatrix source time)).re
  | .effectiveHamiltonianExpectation, time =>
      (Matrix.trace (activeMatrix source * densityMatrix source time)).re

def registeredConsumers (source : ElectronicPropagationSource) : IndependentConsumerSystem ℝ where
  Consumer := DensityProbe
  Output := fun _ => ℝ
  read := probeRead source
  positive := ⟨.realEntry 0 0⟩

theorem densityKernelExact (source : ElectronicPropagationSource) :
    FaceKernelExactAt (registeredConsumers source) (densityMatrix source) := by
  intro left right
  constructor
  · intro same probe
    cases probe <;> simp only [registeredConsumers, probeRead, same]
  · intro same
    apply Matrix.ext
    intro row column
    apply Complex.ext
    · exact same (.realEntry row column)
    · exact same (.imaginaryEntry row column)

def densityQuotientEquivRange (source : ElectronicPropagationSource) :
    (registeredConsumers source).Quotient ≃ Set.range (densityMatrix source) :=
  (densityKernelExact source).quotientEquivRange

theorem everyDensityConsumer_uniqueFactorization (source : ElectronicPropagationSource)
    (probe : DensityProbe) :
    ∃! factor : Set.range (densityMatrix source) → ℝ,
      ∀ time, factor ⟨densityMatrix source time, time, rfl⟩ = probeRead source probe time :=
  (densityKernelExact source).everyConsumer_unique_factorization probe

theorem sameRootDensityCarrier_uniqueIso (source : ElectronicPropagationSource)
    {Alternate : Type} (alternate : ℝ → Alternate)
    (exactKernel : FaceKernelExactAt (registeredConsumers source) alternate) :
    ∃! equivalence : Set.range (densityMatrix source) ≃ Set.range alternate,
      ∀ time, equivalence ⟨densityMatrix source time, time, rfl⟩ =
        ⟨alternate time, time, rfl⟩ :=
  ⟨(densityKernelExact source).completeCarrierEquiv exactKernel,
    (densityKernelExact source).completeCarrierEquiv_commutes exactKernel,
    fun candidate commutes => (densityKernelExact source).completeCarrierEquiv_unique
      exactKernel candidate commutes⟩

private theorem trace_conjugation (U D V : EuclideanSpace ℂ Basis →L[ℂ] EuclideanSpace ℂ Basis)
    (inverse : V * U = 1) :
    Matrix.trace ((Matrix.toEuclideanCLM (n := Basis) (𝕜 := ℂ)).symm (U * D * V)) =
      Matrix.trace ((Matrix.toEuclideanCLM (n := Basis) (𝕜 := ℂ)).symm D) := by
  simp only [map_mul]
  rw [Matrix.trace_mul_cycle, ← map_mul, inverse, map_one, Matrix.one_mul]

theorem densityTrace_preserved (source : ElectronicPropagationSource) (time : ℝ) :
    Matrix.trace (densityMatrix source time) = Matrix.trace (initialDensityMatrix source) := by
  change Matrix.trace ((Matrix.toEuclideanCLM (n := Basis) (𝕜 := ℂ)).symm
    (propagator source time * initialDensity source * propagator source (-time))) = _
  rw [trace_conjugation _ _ _ (propagator_neg_mul source time)]
  simp [initialDensity, matrixOperatorEquiv]

theorem electronTrace_preserved (source : ElectronicPropagationSource) (time : ℝ) :
    probeRead source .electronTrace time = probeRead source .electronTrace 0 := by
  simp only [probeRead, densityTrace_preserved]

theorem densitySelfAdjoint_preserved (source : ElectronicPropagationSource) (time : ℝ) :
    IsSelfAdjoint (densityEvolution source time) := by
  change star (densityEvolution source time) = densityEvolution source time
  unfold densityEvolution
  rw [propagator_neg_eq_star]
  simp only [star_mul, star_star, (initialDensity_selfAdjoint source).star_eq, mul_assoc]

end

end LAlanine40K2025.Propagation.Consumer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
