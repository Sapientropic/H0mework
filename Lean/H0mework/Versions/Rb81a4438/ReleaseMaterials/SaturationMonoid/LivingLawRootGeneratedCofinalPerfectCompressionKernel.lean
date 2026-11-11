import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Noetherian.Basic
import H0mework.Foundation.Cofinal.CompressionFace
import H0mework.Realization.Determinant.FourTermProjection

/-!
# Root-generated cofinal perfect compression

A cofinal source relation history is allowed to expose only its actual finite
generator envelope and its monotone family of generated relation submodules.
No stabilization index, finite model, basis, matrix, perfectness receipt or
quasi-isomorphism enters the mouth.

The finite free generator envelope is Noetherian.  Its ascending relation
history therefore has a least stabilization stage.  At that generated stage
the relation submodule itself is finite free over `ℤ`; its inclusion into the
generator module is the canonical two-term projective resolution of the
cofinal presented carrier.  The exact quotient map generates a
quasi-isomorphism to the cofinal carrier, and the existing four-term
determinant engine reads the padded resolution without a caller-owned
perfectness certificate.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPerfectCompression

open CofinalPerfectCompressionAxiomFreeCore
open PerfectComplexDeterminantProjection

noncomputable section

universe u w

/-- Actual cofinal relation growth inside one source-generated finite
generator envelope.  Monotonicity is the incidence law of the diagram, not a
finished compactness or perfectness receipt. -/
structure CofinalSourceGeneratedRelationDiagramAt
    (Generator : Type u) [Finite Generator] where
  relationStages : ℕ →o Submodule ℤ (Generator →₀ ℤ)

/-- The root-owned compression face.  Its constructor has no calculation
receipt: the only material inputs are the exact root, actual generator
occurrences and the cofinal relation-diagram occurrence. -/
structure RootGeneratedCofinalPerfectCompressionAt
    {Root : Type w} {Generator : Type u} [Finite Generator]
    (rootOccurrence : RootedAccountedUnfolding Root)
    (generatorOccurrences : Generator → RootedAccountedUnfolding Generator)
    (diagramOccurrence : RootedAccountedUnfolding
      (CofinalSourceGeneratedRelationDiagramAt Generator)) : Type where
  private mk ::
  core : RootGeneratedCofinalCompressionIncidenceAt rootOccurrence
    generatorOccurrences diagramOccurrence

namespace RootGeneratedCofinalPerfectCompressionAt

variable {Root : Type w} {Generator : Type u} [Finite Generator]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {generatorOccurrences :
  Generator → RootedAccountedUnfolding Generator}
variable {diagramOccurrence : RootedAccountedUnfolding
  (CofinalSourceGeneratedRelationDiagramAt Generator)}

def generate
    (generatorOccurrences_exact : ∀ generator,
      (generatorOccurrences generator).root = generator) :
    RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence :=
  ⟨RootGeneratedCofinalCompressionIncidenceAt.generate
    generatorOccurrences_exact⟩

def root
    (_face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    RootedAccountedUnfolding Root :=
  rootOccurrence

def generators
    (_face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    Generator → RootedAccountedUnfolding Generator :=
  generatorOccurrences

def actualDiagram
    (_face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    CofinalSourceGeneratedRelationDiagramAt Generator :=
  diagramOccurrence.root

theorem generatorOccurrence_root
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence)
    (generator : Generator) :
    (face.generators generator).root = generator :=
  face.core.generatorOccurrence_root generator

abbrev GeneratorModule
    (_face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :=
  Generator →₀ ℤ

def StabilizesAt
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence)
    (stage : ℕ) : Prop :=
  ∀ later, stage ≤ later →
    face.actualDiagram.relationStages stage =
      face.actualDiagram.relationStages later

private theorem stabilization_exists
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    ∃ stage, face.StabilizesAt stage := by
  letI : Fintype Generator := Fintype.ofFinite Generator
  let generatorBasis : Module.Basis Generator ℤ (Generator →₀ ℤ) :=
    Finsupp.basisSingleOne
  letI : Module.Finite ℤ (Generator →₀ ℤ) :=
    Module.Finite.of_basis generatorBasis
  exact monotone_stabilizes_iff_noetherian.mpr inferInstance
    face.actualDiagram.relationStages

/-- Generated compactness/stabilization trace.  The private constructor
prevents callers from installing a chosen truncation. -/
structure GeneratedCompactnessStabilizationTraceAt
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) : Type where
  private mk ::
  index : ℕ
  stabilizes : face.StabilizesAt index
  least : ∀ stage, face.StabilizesAt stage → index ≤ stage

noncomputable def stabilizationTrace
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    GeneratedCompactnessStabilizationTraceAt face := by
  classical
  exact
    { index := Nat.find face.stabilization_exists
      stabilizes := Nat.find_spec face.stabilization_exists
      least := fun _ stable ↦
        Nat.find_min' face.stabilization_exists stable }

def stableRelationSubmodule
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    Submodule ℤ face.GeneratorModule :=
  face.actualDiagram.relationStages face.stabilizationTrace.index

def cofinalRelationSubmodule
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    Submodule ℤ face.GeneratorModule :=
  ⨆ stage, face.actualDiagram.relationStages stage

/-- Noetherian stabilization identifies the entire cofinal relation carrier
with the relation carrier at the generated least stage. -/
theorem cofinalRelationSubmodule_eq_stable
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    face.cofinalRelationSubmodule = face.stableRelationSubmodule := by
  apply le_antisymm
  · refine iSup_le fun stage ↦ ?_
    by_cases after : face.stabilizationTrace.index ≤ stage
    · exact (face.stabilizationTrace.stabilizes stage after).symm.le
    · exact face.actualDiagram.relationStages.monotone
        (Nat.le_of_not_ge after)
  · exact le_iSup
      (fun stage ↦ face.actualDiagram.relationStages stage)
      face.stabilizationTrace.index

abbrev StableRelationCarrier
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :=
  face.stableRelationSubmodule

abbrev CofinalPresentedCarrier
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :=
  face.GeneratorModule ⧸ face.cofinalRelationSubmodule

abbrev ZeroTerm := Fin 0 → ℤ

/-- The canonical finite-projective compression.  Its relation term is the
stable submodule itself, so redundant source relations are removed without
choosing a presentation matrix or relation basis. -/
def compressionComplex
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    FourTermIntegralComplexAt face.StableRelationCarrier
      face.GeneratorModule ZeroTerm ZeroTerm where
  d₀ := face.stableRelationSubmodule.subtype
  d₁ := 0
  d₂ := 0
  d₁_comp_d₀ := rfl
  d₂_comp_d₁ := rfl

/-- The cofinal presented carrier, placed in degree one. -/
def cofinalCarrierComplex
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    FourTermIntegralComplexAt ZeroTerm face.CofinalPresentedCarrier
      ZeroTerm ZeroTerm where
  d₀ := 0
  d₁ := 0
  d₂ := 0
  d₁_comp_d₀ := rfl
  d₂_comp_d₁ := rfl

/-- Generated quasi-isomorphism face from the canonical compression to the
cofinal carrier.  For this two-term resolution the quasi-isomorphism laws are
the exactness of `relations → generators → quotient`. -/
structure GeneratedCofinalCompressionQuasiIsomorphismAt
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) : Type where
  private mk ::

namespace GeneratedCofinalCompressionQuasiIsomorphismAt

variable {face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
  generatorOccurrences diagramOccurrence}

def generate : GeneratedCofinalCompressionQuasiIsomorphismAt face :=
  ⟨⟩

def degreeZeroMap
    (_quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    face.StableRelationCarrier →ₗ[ℤ] ZeroTerm :=
  0

def degreeOneMap
    (_quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    face.GeneratorModule →ₗ[ℤ] face.CofinalPresentedCarrier :=
  face.cofinalRelationSubmodule.mkQ

def degreeTwoMap
    (_quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    ZeroTerm →ₗ[ℤ] ZeroTerm :=
  0

def degreeThreeMap
    (_quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    ZeroTerm →ₗ[ℤ] ZeroTerm :=
  0

theorem commute_degreeZero
    (quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    quasiIso.degreeOneMap.comp face.compressionComplex.d₀ =
      face.cofinalCarrierComplex.d₀.comp quasiIso.degreeZeroMap := by
  ext relation
  change Submodule.Quotient.mk (relation : face.GeneratorModule) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  rw [face.cofinalRelationSubmodule_eq_stable]
  exact relation.property

theorem degreeZero_acyclic
    (_quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    LinearMap.ker face.compressionComplex.d₀ = ⊥ :=
  Submodule.ker_subtype face.stableRelationSubmodule

theorem degreeOne_exact
    (quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    LinearMap.range face.compressionComplex.d₀ =
      LinearMap.ker quasiIso.degreeOneMap := by
  change LinearMap.range face.stableRelationSubmodule.subtype =
    LinearMap.ker face.cofinalRelationSubmodule.mkQ
  rw [Submodule.range_subtype, Submodule.ker_mkQ,
    face.cofinalRelationSubmodule_eq_stable]

theorem degreeOne_surjective
    (quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    Function.Surjective quasiIso.degreeOneMap :=
  Submodule.mkQ_surjective _

/-- Exact two-term criterion for the generated map to be a
quasi-isomorphism: source degree zero is acyclic and degree-one homology is
the cofinal quotient. -/
def IsQuasiIsomorphism
    (quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) : Prop :=
  LinearMap.ker face.compressionComplex.d₀ = ⊥ ∧
    LinearMap.range face.compressionComplex.d₀ =
      LinearMap.ker quasiIso.degreeOneMap ∧
    Function.Surjective quasiIso.degreeOneMap

theorem isQuasiIsomorphism
    (quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    quasiIso.IsQuasiIsomorphism :=
  ⟨quasiIso.degreeZero_acyclic, quasiIso.degreeOne_exact,
    quasiIso.degreeOne_surjective⟩

/-- Explicit homology-one equivalence generated by exactness and cofinal
stabilization. -/
noncomputable def degreeOneHomologyEquiv
    (quasiIso : GeneratedCofinalCompressionQuasiIsomorphismAt face) :
    (face.GeneratorModule ⧸
        LinearMap.range face.compressionComplex.d₀) ≃ₗ[ℤ]
      face.CofinalPresentedCarrier :=
  (Submodule.quotEquivOfEq _ _ quasiIso.degreeOne_exact).trans
    (quasiIso.degreeOneMap.quotKerEquivOfSurjective
      quasiIso.degreeOne_surjective)

end GeneratedCofinalCompressionQuasiIsomorphismAt

def quasiIsomorphism
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    GeneratedCofinalCompressionQuasiIsomorphismAt face :=
  GeneratedCofinalCompressionQuasiIsomorphismAt.generate

def compressionComplexOccurrence
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :=
  RootedAccountedUnfolding.zero face.compressionComplex

def determinantProjection
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    RootGeneratedFourTermPerfectDeterminantProjectionAt face.root
      face.compressionComplexOccurrence :=
  RootGeneratedFourTermPerfectDeterminantProjectionAt.generate

/-- Internal PID basis of the generated stable relation submodule.  It is
used only to discharge finite-free typeclasses and is never a source field or
installed frame. -/
noncomputable def stableRelationBasis
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    Σ rank : ℕ, Module.Basis (Fin rank) ℤ face.StableRelationCarrier := by
  letI : Fintype Generator := Fintype.ofFinite Generator
  exact Submodule.basisOfPid
    (Finsupp.basisSingleOne :
      Module.Basis Generator ℤ face.GeneratorModule)
    face.stableRelationSubmodule

/-- Perfectness is generated from the finite source envelope, Noetherian
stabilization and the PID submodule theorem.  The caller supplies none of the
eight `Module.Free/Finite` fields required by the downstream determinant
readout. -/
theorem perfectCalculation
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    RootGeneratedFourTermPerfectCalculationAt face.determinantProjection := by
  letI : Fintype Generator := Fintype.ofFinite Generator
  let generatorBasis : Module.Basis Generator ℤ face.GeneratorModule :=
    Finsupp.basisSingleOne
  let relationBasis := face.stableRelationBasis.2
  letI : Module.Free ℤ face.StableRelationCarrier :=
    Module.Free.of_basis relationBasis
  letI : Module.Finite ℤ face.StableRelationCarrier :=
    Module.Finite.of_basis relationBasis
  letI : Module.Free ℤ face.GeneratorModule :=
    Module.Free.of_basis generatorBasis
  letI : Module.Finite ℤ face.GeneratorModule :=
    Module.Finite.of_basis generatorBasis
  exact RootGeneratedFourTermPerfectCalculationAt.generate
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance

def determinantState
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    RootGeneratedFourTermPerfectDeterminantStateAt
      face.determinantProjection face.perfectCalculation :=
  RootGeneratedFourTermPerfectDeterminantStateAt.realize

theorem determinantState_has_unitTorsor
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    Nonempty
      (GradedIntegralDeterminantLine.CanonicalIntegralUnitTorsor
        face.determinantState.integralLine) :=
  ⟨face.determinantState.unitTorsor⟩

theorem preserves_source_occurrences
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    face.root = rootOccurrence ∧
      face.generators = generatorOccurrences ∧
      face.actualDiagram = diagramOccurrence.root :=
  ⟨rfl, rfl, rfl⟩

theorem factors_through_axiomFreeCore
    (face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    face.core.root = rootOccurrence ∧
      face.core.generators = generatorOccurrences ∧
      face.core.diagram = diagramOccurrence :=
  face.core.preserves_occurrences

end RootGeneratedCofinalPerfectCompressionAt

end

end CofinalPerfectCompression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
