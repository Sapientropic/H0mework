import H0mework.Realization.FiniteCell.FrontierCompression
import H0mework.Realization.FiniteCell.CofiberContraction

/-!
# Finite-atom derived-cofiber adequacy

A finite trace of actual graded atoms need not span any raw degree carrier.
The generic engine closes that trace under the actual differential, builds
the canonical bounded finite-free candidate, and reads the candidate's
generated mapping cocone.  If the source also exposes a raw degree `-1`
residual cochain, the framework calculates `δh = 𝟙`; that generated equation,
not degreewise surjectivity, produces the positive adequate-frontier token.

This is a genuine non-degreewise cofiber route.  It remains a sufficient
restriction: an acyclic residual need not be contractible, and a general
derived-perfect realization need not start from a finite atom trace.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace FiniteAtomDerivedCofiberAdequacy

open CategoryTheory
open CochainComplex.HomComplex
open CanonicalFiniteFrontierCompression
open CanonicalFiniteFrontierCompression.RootGeneratedCanonicalFiniteFrontierCompressionAt
open DerivedAdicCofiber
open DerivedCofiberContraction
open DerivedCofiberContraction.RootGeneratedDerivedCofiberContractionAt

noncomputable section

universe w

attribute [local instance] HasDerivedCategory.standard

/-- The actual successor differential image of one graded atom. -/
noncomputable def successorAtom
    {complex : IntegralCochainComplex ℤ}
    (atom : ActualCochainAtomAt complex) :
    ActualCochainAtomAt complex :=
  ⟨atom.degree + 1,
    complex.d atom.degree (atom.degree + 1) atom.value⟩

theorem successorAtom_differential_zero
    {complex : IntegralCochainComplex ℤ}
    (atom : ActualCochainAtomAt complex) :
    complex.d (successorAtom atom).degree
      ((successorAtom atom).degree + 1) (successorAtom atom).value = 0 := by
  dsimp [successorAtom]
  have squareZero := ConcreteCategory.congr_hom
    (complex.d_comp_d atom.degree (atom.degree + 1)
      ((atom.degree + 1) + 1)) atom.value
  change complex.d (atom.degree + 1) ((atom.degree + 1) + 1)
    (complex.d atom.degree (atom.degree + 1) atom.value) = 0 at squareZero
  exact squareZero

/-- One differential step suffices: the next step is zero by `d² = 0`. -/
noncomputable def differentialClosure
    {complex : IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex) :
    CanonicalFiniteFrontierAt complex := by
  classical
  exact frontier ∪ (frontier.image successorAtom).filter
    (fun atom => atom.value ≠ 0)

theorem differentialClosure_covered
    {complex : IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex) :
    DifferentialCoveredAt (differentialClosure frontier) := by
  classical
  intro source target related generator
  dsimp only
  intro imageNonzero
  rcases generator with ⟨⟨atom, atomMem⟩, degreeEq⟩
  subst source
  change atom.degree + 1 = target at related
  subst target
  change complex.d atom.degree (atom.degree + 1) atom.value ≠ 0 at imageNonzero
  change (⟨atom.degree + 1,
    complex.d atom.degree (atom.degree + 1) atom.value⟩ :
      ActualCochainAtomAt complex) ∈ differentialClosure frontier
  rcases Finset.mem_union.mp atomMem with original | generated
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨atom, original, rfl⟩, imageNonzero⟩
  · rcases Finset.mem_image.mp (Finset.mem_filter.mp generated).1 with
      ⟨predecessor, predecessorMem, predecessorEq⟩
    exfalso
    apply imageNonzero
    rw [← predecessorEq]
    exact successorAtom_differential_zero predecessor

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualComplexOccurrence : RootedAccountedUnfolding
  (IntegralCochainComplex ℤ)}
variable {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
  rootOccurrence actualComplexOccurrence}
variable {atomOccurrence : RootedAccountedUnfolding
  (ActualCochainAtomAt compression.actualComplex)}

local instance : DecidableEq
    (ActualCochainAtomAt compression.actualComplex) :=
  Classical.decEq _

/-- Intrinsic finite frontier: actual atom trace plus all its differential
images. -/
noncomputable def traceDifferentialFrontier :
    CanonicalFiniteFrontierAt compression.actualComplex :=
  differentialClosure atomOccurrence.trace.toFinset

/-- Differential coverage is generated from `d² = 0`; it is not a caller
premise. -/
noncomputable def traceDifferentialCoverage :
    GeneratedDifferentialCoverageAt
      (traceDifferentialFrontier (compression := compression)
        (atomOccurrence := atomOccurrence)) := by
  let frontier := traceDifferentialFrontier (compression := compression)
    (atomOccurrence := atomOccurrence)
  cases settleDifferentialCoverage frontier with
  | inl coverage => exact coverage
  | inr obstruction =>
      exact False.elim
        (obstruction.notCovered (differentialClosure_covered _))

noncomputable def traceDerivedFace :=
  compression.derivedFace
    (traceDifferentialFrontier (compression := compression)
      (atomOccurrence := atomOccurrence))
    (traceDifferentialCoverage (compression := compression)
      (atomOccurrence := atomOccurrence))

/-- Cofiber route indexed by a raw degree `-1` residual cochain.  No spanning,
homotopy, quasi-isomorphism, or residual-zero proposition is an input. -/
structure RootGeneratedFiniteAtomDerivedCofiberAdequacyAt
    (compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
      rootOccurrence actualComplexOccurrence)
    (atomOccurrence : RootedAccountedUnfolding
      (ActualCochainAtomAt compression.actualComplex))
    (cochainOccurrence : RootedAccountedUnfolding
      (Cochain
        (traceDerivedFace (compression := compression)
          (atomOccurrence := atomOccurrence)).cofiberComplex
        (traceDerivedFace (compression := compression)
          (atomOccurrence := atomOccurrence)).cofiberComplex (-1))) : Type w where
  private mk ::

namespace RootGeneratedFiniteAtomDerivedCofiberAdequacyAt

variable {cochainOccurrence : RootedAccountedUnfolding
  (Cochain
    (traceDerivedFace (compression := compression)
      (atomOccurrence := atomOccurrence)).cofiberComplex
    (traceDerivedFace (compression := compression)
      (atomOccurrence := atomOccurrence)).cofiberComplex (-1))}

def generate : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
    atomOccurrence cochainOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence) :=
  compression.root

def frontier
    (_face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence) :=
  traceDifferentialFrontier (compression := compression)
    (atomOccurrence := atomOccurrence)

def coverage
    (_face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence) :=
  traceDifferentialCoverage (compression := compression)
    (atomOccurrence := atomOccurrence)

def derivedFace
    (_face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence) :=
  traceDerivedFace (compression := compression)
    (atomOccurrence := atomOccurrence)

def contractionFace
    (face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence) :
    RootGeneratedDerivedCofiberContractionAt face.derivedFace
      cochainOccurrence :=
  RootGeneratedDerivedCofiberContractionAt.generate

theorem derivedResidualVanishes
    (face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence)
    (calculation : GeneratedCofiberContractionCalculationAt
      face.contractionFace) :
    compression.DerivedResidualVanishes face.frontier face.coverage :=
  face.contractionFace.derivedCofiberVanishes calculation

/-- A generated positive contraction calculation forces the canonical
classifier into its positive branch. -/
noncomputable def adequateFrontier
    (face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence)
    (calculation : GeneratedCofiberContractionCalculationAt
      face.contractionFace) :
    ClassifiedAdequateFrontierAt compression := by
  cases compression.settle with
  | inl settlement => exact settlement
  | inr obstruction =>
      exact False.elim
        (obstruction.persists face.frontier face.coverage
          (face.derivedResidualVanishes calculation))

noncomputable def globalSettlement
    (face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence)
    (calculation : GeneratedCofiberContractionCalculationAt
      face.contractionFace) :=
  compression.classifiedGlobalSettlement
    (face.adequateFrontier calculation)

theorem preserves_source_trace_and_actual_complex
    (face : RootGeneratedFiniteAtomDerivedCofiberAdequacyAt compression
      atomOccurrence cochainOccurrence) :
    face.root = compression.root ∧
      face.frontier = differentialClosure atomOccurrence.trace.toFinset ∧
      compression.actualComplex = actualComplexOccurrence.root ∧
      face.contractionFace.actualCochain = cochainOccurrence.root :=
  ⟨rfl, rfl, rfl, rfl⟩

end RootGeneratedFiniteAtomDerivedCofiberAdequacyAt

end

end FiniteAtomDerivedCofiberAdequacy
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
