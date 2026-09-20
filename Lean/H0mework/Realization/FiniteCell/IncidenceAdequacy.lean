import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import H0mework.Realization.FiniteCell.FrontierCompression

/-!
# Source-generated finite atom incidence adequacy

This file is one genuine nonzero sufficient producer for the canonical
finite-frontier classifier.  A finite occurrence of actual graded atoms
generates its frontier from the occurrence trace.  The engine then calculates,
rather than accepts, two conditions:

* the finite atoms span every actual degree carrier;
* the frontier contains every nonzero differential image needed by the
  canonical lifted differential.

On that branch `kernel → free → actual` is degreewise short exact.  Mathlib's
mapping-cone theorem generates a quasi-isomorphism from the already generated
finite bounded candidate to the actual complex, hence a zero derived
mapping-cofiber residual and an adequate-frontier token.

No frontier, finite envelope, differential closure, candidate,
quasi-isomorphism, perfectness, basis, or determinant is submitted by the
domain caller.  This is deliberately only a sufficient restriction:
derived-perfect complexes can have huge degree carriers and no finite
degreewise spanning trace.  Absence of such a trace does not obstruct the
general relation/history/cofiber compression routes.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace FiniteAtomIncidenceAdequacy

open CategoryTheory
open CategoryTheory.Limits
open CanonicalFiniteFrontierCompression
open CanonicalFiniteFrontierCompression.RootGeneratedCanonicalFiniteFrontierCompressionAt
open DerivedAdicCofiber

noncomputable section

universe w

attribute [local instance] HasDerivedCategory.standard

/-- Short complex resolved by the generated kernel and evaluation maps. -/
noncomputable def stageShortComplex
    {complex : IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex)
    (coverage : GeneratedDifferentialCoverageAt frontier) :
    ShortComplex (IntegralCochainComplex ℤ) :=
  ShortComplex.mk (stageKernelInclusion frontier coverage)
    (stageEvaluationMap frontier coverage)
    (stageKernelInclusion_comp_evaluation frontier coverage)

def DegreewiseSpansActualCarrier
    {complex : IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex) : Prop :=
  ∀ degree, Function.Surjective (stageEvaluation frontier degree)

theorem stageShortComplex_shortExact
    {complex : IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex)
    (coverage : GeneratedDifferentialCoverageAt frontier)
    (spans : DegreewiseSpansActualCarrier frontier) :
    (stageShortComplex frontier coverage).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro degree
  apply ModuleCat.shortComplex_shortExact
  · exact (stageEvaluation frontier degree).exact_subtype_ker_map
  · exact (LinearMap.ker
      (stageEvaluation frontier degree)).injective_subtype
  · exact spans degree

theorem finitePerfectCandidateMap_eq_descShortComplex
    {complex : IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex)
    (coverage : GeneratedDifferentialCoverageAt frontier) :
    finitePerfectCandidateMap frontier coverage =
      CochainComplex.mappingCone.descShortComplex
        (stageShortComplex frontier coverage) :=
  rfl

theorem candidateMap_quasiIso_of_degreewiseSpans
    {complex : IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex)
    (coverage : GeneratedDifferentialCoverageAt frontier)
    (spans : DegreewiseSpansActualCarrier frontier) :
    QuasiIso (finitePerfectCandidateMap frontier coverage) := by
  rw [finitePerfectCandidateMap_eq_descShortComplex]
  exact CochainComplex.mappingCone.quasiIso_descShortComplex
    (stageShortComplex_shortExact frontier coverage spans)

/-- One finite occurrence of actual graded atoms.  The frontier is generated
from its trace; this face is subordinate to the owning global/root face. -/
structure RootGeneratedFiniteAtomIncidenceAt
    {Root : Type w}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {actualComplexOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
      rootOccurrence actualComplexOccurrence)
    (atomOccurrence : RootedAccountedUnfolding
      (ActualCochainAtomAt compression.actualComplex)) : Type w where
  private mk ::

namespace RootGeneratedFiniteAtomIncidenceAt

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualComplexOccurrence : RootedAccountedUnfolding
  (IntegralCochainComplex ℤ)}
variable {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
  rootOccurrence actualComplexOccurrence}
variable {atomOccurrence : RootedAccountedUnfolding
  (ActualCochainAtomAt compression.actualComplex)}

local instance :
    DecidableEq (ActualCochainAtomAt compression.actualComplex) :=
  Classical.decEq _

def generate : RootGeneratedFiniteAtomIncidenceAt
    compression atomOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence) :=
  compression.root

/-- Intrinsic frontier generated from the actual occurrence trace. -/
noncomputable def frontier
    (_face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence) :
    CanonicalFiniteFrontierAt compression.actualComplex := by
  classical
  exact atomOccurrence.trace.toFinset

def AdequacyCalculation
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence) : Prop :=
  DegreewiseSpansActualCarrier face.frontier ∧
    DifferentialCoveredAt face.frontier

structure GeneratedAdequacyCalculationAt
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence) : Type w where
  private mk ::
  calculation : face.AdequacyCalculation

structure FiniteAtomIncidenceObstructionAt
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence) : Type w where
  private mk ::
  persists : ¬ face.AdequacyCalculation

abbrev CalculationOutcome
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence) :=
  Sum (GeneratedAdequacyCalculationAt face)
    (FiniteAtomIncidenceObstructionAt face)

/-- Caller-free calculation of spanning and differential closure. -/
noncomputable def settle
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence) : CalculationOutcome face := by
  classical
  by_cases adequate : face.AdequacyCalculation
  · exact Sum.inl ⟨adequate⟩
  · exact Sum.inr ⟨adequate⟩

noncomputable def differentialCoverage
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence)
    (calculation : GeneratedAdequacyCalculationAt face) :
    GeneratedDifferentialCoverageAt face.frontier := by
  cases settleDifferentialCoverage face.frontier with
  | inl coverage => exact coverage
  | inr obstruction =>
      exact False.elim
        (obstruction.notCovered calculation.calculation.2)

theorem candidateMap_quasiIso
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence)
    (calculation : GeneratedAdequacyCalculationAt face) :
    QuasiIso (finitePerfectCandidateMap face.frontier
      (face.differentialCoverage calculation)) :=
  candidateMap_quasiIso_of_degreewiseSpans face.frontier
    (face.differentialCoverage calculation) calculation.calculation.1

theorem derivedResidualVanishes
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence)
    (calculation : GeneratedAdequacyCalculationAt face) :
    compression.DerivedResidualVanishes face.frontier
      (face.differentialCoverage calculation) := by
  let derivedIso : IsIso (DerivedCategory.Q.map
      (finitePerfectCandidateMap face.frontier
        (face.differentialCoverage calculation))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat ℤ) _).2
      (face.candidateMap_quasiIso calculation)
  letI : IsIso (DerivedCategory.Q.map
      (compression.derivedFace face.frontier
        (face.differentialCoverage calculation)).actualTransition) := by
    change IsIso (DerivedCategory.Q.map
      (finitePerfectCandidateMap face.frontier
        (face.differentialCoverage calculation)))
    exact derivedIso
  exact (compression.derivedFace face.frontier
    (face.differentialCoverage calculation)
      ).derivedCofiber_isZero_of_derivedIsIso

/-- Genuine source-generated positive frontier from the actual atom trace. -/
noncomputable def adequateFrontier
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence)
    (calculation : GeneratedAdequacyCalculationAt face) :
    ClassifiedAdequateFrontierAt compression := by
  cases compression.settle with
  | inl settlement => exact settlement
  | inr obstruction =>
      exact False.elim
        (obstruction.persists face.frontier
          (face.differentialCoverage calculation)
          (face.derivedResidualVanishes calculation))

theorem preserves_source_trace_and_global_complex
    (face : RootGeneratedFiniteAtomIncidenceAt
      compression atomOccurrence) :
    face.root = compression.root ∧
      face.frontier = atomOccurrence.trace.toFinset ∧
      compression.actualComplex = actualComplexOccurrence.root :=
  ⟨rfl, rfl, rfl⟩

end RootGeneratedFiniteAtomIncidenceAt

end


end FiniteAtomIncidenceAdequacy
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
