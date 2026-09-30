import H0mework.Foundation.Semantics.RootReality
import H0mework.Arithmetic.PrimeShadow.LivingLawRootAnswerNextHistoryRegression

/-!
# Regression: total reality excludes a root-external magic bit

The abstract implication chain and its causally closed root realization remain
constructive.  The root instance derives structural identity from exact
registered occurrences; no caller supplies a no-magic premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootTotalRealityRegression

open TotalReality
open ZeroLawRootAdmission
open RootTotalReality

universe u

variable
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V)

/-- A real root-state difference generates positive structural identity. -/
theorem actual_difference_has_structural_identity
    {difference : RootDifference root}
    (different : difference.1 ≠ difference.2) :
    (semantics root).StructuralIdentityAt difference :=
  LawfulWorldStateAt.registeredOccurrence_ne_of_ne different

/-- A same-occurrence wrapper bit cannot become a root difference. -/
theorem same_registered_occurrence_not_real_difference
    {left right : LawfulWorldStateAt root}
    (same : left.registeredOccurrence = right.registeredOccurrence) :
    ¬(left ≠ right) := by
  intro different
  exact different (LawfulWorldStateAt.eq_of_registeredOccurrence_eq same)

/-- The complete non-circular derivation at the root. -/
theorem root_rejects_magic
    {difference : RootDifference root} :
    MagicBitAt (semantics root) difference -> False :=
  noMagicBit root

#print axioms MagicBitAt.toExternalSupplement
#print axioms TotalRealityAt.noExternalSupplement
#print axioms TotalRealityAt.noMagicBit
#print axioms actualDifference
#print axioms isTotal
#print axioms noExternalSupplement
#print axioms noMagicBit
#print axioms actual_difference_has_structural_identity
#print axioms same_registered_occurrence_not_real_difference
#print axioms root_rejects_magic

/-! ## Heterogeneous living-process totality -/

open RootProcessTotalReality

private abbrev livingProcess := RootAnswerNextHistoryRegression.process

/-- The first source-process transition crosses a genuine local terminal into
the existing native-write root.  The two states are nevertheless distinguished
by their complete registered living currents, not by a global-stop bit. -/
theorem local_terminal_handoff_has_structural_identity :
    (RootProcessTotalReality.semantics livingProcess).StructuralIdentityAt
      (none, some 0) :=
  RootProcessTotalReality.registeredCurrent_ne_of_ne livingProcess (by
    intro equality
    cases equality)

/-- Total reality remains constructive across the heterogeneous root handoff;
the local terminal is an answer inside one continuing source process. -/
theorem living_process_rejects_magic :
    MagicBitAt (RootProcessTotalReality.semantics livingProcess)
        (none, some 0) -> False :=
  RootProcessTotalReality.noMagicBit livingProcess

#print axioms RootProcessTotalReality.isTotal
#print axioms RootProcessTotalReality.noMagicBit
#print axioms local_terminal_handoff_has_structural_identity
#print axioms living_process_rejects_magic

end RootTotalRealityRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
