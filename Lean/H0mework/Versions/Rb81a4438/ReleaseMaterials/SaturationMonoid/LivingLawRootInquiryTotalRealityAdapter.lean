import H0mework.Foundation.Semantics.RootReality
import H0mework.Foundation.Runtime.Inquiry

/-!
# Total reality at one exact inquiry occurrence

Different registered queries may generate different worlds.  At one fixed
reachable runtime state, however, answer, receipt, and successor are dependent
readouts of the unique authority-bearing occurrence type.  Raw engine
occurrences are intentionally outside this adapter.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootInquiryTotalReality

open TotalReality
open RootInquiryCompletion

universe u

variable
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    (state : runtime.State)

/-- A purported pair of realizations of one fixed inquiry occurrence. -/
abbrev InquiryDifference :=
  SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt state ×
    SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt state

/-- Inhabiting the sealed exact-occurrence type is already actuality. -/
abbrev InquiryActualityAt
    (_difference : InquiryDifference state) : Prop :=
  True

/-- Stable reference retains the engine and query in the dependent occurrence
type rather than comparing an erased answer payload. -/
abbrev InquiryStableReferenceAt
    (_difference : InquiryDifference state) : Prop :=
  True

/-- Weak difference semantics at one exact inquiry.  Distinct registered
queries are intentionally outside this fibre. -/
def semantics : RealityDifferenceSemantics where
  Difference := InquiryDifference state
  ActualAt := InquiryActualityAt state
  StableReferenceAt := InquiryStableReferenceAt state
  RealDifferenceAt := fun difference => difference.1 ≠ difference.2
  RedundantAt := fun difference => difference.1 = difference.2
  StructuralIdentityAt := fun _difference => False

/-- Same-source inquiry realizations are definitionally redundant after
canonical occurrence uniqueness; there is no second typed outcome to locate. -/
theorem realization_eq
    (difference : InquiryDifference state) :
    difference.1 = difference.2 :=
  difference.1.eq_tick.trans difference.2.eq_tick.symm

/-- Positive totality at one inquiry occurrence.  The only lawful branch is
redundancy; genuine diversity must first change the registered source/query
index. -/
theorem isTotal : TotalRealityAt (semantics state) where
  locate := fun difference _actual => Or.inl (realization_eq state difference)

/-- A caller cannot retain the same engine/query occurrence while changing
any answer, receipt, or successor readout. -/
theorem noMagicBit {difference : InquiryDifference state} :
    MagicBitAt (semantics state) difference → False :=
  (isTotal state).noMagicBit

end RootInquiryTotalReality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
