import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootInquiryTotalRealityAdapter

/-!
# Regression: one inquiry occurrence has one typed outcome
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootInquiryTotalRealityRegression

open TotalReality
open RootInquiryCompletion
open RootInquiryTotalReality

universe u

variable
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    (state : runtime.State)

/-- Two purported realizations of the same public inquiry collapse to the
single compiler-generated occurrence. -/
theorem same_inquiry_realization_eq
    (left right :
      SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt state) :
    left = right :=
  left.eq_tick.trans right.eq_tick.symm

/-- Equality of the occurrence forces every dependent public readout to agree. -/
theorem same_inquiry_readouts_agree
    (left right :
      SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt state) :
    HEq left.answer right.answer ∧ HEq left.receipt right.receipt ∧
      left.next = right.next := by
  cases same_inquiry_realization_eq state left right
  exact ⟨HEq.rfl, HEq.rfl, rfl⟩

/-- The generic zero-law consumer rejects an unregistered outcome bit at this
exact inquiry occurrence. -/
theorem fixed_inquiry_rejects_magic
    {difference : RootInquiryTotalReality.InquiryDifference state} :
    MagicBitAt (RootInquiryTotalReality.semantics state) difference → False :=
  RootInquiryTotalReality.noMagicBit state

#print axioms SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.eq_tick
#print axioms RootInquiryTotalReality.isTotal
#print axioms RootInquiryTotalReality.noMagicBit
#print axioms same_inquiry_readouts_agree
#print axioms fixed_inquiry_rejects_magic

end RootInquiryTotalRealityRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
