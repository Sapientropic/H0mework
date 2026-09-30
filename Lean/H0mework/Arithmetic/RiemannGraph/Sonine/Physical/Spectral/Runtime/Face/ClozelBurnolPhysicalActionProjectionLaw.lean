import H0mework.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticIntegralFixedNamedFacade
import H0mework.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Face.ClozelBurnolPhysicalActionFace

/-! # Fixed-ledger projection law for the Burnol physical action -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.BurnolPhysicalActionProjection

open CanonicalUnitArithmeticRoot
open CanonicalRiemann
open CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace

noncomputable section

abbrev BaseAuthoritySource :=
  CanonicalUnitArithmeticIntegralFixedNamedFacade.authoritySource

abbrev BaseLedgerSource :=
  BaseAuthoritySource.restructuringSource.toLedgerSource

/-- Proposition-only readout of the certified common action and its true
multiplicative compression. -/
structure SourceGeneratedBurnolPhysicalActionReadout : Type where
  private mk ::
  analyticProjects :
    generatedBurnolThetaCommonActionReceiptOccurrence.map Sigma.fst =
      generatedRiemannAnalyticContinuationOccurrence
  actionRead :
    generatedBurnolThetaCommonActionReceiptOccurrence.root.2.action =
      AllPlaceOriginDefect.ownerArithmeticCounterterm
        generatedBurnolThetaCommonActionReceiptOccurrence.root.1.1
  thetaActionCommutes : GaussianActionCommutingAt
    generatedBurnolThetaCommonActionReceiptOccurrence.root.2.action
    generatedBurnolThetaCommonActionReceiptOccurrence.root.1.2.thetaPair.pair
  physicalStateRead : burnolPhysicalActionState =
    generatedBurnolThetaCommonActionReceiptOccurrence.root.2.fixedState
  physicalStateNonzero : burnolPhysicalActionState ≠ 0
  compressionSymmetric : ∀ left right,
    inner ℂ (burnolPhysicalActionCompression left) right =
      inner ℂ left (burnolPhysicalActionCompression right)
  compressionContractive : ∀ state,
    ‖burnolPhysicalActionCompression state‖ ≤ ‖state‖

def sourceGeneratedBurnolPhysicalActionReadout :
    SourceGeneratedBurnolPhysicalActionReadout where
  analyticProjects :=
    generatedBurnolThetaCommonActionReceiptOccurrence_projects
  actionRead :=
    generatedBurnolThetaCommonActionReceiptOccurrence.root.2.action_eq
  thetaActionCommutes :=
    generatedBurnolThetaCommonActionReceiptOccurrence.root.2.gaussianActionRead
  physicalStateRead := rfl
  physicalStateNonzero := burnolPhysicalActionState_ne_zero
  compressionSymmetric := burnolPhysicalActionCompression_symmetric
  compressionContractive := burnolPhysicalActionCompression_contractive

instance : Subsingleton SourceGeneratedBurnolPhysicalActionReadout := by
  constructor
  intro left right
  cases left
  cases right
  rfl

/-- This component lives over the same fixed ledger source as the existing
analytic projection. -/
def projectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (current = initialCurrent)
  InactiveAt := fun _ {current} _occurrence => PLift (current ≠ initialCurrent)
  classify := by
    intro _ current _occurrence
    classical
    by_cases initial : current = initialCurrent
    · exact .inl ⟨initial⟩
    · exact .inr ⟨initial⟩
  PayloadAt := fun _ {_current} _occurrence _active =>
    SourceGeneratedBurnolPhysicalActionReadout
  project := fun _ {_current} _occurrence _active =>
    sourceGeneratedBurnolPhysicalActionReadout

end
end NoIslandNoMagic.BurnolPhysicalActionProjection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
