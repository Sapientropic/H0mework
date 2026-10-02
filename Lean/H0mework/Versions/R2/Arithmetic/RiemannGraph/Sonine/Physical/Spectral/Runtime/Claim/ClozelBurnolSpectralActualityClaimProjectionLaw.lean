import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticIntegralFixedNamedFacade
import H0mework.Versions.R2.Foundation.Responsibility.PendingClaimBirth
import H0mework.Versions.R2.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Debt.ClozelBurnolSpectralActualityDebt

/-!
# Fixed-ledger dependent projection for spectral actuality

One nontrivial zero fibre of the fixed generated zeta function selects a
dependent projection.  Its package fixes the zero-field actuality claim,
pending state and positive debt clock together; neither a spectral landing
nor its settlement is stored here.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace SpectralActuality

open CanonicalUnitArithmeticRoot
open PendingClaimBirth SpectralActualityDebt

noncomputable section

abbrev BaseAuthoritySource :=
  CanonicalUnitArithmeticIntegralFixedNamedFacade.authoritySource

abbrev BaseLedgerSource :=
  BaseAuthoritySource.restructuringSource.toLedgerSource

/-- Projection coordinate for one dependent event fibre of the fixed analytic
source.  The proofs occur in the projection request, never in the source
payload. -/
structure ProjectionAt : Type where
  coordinate : ℂ
  zero : generatedRiemannZeta AnalyticOwner coordinate = 0
  nontrivial : NontrivialZeroTag coordinate
  event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial

noncomputable instance : DecidableEq ProjectionAt := Classical.decEq _

def ProjectionAt.generate
    (coordinate : ℂ)
    (zero : generatedRiemannZeta AnalyticOwner coordinate = 0)
    (nontrivial : NontrivialZeroTag coordinate) : ProjectionAt where
  coordinate := coordinate
  zero := zero
  nontrivial := nontrivial
  event := GeneratedNontrivialZeroEventAt.generate coordinate zero nontrivial

/-- The dependent claim package is active only at the fixed initial analytic
occurrence.  The strong projection fixes its debt law definitionally, so no
external mapper can replace the semantic claim. -/
def spectralActualityPendingClaimProjectionLaw :
    SourceNativePendingClaimProjectionLaw BaseLedgerSource where
  Projection := ProjectionAt
  ActiveAt := fun _ {current} _occurrence => PLift (current = initialCurrent)
  InactiveAt := fun _ {current} _occurrence => PLift (current ≠ initialCurrent)
  classify := by
    intro _ current _occurrence
    classical
    by_cases initial : current = initialCurrent
    · exact .inl ⟨initial⟩
    · exact .inr ⟨initial⟩
  lawAt := fun projection {_current} _occurrence _active =>
    SpectralActualityDebt.activationLaw projection.event
  project := fun _projection {_current} _occurrence _active =>
    { initial := SpectralActualityDebt.StateAt.pending
      initialBudget_positive := Nat.zero_lt_one }

abbrev spectralActualityProjectionLaw :
    SourceNativeProjectionLaw BaseLedgerSource :=
  spectralActualityPendingClaimProjectionLaw.toProjectionLaw

def projectionPackage (projection : ProjectionAt) :
  SourceGeneratedPendingClaimPackage
      (SpectralActualityDebt.activationLaw projection.event) :=
  spectralActualityPendingClaimProjectionLaw.project projection
    (CanonicalUnitArithmeticRoot.emitted initialCurrent) ⟨rfl⟩

theorem projectionPackage_claim (projection : ProjectionAt) :
    (SpectralActualityDebt.activationLaw projection.event).debtClaim =
      SpectralActualityClaimAt.generate projection.event :=
  SpectralActualityDebt.activationLaw_claim_eq_generated projection.event

end
end SpectralActuality
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
