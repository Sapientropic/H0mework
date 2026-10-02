import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Consumer
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Authority

/-! The old identity scope is extracted from this actual source's existing
certificate, before the registered request adds its next mathematical row. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open DebtActivationWorld

noncomputable section
variable (runtime : LivingRuntimeState process)

theorem oldOpenSubsingleton (support : (NewN runtime).Support)
    (responsibility : (NewN runtime).Responsibility) :
    Subsingleton ((NewN runtime).OpenAt support responsibility) := by
  rcases support with ⟨old, state⟩
  cases responsibility with
  | inl oldResponsibility =>
      constructor
      rintro ⟨left⟩ ⟨right⟩
      rfl
  | inr debt =>
      cases state with
      | none => exact ⟨fun impossible => nomatch impossible⟩
      | some state =>
          constructor
          rintro ⟨⟨left⟩⟩ ⟨⟨right⟩⟩
          rfl

def oldCertificate (oldCurrent : Joint.Current (SourcePhysicalCalculationAdmission.registered runtime)) :
    ExactLedgerRestructuringCertificationAt
      (identityOnlyWorldLedgerRestructuringLaw (lower runtime).source.source PUnit.unit
        (oldOpenSubsingleton runtime))
      ((lower runtime).emitted oldCurrent) ((program runtime).emit oldCurrent).evolution := by
  let original := (targetRoot runtime).source.base.restructuringSource.compiler
  have paid := original.certifyRestructuring ((lower runtime).emitted oldCurrent)
  have branch := ((program runtime).emit oldCurrent).generated_eq
  exact Eq.mp (congrArg (fun generated =>
    SourceNativeLedgerRestructuringCertificationAt original.restructuringLaw generated) branch) paid

theorem oldOrigin_injective (oldCurrent : Joint.Current (SourcePhysicalCalculationAdmission.registered runtime)) :
    Function.Injective (fun entry => (((program runtime).emit oldCurrent).evolution.origin entry).1) :=
  RootGeneratedDebtActivationJointSource.Native.Identity.origin_injective PUnit.unit
    (oldOpenSubsingleton runtime) (oldCertificate runtime oldCurrent)

theorem oldDestination_injective (oldCurrent : Joint.Current (SourcePhysicalCalculationAdmission.registered runtime)) :
    Function.Injective (fun entry => (((program runtime).emit oldCurrent).evolution.destination entry).1) :=
  RootGeneratedDebtActivationJointSource.Native.Identity.destination_injective PUnit.unit
    (oldOpenSubsingleton runtime) (oldCertificate runtime oldCurrent)

def oldProjectionLaw : SourceNativeProjectionLaw (lower runtime).source :=
  (targetRoot runtime).source.base.projectionLaw

def identityScope : RootGeneratedDebtActivationJointSource.Native.IdentityScope (program runtime) where
  defaultAnchor := PUnit.unit
  openAt_subsingleton := oldOpenSubsingleton runtime
  certify := oldCertificate runtime

variable (depth : Nat)

def authoritySource := RootGeneratedDebtActivationJointSource.Native.authoritySource
  (program runtime) (registered runtime depth) (identityScope runtime) (oldProjectionLaw runtime)

def authoritativeRoot := RootGeneratedDebtActivationJointSource.Native.authoritativeRoot
  (program runtime) (registered runtime depth) (identityScope runtime) (oldProjectionLaw runtime)

def livingRoot := RootGeneratedDebtActivationJointSource.Native.livingRoot
  (program runtime) (registered runtime depth) (identityScope runtime) (oldProjectionLaw runtime)

theorem living_ledger : (livingRoot runtime depth).toAuthoritativeRoot.toLedgerRoot = jointRoot runtime depth := rfl

theorem living_original_family (projection : (targetRoot runtime).source.base.projectionLaw.Projection) :
    HEq ((livingRoot runtime depth).source.base.projectionLaw.outcomeAt (.inl projection)
      (jointOccurrence runtime depth))
      ((targetRoot runtime).source.base.projectionLaw.outcomeAt projection (occurrence runtime depth)) :=
  joint_original_projection runtime depth projection

end
end SourcePhysicalCalculationAdmission.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
