import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptBlockProjectionSource

/-!
# One projection coface of the original unit root

The added block coordinate and all three inherited faces use the original
source, event inventory, ledger compiler, law surface and exact occurrence.
The named runtime follows the same generated unit-history successor.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitBlockProjectionCoface

open ArithmeticGeneration
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitNativeReceiptFactorization
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead

noncomputable section

def authoritySource :=
  authoritativeRoot.source.withProjectionCoface blockComponent

def blockInstallation :
    SourceNativeProjectionLaw.InstallationAt blockComponent
      authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    authoritativeRoot.source blockComponent

def inheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt
      authoritativeRoot.source.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    authoritativeRoot.source blockComponent

def authoritativeCoface : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := authoritativeRoot.emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

def livingCoface : SourceNativeLivingRootClosure N V :=
  authoritativeCoface.toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem same_source_ledger_and_law :
    authoritySource.restructuringSource = authoritativeRoot.source.restructuringSource ∧
      authoritySource.eventInventoryAdmission =
        authoritativeRoot.source.eventInventoryAdmission ∧
      authoritySource.lawSurface = authoritativeRoot.source.lawSurface ∧
      (∀ current, authoritativeCoface.toLedgerRoot.generatedLedgerAt current =
        authoritativeRoot.toLedgerRoot.generatedLedgerAt current) :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

def finiteVisit : Nat → RootVisit authoritativeCoface.toRoot
  | 0 => authoritativeCoface.toRoot.initialVisit
  | depth + 1 => (finiteVisit depth).next rfl

def temporalVisit (depth : Nat) :
    SourceNativeTemporalVisitAt authoritativeCoface.toLedgerRoot :=
  .finite (finiteVisit depth)

theorem temporalVisit_depth (depth : Nat) :
    temporalDepth? ⟨V, livingCoface, temporalVisit depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change some (ProductiveFiniteRootHistoryAt.causalDepth
        (finiteVisit depth).history + 1) = some (depth + 1)
      have hprior : ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit depth).history = depth := by
        change some (ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit depth).history) = some depth at ih
        exact Option.some.inj ih
      rw [hprior]

def process : SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth => ⟨V, livingCoface, temporalVisit depth⟩
  stateAt_injective := by
    intro left right equality
    have hdepth := congrArg temporalDepth? equality
    rw [temporalVisit_depth left, temporalVisit_depth right] at hdepth
    exact Option.some.inj hdepth
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

abbrev Face := SourceNativeProjectionCoface FacadeFace PUnit

def facade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _ => Face
  componentAt := fun runtime face =>
    match face with
    | .component _ => blockComponent
    | .inherited oldFace =>
        runtimeFacade.componentAt (runtimeAt runtime.state) oldFace
  installationAt := fun runtime face =>
    match face with
    | .component _ => blockInstallation
    | .inherited oldFace =>
        (runtimeFacade.installationAt (runtimeAt runtime.state) oldFace).trans
          inheritedInstallation
  projectionAt := fun runtime face =>
    match face with
    | .component projection => projection
    | .inherited oldFace =>
        runtimeFacade.projectionAt (runtimeAt runtime.state) oldFace

def seed : LivingRuntimeState process := facade.seed

def runtimeAtCoface (stage : Nat) : LivingRuntimeState process := seed.advance stage

theorem same_current (stage : Nat) :
    (runtimeAtCoface stage).current.visit.current =
      (runtimeAt stage).current.visit.current := by
  induction stage with
  | zero => rfl
  | succ stage ih =>
      change next (runtimeAtCoface stage).current.visit.current =
        next (runtimeAt stage).current.visit.current
      exact congrArg next ih

theorem emitted_same_at_current (current : Current) :
    authoritativeCoface.emitted current = authoritativeRoot.emitted current :=
  rfl

end
end CanonicalUnitBlockProjectionCoface
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
