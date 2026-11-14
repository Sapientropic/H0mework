import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain
import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Native
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

open CategoryTheory CategoryTheory.Limits
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations
open CofinalRelationGeneratedComplex DerivedAdicCofiber

attribute [local instance] HasDerivedCategory.standard

namespace SourceOperationCompletion

variable {S Root NextRoot : Type} {V X : S → Type} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before middle after : Expr V X s}
variable (root : RootedAccountedUnfolding Root) (prior : Trace old before middle)
variable (nextRoot : RootedAccountedUnfolding NextRoot) (next : Trace old before after)
variable (paid : words prior <+: words next)

local notation "sourceHistory" => prefixHistory root (exposure prior)
local notation "targetHistory" => prefixHistory nextRoot (exposure next)

/-- Generate the existing derived cofiber from the actual cochain continuation. -/
def continuationDerivedCofiber :=
  RootGeneratedDerivedAdicCofiberAt.generate (rootOccurrence := root)
    (sourceOccurrence := .zero (intComplex sourceHistory))
    (targetOccurrence := .zero (intComplex targetHistory))
    (transitionOccurrence := .zero (HomologicalComplex.extendMap
      (continuationCochainMap root prior nextRoot next paid) ComplexShape.embeddingUpNat))

theorem continuation_derived_zero :
    IsZero (continuationDerivedCofiber root prior nextRoot next paid).derivedTriangle.obj₁ := by
  let map := continuationCochainMap root prior nextRoot next paid
  let equivalence := continuationCochainHomotopyEquiv root prior nextRoot next paid
  haveI quasi : QuasiIso map := equivalence.quasiIso_hom
  let face := continuationDerivedCofiber root prior nextRoot next paid
  haveI : IsIso (DerivedCategory.Q.map face.actualTransition) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _).2
      (show QuasiIso (HomologicalComplex.extendMap map ComplexShape.embeddingUpNat) from inferInstance)
  exact face.derivedCofiber_isZero_of_derivedIsIso

end SourceOperationCompletion

namespace RootGeneratedDebtActivationJointSource.OwnerFree

open SourceOperationCompletion

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {S : Type} {Value Var : S → Type} [∀ s, AddCommGroup (Value s)] {sort : S}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))
variable (runtime : Runtime old origin reader)

local notation "priorState" => runtimeCurrent old origin reader runtime
local notation "arrivedState" => runtimeCurrent old origin reader runtime.tick.next
local notation "priorRoot" => RootedAccountedUnfolding.zero runtime.emittedOccurrence
local notation "arrivedRoot" => RootedAccountedUnfolding.zero runtime.tick.next.emittedOccurrence

/-- The exact activated occurrence owns the cochain continuation and the original whole write. -/
theorem cofinal_tick_derived_write :
    IsZero (continuationDerivedCofiber priorRoot priorState.2 arrivedRoot arrivedState.2
      (tick_paid_prefix old origin reader runtime)).derivedTriangle.obj₁ ∧
      type_of% (Relations.coversAt_factorizes old origin reader runtime) ∧
      type_of% (tick_ledger old origin reader runtime) :=
  ⟨continuation_derived_zero priorRoot priorState.2 arrivedRoot arrivedState.2 (tick_paid_prefix old origin reader runtime),
    Relations.coversAt_factorizes old origin reader runtime, tick_ledger old origin reader runtime⟩

end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
