import H0mework.Versions.Rb81a4438.Realization.Completion.ComplexInstallation

/-!
# Explicit coordinates for a derived cofinal residual

The cofinal cochain classifier already distinguishes a settled presentation
from a nonzero derived mapping cofiber.  A proposition `¬ IsZero` is useful
but is not yet a transportable residual.  This file turns that exact branch
into a canonical categorical coordinate: the identity endomorphism of the
generated residual object.  It is not a caller-selected probe or a hidden
scalar; its source, target, and non-vanishing proof are all read from the
same derived mapping cofiber.

The resulting two-way disposition is deliberately local to the derived
residual.  It does not claim that every source is perfect, and it does not
turn a nonzero residual into a terminal failure.  The source-installed
cochain face below lifts the coordinate into its full five-way settlement,
preserving the existing whole-ledger write-back and generated next.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPresentedComplexDerivedResidualCoordinate

open CategoryTheory
open CategoryTheory.Limits
open CofinalPresentedComplex
open CofinalPresentedComplex.RootGeneratedCofinalPresentedComplexDiagramAt
open CofinalPresentedComplexSettlementFace
open CofinalPresentedComplexSettlementFace.RootGeneratedCofinalPresentedComplexSettlementStepAt
open DerivedAdicCofiber

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u w

/-! ## A canonical coordinate of a nonzero derived object -/

structure GeneratedDerivedResidualCoordinateAt
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
    (obstruction : GeneratedDerivedResidualObstructionAt
      diagram closure laws soundness) : Type (max w 2) where
  private mk ::
  probe : DerivedCategory (ModuleCat.{0} ℤ)
  coordinate : probe ⟶
    (diagram.derivedFace closure laws soundness).derivedTriangle.obj₁
  coordinate_eq_identity : probe =
    (diagram.derivedFace closure laws soundness).derivedTriangle.obj₁
  coordinate_ne_zero : coordinate ≠ 0

namespace GeneratedDerivedResidualCoordinateAt

variable {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualCochainOccurrence : RootedAccountedUnfolding
  (IntegralCochainComplex ℤ)}
variable {diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
  rootOccurrence actualCochainOccurrence}
variable {closure : GeneratedDifferentialClosureAt diagram}
variable {laws : GeneratedCompletionLawsAt diagram closure}
variable {soundness : GeneratedDegreewiseRelationSoundnessAt diagram}
variable {obstruction : GeneratedDerivedResidualObstructionAt
  diagram closure laws soundness}

theorem probe_eq_residual
    (coordinate : GeneratedDerivedResidualCoordinateAt
      diagram closure laws soundness obstruction) :
    coordinate.probe =
      (diagram.derivedFace closure laws soundness).derivedTriangle.obj₁ :=
  coordinate.coordinate_eq_identity

theorem coordinate_nonzero
    (coordinate : GeneratedDerivedResidualCoordinateAt
      diagram closure laws soundness obstruction) :
    coordinate.coordinate ≠ 0 :=
  coordinate.coordinate_ne_zero

end GeneratedDerivedResidualCoordinateAt

/-- The identity of a nonzero generated residual is itself nonzero. -/
noncomputable def derivedResidualCoordinate
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    {diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence}
    {closure : GeneratedDifferentialClosureAt diagram}
    {laws : GeneratedCompletionLawsAt diagram closure}
    {soundness : GeneratedDegreewiseRelationSoundnessAt diagram}
    (obstruction : GeneratedDerivedResidualObstructionAt
      diagram closure laws soundness) :
    GeneratedDerivedResidualCoordinateAt
      diagram closure laws soundness obstruction := by
  let residual :=
    (diagram.derivedFace closure laws soundness).derivedTriangle.obj₁
  have identity_ne_zero : (𝟙 residual) ≠ 0 := by
    intro identity_zero
    apply obstruction.persists
    exact (CategoryTheory.Limits.IsZero.iff_id_eq_zero residual).mpr identity_zero
  exact ⟨residual, 𝟙 residual, rfl, identity_ne_zero⟩

theorem derivedResidualCoordinate_nonzero
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    {diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence}
    {closure : GeneratedDifferentialClosureAt diagram}
    {laws : GeneratedCompletionLawsAt diagram closure}
    {soundness : GeneratedDegreewiseRelationSoundnessAt diagram}
    (obstruction : GeneratedDerivedResidualObstructionAt
      diagram closure laws soundness) :
    (derivedResidualCoordinate obstruction).coordinate ≠ 0 :=
  (derivedResidualCoordinate obstruction).coordinate_ne_zero

/-! ## Total local disposition -/

inductive DerivedResidualDispositionOutcome
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) : Type (max w 2) where
  | zero (receipt : GeneratedDerivedResidualZeroAt diagram closure laws soundness)
  | residual (obstruction : GeneratedDerivedResidualObstructionAt
      diagram closure laws soundness)
      (coordinate : GeneratedDerivedResidualCoordinateAt
        diagram closure laws soundness obstruction)

noncomputable def settleWithCoordinate
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) :
    DerivedResidualDispositionOutcome diagram closure laws soundness := by
  cases diagram.settleDerivedResidual closure laws soundness with
  | inl receipt => exact .zero receipt
  | inr obstruction =>
      exact .residual obstruction (derivedResidualCoordinate obstruction)

/-! ## Full cofinal settlement with an explicit residual branch -/

inductive SettlementDispositionOutcome
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence) : Type (max w 2) where
  | differentialObstruction
      (obstruction : GeneratedDifferentialClosureObstructionAt diagram)
  | lawObstruction
      (closure : GeneratedDifferentialClosureAt diagram)
      (obstruction : GeneratedCompletionLawObstructionAt diagram closure)
  | relationObstruction
      (obstruction : GeneratedDegreewiseRelationUnsoundObstructionAt diagram)
  | residualObstruction
      (closure : GeneratedDifferentialClosureAt diagram)
      (laws : GeneratedCompletionLawsAt diagram closure)
      (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
      (obstruction : GeneratedDerivedResidualObstructionAt
        diagram closure laws soundness)
      (coordinate : GeneratedDerivedResidualCoordinateAt
        diagram closure laws soundness obstruction)
  | settled
      (closure : GeneratedDifferentialClosureAt diagram)
      (laws : GeneratedCompletionLawsAt diagram closure)
      (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
      (residualZero : GeneratedDerivedResidualZeroAt
        diagram closure laws soundness)

noncomputable def settleWithExplicitResidual
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence) :
    SettlementDispositionOutcome diagram := by
  cases diagram.settle with
  | differentialObstruction obstruction => exact .differentialObstruction obstruction
  | lawObstruction closure obstruction => exact .lawObstruction closure obstruction
  | relationObstruction obstruction => exact .relationObstruction obstruction
  | residualObstruction closure laws soundness obstruction =>
      exact .residualObstruction closure laws soundness obstruction
        (derivedResidualCoordinate obstruction)
  | settled closure laws soundness residualZero =>
      exact .settled closure laws soundness residualZero

theorem settlementDispositionMouth
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence) :
    Nonempty (SettlementDispositionOutcome diagram) :=
  ⟨settleWithExplicitResidual diagram⟩

/-! ## Root-facing extension -/

namespace RootGeneratedCofinalPresentedComplexSettlementStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalPresentedComplexRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

abbrev SettlementDispositionOutcome
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :=
  CofinalPresentedComplexDerivedResidualCoordinate.SettlementDispositionOutcome
    step.diagram

def settlementWithExplicitResidual
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    CofinalPresentedComplexDerivedResidualCoordinate.SettlementDispositionOutcome
      step.diagram :=
  CofinalPresentedComplexDerivedResidualCoordinate.settleWithExplicitResidual
    step.diagram

theorem settlementDisposition_is_total
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    Nonempty
      (CofinalPresentedComplexDerivedResidualCoordinate.SettlementDispositionOutcome
        step.diagram) :=
  ⟨settlementWithExplicitResidual step⟩

end RootGeneratedCofinalPresentedComplexSettlementStepAt

end
end CofinalPresentedComplexDerivedResidualCoordinate
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
