import H0mework.Versions.V2.Arithmetic.RiemannRuntime.PairedOmegaEffectRuntimeFacade
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Source.Division.Whole

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RuntimeCombCalculationGate
open Complex MeasureTheory Set
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
noncomputable section
namespace C
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
  (targetState relation_boundary updated_inverse_fibre relation_cochain)
end C
namespace A
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (target_factorizes)
end A
abbrev Value := OriginalKCombCalculation.Value
abbrev Var := OriginalKCombCalculation.Var

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (rightHalf : 1/2 < observation.coordinate.re) (depth : Nat)

abbrev half := (⟨rightHalf⟩ : OriginalKCombCalculation.Half observation)
abbrev occurrence := (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
abbrev origin := (runtimeEffectRuntimeAt observation nontrivial depth).current.visit.current
abbrev read := runtimeCombCalculationResultAt observation nontrivial depth (half observation rightHalf)
abbrev raw := OriginalKCombCalculation.reader observation nontrivial (half observation rightHalf)
  (occurrence observation nontrivial depth)
abbrev inputReader := fun (_ : OriginalKCombCalculation.Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  (origin observation nontrivial depth)) => raw observation nontrivial rightHalf depth

-- The result is extracted from the newly installed face of the original named facade.
theorem installed_value :
    (read observation nontrivial rightHalf depth).2.2.1 =
      (burnolDirectRightResolventCLM (originalKCoordinate observation.coordinate
        (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial).2 rightHalf) ^
        generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate)
          (burnolPaCombApproximation 0 : BurnolL2) :=
  OriginalKCombCalculation.result_value observation nontrivial (half observation rightHalf)
    (occurrence observation nontrivial depth)

theorem installed_trace : (read observation nontrivial rightHalf depth).2.1.2.length =
    generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate + 1 :=
  OriginalKCombCalculation.result_trace observation nontrivial (half observation rightHalf)
    (occurrence observation nontrivial depth)

theorem installed_targetState : (read observation nontrivial rightHalf depth).2.1 =
    C.targetState OriginalKCombCalculation.Base (origin observation nontrivial depth)
      (inputReader observation nontrivial rightHalf depth) := rfl

theorem installed_relation :
    relationMap (R := ℂ) (read observation nontrivial rightHalf depth).1.environment
      (read observation nontrivial rightHalf depth).2.1.2.relationWords =
      Finsupp.single (read observation nontrivial rightHalf depth).1.expression (1 : ℂ) -
        Finsupp.single (.const (read observation nontrivial rightHalf depth).2.2.1) (1 : ℂ) :=
  C.relation_boundary (R := ℂ) OriginalKCombCalculation.Base (origin observation nontrivial depth)
    (inputReader observation nontrivial rightHalf depth)

theorem installed_inverse (increment : Env Value Var) : type_of%
    ((read observation nontrivial rightHalf depth).2.1.2.updated_residual (R := ℂ) increment) :=
  C.updated_inverse_fibre (R := ℂ) OriginalKCombCalculation.Base (origin observation nontrivial depth)
    (inputReader observation nontrivial rightHalf depth) increment

theorem installed_cochain (increment : Env Value Var) : type_of%
    ((read observation nontrivial rightHalf depth).2.1.2.relation_cochain (R := ℂ) increment) :=
  C.relation_cochain (R := ℂ) OriginalKCombCalculation.Base (origin observation nontrivial depth)
    (inputReader observation nontrivial rightHalf depth) increment

-- Executor authority is the existing mathematical completion, not another physical tick.
example : type_of% (A.target_factorizes OriginalKCombCalculation.Base (origin observation nontrivial depth)
    (inputReader observation nontrivial rightHalf depth)) :=
  A.target_factorizes OriginalKCombCalculation.Base (origin observation nontrivial depth)
    (inputReader observation nontrivial rightHalf depth)

-- This physical theorem is downstream of the source AST and its emitted value.
theorem installed_physical : (read observation nontrivial rightHalf depth).2.2.1 ∈
    evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  rw [installed_value]
  exact CombSource.Division.actual_comb_physical observation nontrivial rightHalf 0 _ (le_refl _)

example : (read observation nontrivial rightHalf depth).1.environment () () =
    (burnolPaCombApproximation 0 : BurnolL2) := rfl

example : remaining (read observation nontrivial rightHalf depth).1.expression =
    generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate + 1 :=
  OriginalKCombCalculation.code_budget _ _

-- A proof in the original fibre cannot select a second result.
example (other : OriginalKCombCalculation.Half observation) :
    runtimeCombCalculationReadoutAt observation nontrivial depth (half observation rightHalf) =
      runtimeCombCalculationReadoutAt observation nontrivial depth other := by
  have same : half observation rightHalf = other := Subsingleton.elim _ _
  cases same
  rfl

-- Same installed source, complete old ledger, and original physical successor.
example : type_of% (runtimeCombCalculationReadoutAt_factorizes observation nontrivial depth
    (half observation rightHalf)) :=
  runtimeCombCalculationReadoutAt_factorizes observation nontrivial depth (half observation rightHalf)

example : type_of% (runtimeEffectRoot_reuses_lower_source_emitter observation nontrivial) :=
  runtimeEffectRoot_reuses_lower_source_emitter observation nontrivial

example : type_of% (runtimeEffectFacadeReadoutAt_heq_installedFiber observation nontrivial depth) :=
  runtimeEffectFacadeReadoutAt_heq_installedFiber observation nontrivial depth

example : (runtimeEffectCausalSuccessorAt observation nontrivial depth).successor.targetVisit =
    runtimeEffectVisitAt observation nontrivial (depth + 1) :=
  runtimeEffectCausalSuccessorAt_targetVisit observation nontrivial depth

-- m+1 paid mathematical steps are not the single original physical tick.
theorem math_trace_not_one : (read observation nontrivial rightHalf depth).2.1.2.length ≠ 1 := by
  rw [installed_trace]
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  omega

-- The old next exists without a right-half fibre or a calculation face.
example (anyDepth : Nat) :
    (runtimeEffectCausalSuccessorAt observation nontrivial anyDepth).successor.targetVisit =
      runtimeEffectVisitAt observation nontrivial (anyDepth + 1) :=
  runtimeEffectCausalSuccessorAt_targetVisit observation nontrivial anyDepth

#print axioms OriginalKCombCalculation.reader
#print axioms OriginalKCombCalculation.result_value
#print axioms OriginalKCombCalculation.result_trace
#print axioms runtimeCombCalculationReadoutAt_factorizes
#print axioms installed_value
#print axioms installed_trace
#print axioms installed_targetState
#print axioms installed_relation
#print axioms installed_inverse
#print axioms installed_cochain
#print axioms installed_physical
#print axioms math_trace_not_one
end
end RuntimeCombCalculationGate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
