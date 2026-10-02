import H0mework.Versions.R2.Arithmetic.EulerLocal.UnitRealization
import H0mework.Realization.Determinant.FourTermProjection

/-!
# Full-Euler action on the unit-normalized perfect determinant

The direct unit-normalized history has a fixed finite generator carrier and
a generated perfect resolution.  This file first descends dual-bit reversal
through the exact cofinal relation closure.  It then takes the finite
two-exponent fibre of that same perfect resolution and installs the genuine
Euler prefix operator

`(v₀,v₁) ↦ (v₀,v₀+v₁)`

coupled to reversal.  The action is a chain equivalence, so the frozen
determinant-naturality engine produces its determinant-line action.  Euler
is now part of the determinant occurrence itself; it is not an external
readout paired with an unrelated determinant.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticUnitNormalizedEulerDeterminantAction

open CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope
  (EnvelopeRole basis)
open CanonicalUnitArithmeticUnitNormalizedRelationHistory
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open PerfectComplexDeterminantProjection
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure
  (scheduledFactor)

noncomputable section

/-! ## Reversal on the direct cofinal completion -/

def generatorReversalEquiv : Generator ≃ Generator where
  toFun
    | none => none
    | some (role, dualIndex) => some (role, dualIndex.rev)
  invFun
    | none => none
    | some (role, dualIndex) => some (role, dualIndex.rev)
  left_inv := by
    intro generator
    rcases generator with _ | ⟨role, dualIndex⟩ <;> simp
  right_inv := by
    intro generator
    rcases generator with _ | ⟨role, dualIndex⟩ <;> simp

noncomputable def freeReversalEquiv : Lattice ≃ₗ[ℤ] Lattice :=
  Finsupp.domLCongr generatorReversalEquiv

def freeReversal : Lattice →ₗ[ℤ] Lattice :=
  freeReversalEquiv.toLinearMap

theorem freeReversal_involutive : Function.Involutive freeReversal := by
  intro value
  change freeReversalEquiv (freeReversalEquiv value) = value
  exact freeReversalEquiv.symm_apply_apply value

@[simp] theorem freeReversal_liftEnvelope_basis
    (role : EnvelopeRole) (dualIndex : Fin 2) :
    freeReversal (liftEnvelope (basis role dualIndex)) =
      liftEnvelope (basis role dualIndex.rev) := by
  rw [liftEnvelope_basis, liftEnvelope_basis]
  unfold freeReversal freeReversalEquiv
  simp [generatorReversalEquiv]

@[simp] theorem freeReversal_clockMarker (cursor : Nat) :
    freeReversal (clockMarker cursor) = clockMarker cursor := by
  ext generator
  rcases generator with _ | ⟨role, dualIndex⟩ <;>
    simp [clockMarker, freeReversal, freeReversalEquiv,
      generatorReversalEquiv]

@[simp] theorem freeReversal_embeddedComponentDifference :
    freeReversal embeddedComponentDifference =
      -embeddedComponentDifference := by
  unfold embeddedComponentDifference
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.componentDifference
  calc
    freeReversal
        (liftEnvelope
          (basis .component 0 - basis .component 1)) =
        freeReversal
          (liftEnvelope (basis .component 0) -
            liftEnvelope (basis .component 1)) := by
      rw [map_sub]
    _ = freeReversal (liftEnvelope (basis .component 0)) -
          freeReversal (liftEnvelope (basis .component 1)) :=
      map_sub _ _ _
    _ = -(liftEnvelope (basis .component 0) -
        liftEnvelope (basis .component 1)) := by
      rw [freeReversal_liftEnvelope_basis,
        freeReversal_liftEnvelope_basis]
      have reverseZero : (0 : Fin 2).rev = 1 := by decide
      have reverseOne : (1 : Fin 2).rev = 0 := by decide
      rw [reverseZero, reverseOne]
      module
    _ = -liftEnvelope
        (basis .component 0 - basis .component 1) := by
      rw [map_sub]

@[simp] theorem freeReversal_embeddedQuotientUnitDifference :
    freeReversal embeddedQuotientUnitDifference =
      -embeddedQuotientUnitDifference := by
  unfold embeddedQuotientUnitDifference
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.quotientUnitDifference
  calc
    freeReversal
        (liftEnvelope
          (basis .quotientUnit 0 - basis .quotientUnit 1)) =
        freeReversal
          (liftEnvelope (basis .quotientUnit 0) -
            liftEnvelope (basis .quotientUnit 1)) := by
      rw [map_sub]
    _ = freeReversal (liftEnvelope (basis .quotientUnit 0)) -
          freeReversal (liftEnvelope (basis .quotientUnit 1)) :=
      map_sub _ _ _
    _ = -(liftEnvelope (basis .quotientUnit 0) -
        liftEnvelope (basis .quotientUnit 1)) := by
      rw [freeReversal_liftEnvelope_basis,
        freeReversal_liftEnvelope_basis]
      have reverseZero : (0 : Fin 2).rev = 1 := by decide
      have reverseOne : (1 : Fin 2).rev = 0 := by decide
      rw [reverseZero, reverseOne]
      module
    _ = -liftEnvelope
        (basis .quotientUnit 0 - basis .quotientUnit 1) := by
      rw [map_sub]

theorem freeReversal_localRelation (cursor : Nat) :
    freeReversal (localRelation cursor) = -localRelation cursor := by
  rw [localRelation_normalForm]
  rw [map_sub, map_nsmul, map_nsmul,
    freeReversal_embeddedComponentDifference,
    freeReversal_embeddedQuotientUnitDifference]
  module

def IsGeneratedRelation (relationValue : Lattice) : Prop :=
  (∃ cursor, relationValue = localRelation cursor) ∨
    ∃ cursor, relationValue = clockMarker cursor

private theorem trace_advance_cases
    (next : Event → RootedAccountedUnfolding Event)
    (occurrence : RootedAccountedUnfolding Event) :
    ∀ event, event ∈ (occurrence.advance next).trace →
      event ∈ occurrence.trace ∨
        ∃ leaf, leaf ∈ occurrence.frontier ∧
          event ∈ (next leaf).trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ event, event ∈ (current.advance next).trace →
        event ∈ current.trace ∨
          ∃ leaf, leaf ∈ current.frontier ∧
            event ∈ (next leaf).trace)
    (motive_2 := fun branches =>
      ∀ event,
        event ∈ RootedAccountedUnfolding.traceBranches
          (RootedAccountedUnfolding.advanceBranches next branches) →
        event ∈ RootedAccountedUnfolding.traceBranches branches ∨
          ∃ leaf,
            leaf ∈ RootedAccountedUnfolding.frontierBranches branches ∧
              event ∈ (next leaf).trace)
    (fun root branches branchResult event event_mem => by
      cases branches with
      | nil =>
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.nil : AccountedBranches Event)).advance next =
                RootedAccountedUnfolding.occur root
                  (AccountedBranches.singleton (next root)) from rfl] at event_mem
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.singleton (next root))).trace =
                root :: (next root).trace by
            simp [RootedAccountedUnfolding.trace,
              AccountedBranches.singleton]] at event_mem
          rw [List.mem_cons] at event_mem
          cases event_mem with
          | inl event_eq =>
              subst event
              exact Or.inl (RootedAccountedUnfolding.root_mem_trace _)
          | inr next_mem =>
              exact Or.inr ⟨root, by
                change root ∈ [root]
                simp, next_mem⟩
      | cons head tail =>
          change event ∈ root ::
            RootedAccountedUnfolding.traceBranches
              (RootedAccountedUnfolding.advanceBranches next
                (.cons head tail)) at event_mem
          rw [List.mem_cons] at event_mem
          cases event_mem with
          | inl event_eq =>
              subst event
              exact Or.inl (RootedAccountedUnfolding.root_mem_trace _)
          | inr branch_mem =>
              cases branchResult event branch_mem with
              | inl old_mem =>
                  exact Or.inl (List.mem_cons_of_mem root old_mem)
              | inr generated => exact Or.inr generated)
    (fun event event_mem => by
      change event ∈ ([] : List Event) at event_mem
      exact False.elim (List.not_mem_nil event_mem))
    (fun head tail headResult tailResult event event_mem => by
      change event ∈ (head.advance next).trace ++
        RootedAccountedUnfolding.traceBranches
          (RootedAccountedUnfolding.advanceBranches next tail) at event_mem
      rw [List.mem_append] at event_mem
      cases event_mem with
      | inl inHead =>
          cases headResult event inHead with
          | inl oldHead =>
              exact Or.inl (by
                change event ∈ head.trace ++
                  RootedAccountedUnfolding.traceBranches tail
                rw [List.mem_append]
                exact Or.inl oldHead)
          | inr generated =>
              obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
              exact Or.inr ⟨leaf, by
                change leaf ∈ head.frontier ++
                  RootedAccountedUnfolding.frontierBranches tail
                rw [List.mem_append]
                exact Or.inl leaf_mem,
                generated_mem⟩
      | inr inTail =>
          cases tailResult event inTail with
          | inl oldTail =>
              exact Or.inl (by
                change event ∈ head.trace ++
                  RootedAccountedUnfolding.traceBranches tail
                rw [List.mem_append]
                exact Or.inr oldTail)
          | inr generated =>
              obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
              exact Or.inr ⟨leaf, by
                change leaf ∈ head.frontier ++
                  RootedAccountedUnfolding.frontierBranches tail
                rw [List.mem_append]
                exact Or.inr leaf_mem,
                generated_mem⟩)
    occurrence

theorem rowPatch_relation_generated (cursor : Nat)
    (relationValue : Lattice)
    (membership : PresentedRelationEventAt.relation relationValue ∈
      (rowPatch cursor).trace) :
    IsGeneratedRelation relationValue := by
  rw [rowPatch_trace] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with relation_eq | marker_eq
  · left
    exact ⟨cursor, PresentedRelationEventAt.relation.inj relation_eq⟩
  · right
    exact ⟨cursor, PresentedRelationEventAt.relation.inj marker_eq⟩

theorem observation_relation_generated (stage : Nat)
    (relationValue : Lattice)
    (membership : PresentedRelationEventAt.relation relationValue ∈
      (history.observation stage).trace) :
    IsGeneratedRelation relationValue := by
  induction stage with
  | zero => exact rowPatch_relation_generated 0 relationValue membership
  | succ stage inductionHypothesis =>
      rw [history.observation_succ] at membership
      cases trace_advance_cases history.actualContinuation
          (history.observation stage) _ membership with
      | inl old => exact inductionHypothesis old
      | inr generated =>
          obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
          rw [observation_frontier] at leaf_mem
          have leaf_eq : leaf = clockMarkerEvent stage := by
            simpa using leaf_mem
          subst leaf
          change PresentedRelationEventAt.relation relationValue ∈
            (nextPatch (clockMarkerEvent stage)).trace at generated_mem
          rw [nextPatch_clockMarkerEvent] at generated_mem
          exact rowPatch_relation_generated
            (stage + 1) relationValue generated_mem

theorem observed_relation_generated (stage : Nat)
    (relationValue : Lattice)
    (membership : PresentedRelationEventAt.relation relationValue ∈
      history.observedEvents stage) :
    IsGeneratedRelation relationValue := by
  rw [RootGeneratedCofinalHistoryAt.observedEvents,
    List.mem_flatMap] at membership
  obtain ⟨index, _index_mem, relation_mem⟩ := membership
  exact observation_relation_generated index relationValue relation_mem

theorem freeReversal_maps_relationClosure :
    history.relationClosure ≤ history.relationClosure.comap freeReversal := by
  apply iSup_le
  intro stage
  apply Submodule.span_le.mpr
  intro relationValue relationEvent
  rcases observed_relation_generated stage relationValue relationEvent with
    localRow | markerRow
  · obtain ⟨cursor, rfl⟩ := localRow
    change freeReversal (localRelation cursor) ∈ history.relationClosure
    rw [freeReversal_localRelation]
    exact history.relationClosure.neg_mem
      (localRelation_mem_relationClosure cursor)
  · obtain ⟨cursor, rfl⟩ := markerRow
    change freeReversal (clockMarker cursor) ∈ history.relationClosure
    rw [freeReversal_clockMarker]
    exact history.relationStage_le_closure stage
      (Submodule.subset_span relationEvent)

def closureReversal : history.generatorClosure →ₗ[ℤ]
    history.generatorClosure :=
  LinearMap.codRestrict history.generatorClosure
    (freeReversal.comp history.generatorClosure.subtype)
    (fun value => by
      change freeReversal value.1 ∈ history.generatorClosure
      have topMembership : freeReversal value.1 ∈
          (⊤ : Submodule ℤ Lattice) := Submodule.mem_top
      simpa only [generatorClosure_eq_top] using topMembership)

theorem closureReversal_involutive : Function.Involutive closureReversal := by
  intro value
  apply Subtype.ext
  exact freeReversal_involutive value

theorem relationInGeneratorClosure_maps :
    history.relationInGeneratorClosure ≤
      history.relationInGeneratorClosure.comap closureReversal := by
  intro relationValue relationMem
  change freeReversal relationValue.1 ∈ history.relationClosure
  exact freeReversal_maps_relationClosure relationMem

def completionReversal : history.CompletionCarrier →ₗ[ℤ]
    history.CompletionCarrier :=
  Submodule.mapQ history.relationInGeneratorClosure
    history.relationInGeneratorClosure closureReversal
    relationInGeneratorClosure_maps

theorem completionReversal_involutive :
    Function.Involutive completionReversal := by
  intro value
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change Submodule.Quotient.mk
      (closureReversal (closureReversal representative)) =
    Submodule.Quotient.mk representative
  rw [closureReversal_involutive]

/-! ## Exact stage-zero perfect resolution and its reversal -/

abbrev StageZeroGenerator := history.generatorStage 0

abbrev StageZeroKernel :=
  LinearMap.ker (history.stageGeneratorToCompletion 0)

abbrev ZeroTerm := Fin 0 → ℤ

def stageZeroPerfectComplex :
    FourTermIntegralComplexAt StageZeroKernel StageZeroGenerator
      ZeroTerm ZeroTerm where
  d₀ := StageZeroKernel.subtype
  d₁ := 0
  d₂ := 0
  d₁_comp_d₀ := rfl
  d₂_comp_d₁ := rfl

noncomputable def stageZeroGeneratorBasis :
    Module.Basis
      { generator // generator ∈ history.generatorSupport 0 }
      ℤ StageZeroGenerator := by
  let supportSet : Set Generator := history.generatorSupport 0
  let basis : Module.Basis supportSet ℤ (supportSet →₀ ℤ) :=
    Finsupp.basisSingleOne
  exact basis.map (Finsupp.supportedEquivFinsupp supportSet).symm

noncomputable def stageZeroKernelBasis :
    Σ rank : Nat, Module.Basis (Fin rank) ℤ StageZeroKernel :=
  Submodule.basisOfPid stageZeroGeneratorBasis StageZeroKernel

noncomputable instance stageZeroGeneratorFree :
    Module.Free ℤ StageZeroGenerator :=
  Module.Free.of_basis stageZeroGeneratorBasis

noncomputable instance stageZeroGeneratorFinite :
    Module.Finite ℤ StageZeroGenerator :=
  Module.Finite.of_basis stageZeroGeneratorBasis

noncomputable instance stageZeroKernelFree :
    Module.Free ℤ StageZeroKernel :=
  Module.Free.of_basis stageZeroKernelBasis.2

noncomputable instance stageZeroKernelFinite :
    Module.Finite ℤ StageZeroKernel :=
  Module.Finite.of_basis stageZeroKernelBasis.2

def stageZeroPerfectComplexOccurrence : RootedAccountedUnfolding
    (FourTermIntegralComplexAt StageZeroKernel StageZeroGenerator
      ZeroTerm ZeroTerm) :=
  history.root.map fun _root => stageZeroPerfectComplex

def stageZeroDeterminantProjection :
    RootGeneratedFourTermPerfectDeterminantProjectionAt history.root
      stageZeroPerfectComplexOccurrence :=
  RootGeneratedFourTermPerfectDeterminantProjectionAt.generate

theorem stageZeroPerfectCalculation :
    RootGeneratedFourTermPerfectCalculationAt
      stageZeroDeterminantProjection :=
  RootGeneratedFourTermPerfectCalculationAt.generate
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance

def stageZeroDeterminantState :
    RootGeneratedFourTermPerfectDeterminantStateAt
      stageZeroDeterminantProjection stageZeroPerfectCalculation :=
  RootGeneratedFourTermPerfectDeterminantStateAt.realize

def stageZeroReversal : StageZeroGenerator →ₗ[ℤ]
    StageZeroGenerator :=
  LinearMap.codRestrict StageZeroGenerator
    (freeReversal.comp StageZeroGenerator.subtype)
    (fun value => by
      change freeReversal value.1 ∈ history.generatorStage 0
      have topMembership : freeReversal value.1 ∈
          (⊤ : Submodule ℤ Lattice) := Submodule.mem_top
      simpa only [generatorStage_zero_eq_top] using topMembership)

theorem stageZeroReversal_involutive :
    Function.Involutive stageZeroReversal := by
  intro value
  apply Subtype.ext
  exact freeReversal_involutive value

noncomputable def stageZeroReversalEquiv :
    StageZeroGenerator ≃ₗ[ℤ] StageZeroGenerator where
  toLinearMap := stageZeroReversal
  invFun := stageZeroReversal
  left_inv := stageZeroReversal_involutive
  right_inv := stageZeroReversal_involutive

theorem completionReversal_stageGeneratorToCompletion
    (value : StageZeroGenerator) :
    completionReversal
        (history.stageGeneratorToCompletion 0 value) =
      history.stageGeneratorToCompletion 0
        (stageZeroReversal value) := by
  rfl

def stageZeroKernelReversal : StageZeroKernel →ₗ[ℤ]
    StageZeroKernel :=
  LinearMap.codRestrict StageZeroKernel
    (stageZeroReversal.comp StageZeroKernel.subtype)
    (fun value => by
      rw [LinearMap.mem_ker]
      change history.stageGeneratorToCompletion 0
        (stageZeroReversal (StageZeroKernel.subtype value)) = 0
      rw [← completionReversal_stageGeneratorToCompletion]
      have kernelZero : history.stageGeneratorToCompletion 0
          (StageZeroKernel.subtype value) = 0 :=
        LinearMap.mem_ker.mp value.property
      rw [kernelZero, map_zero])

theorem stageZeroKernelReversal_involutive :
    Function.Involutive stageZeroKernelReversal := by
  intro value
  apply Subtype.ext
  exact stageZeroReversal_involutive value

noncomputable def stageZeroKernelReversalEquiv :
    StageZeroKernel ≃ₗ[ℤ] StageZeroKernel where
  toLinearMap := stageZeroKernelReversal
  invFun := stageZeroKernelReversal
  left_inv := stageZeroKernelReversal_involutive
  right_inv := stageZeroKernelReversal_involutive

theorem stageZeroKernelReversal_subtype (value : StageZeroKernel) :
    StageZeroKernel.subtype (stageZeroKernelReversal value) =
      stageZeroReversal (StageZeroKernel.subtype value) :=
  rfl

/-! ## Two-exponent Euler/reversal chain action -/

abbrev TwoLevel (M : Type*) := M × M

noncomputable def twoLevelPrefixEquiv
    (M : Type*) [AddCommGroup M] [Module ℤ M] :
    TwoLevel M ≃ₗ[ℤ] TwoLevel M where
  toFun value := (value.1, value.1 + value.2)
  invFun value := (value.1, value.2 - value.1)
  left_inv := by
    intro value
    ext <;> simp
  right_inv := by
    intro value
    ext <;> simp
  map_add' := by
    intro left right
    apply Prod.ext
    · rfl
    · change (left.1 + right.1) + (left.2 + right.2) =
        (left.1 + left.2) + (right.1 + right.2)
      abel
  map_smul' := by
    intro scalar value
    ext <;> simp [zsmul_add]

noncomputable def twoLevelPointwiseEquiv
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (equiv : M ≃ₗ[ℤ] M) : TwoLevel M ≃ₗ[ℤ] TwoLevel M where
  toFun value := (equiv value.1, equiv value.2)
  invFun value := (equiv.symm value.1, equiv.symm value.2)
  left_inv := by
    intro value
    ext <;> simp
  right_inv := by
    intro value
    ext <;> simp
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro scalar value
    ext <;> simp

/-- Genuine two-exponent Euler prefix after pointwise reversal. -/
noncomputable def twoLevelEulerReversalEquiv
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (reversal : M ≃ₗ[ℤ] M) : TwoLevel M ≃ₗ[ℤ] TwoLevel M :=
  (twoLevelPointwiseEquiv reversal).trans (twoLevelPrefixEquiv M)

/-- The two-state prefix action realizes the entire geometric Euler series:
after `n` steps its accumulator contains exactly `n` copies of the seed. -/
def twoLevelPrefixIterate
    (M : Type*) [AddCommGroup M] [Module ℤ M] :
    Nat → TwoLevel M → TwoLevel M
  | 0, value => value
  | stage + 1, value =>
      twoLevelPrefixEquiv M (twoLevelPrefixIterate M stage value)

theorem twoLevelPrefixIterate_eq
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    (stage : Nat) (value : TwoLevel M) :
    twoLevelPrefixIterate M stage value =
      (value.1, stage • value.1 + value.2) := by
  induction stage with
  | zero => simp [twoLevelPrefixIterate]
  | succ stage inductionHypothesis =>
      rw [twoLevelPrefixIterate, inductionHypothesis]
      change (value.1, value.1 + (stage • value.1 + value.2)) =
        (value.1, (stage + 1) • value.1 + value.2)
      apply Prod.ext
      · rfl
      · rw [add_nsmul, one_nsmul]
        abel

theorem twoLevelPrefixIterate_seed_coefficient
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    (stage : Nat) (seed : M) :
    (twoLevelPrefixIterate M stage (seed, 0)).2 = stage • seed := by
  rw [twoLevelPrefixIterate_eq]
  simp

abbrev TwoLevelKernel := TwoLevel StageZeroKernel
abbrev TwoLevelGenerator := TwoLevel StageZeroGenerator
abbrev TwoLevelZero := TwoLevel ZeroTerm

def twoLevelDifferentialZero :
    TwoLevelKernel →ₗ[ℤ] TwoLevelGenerator where
  toFun value :=
    (StageZeroKernel.subtype value.1,
      StageZeroKernel.subtype value.2)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def twoLevelPerfectComplex :
    FourTermIntegralComplexAt TwoLevelKernel TwoLevelGenerator
      TwoLevelZero TwoLevelZero where
  d₀ := twoLevelDifferentialZero
  d₁ := 0
  d₂ := 0
  d₁_comp_d₀ := rfl
  d₂_comp_d₁ := rfl

noncomputable instance twoLevelKernelFree :
    Module.Free ℤ TwoLevelKernel := inferInstance

noncomputable instance twoLevelKernelFinite :
    Module.Finite ℤ TwoLevelKernel := inferInstance

noncomputable instance twoLevelGeneratorFree :
    Module.Free ℤ TwoLevelGenerator := inferInstance

noncomputable instance twoLevelGeneratorFinite :
    Module.Finite ℤ TwoLevelGenerator := inferInstance

noncomputable instance twoLevelZeroFree :
    Module.Free ℤ TwoLevelZero := inferInstance

noncomputable instance twoLevelZeroFinite :
    Module.Finite ℤ TwoLevelZero := inferInstance

def twoLevelPerfectComplexOccurrence : RootedAccountedUnfolding
    (FourTermIntegralComplexAt TwoLevelKernel TwoLevelGenerator
      TwoLevelZero TwoLevelZero) :=
  history.root.map fun _root => twoLevelPerfectComplex

def twoLevelDeterminantProjection :
    RootGeneratedFourTermPerfectDeterminantProjectionAt history.root
      twoLevelPerfectComplexOccurrence :=
  RootGeneratedFourTermPerfectDeterminantProjectionAt.generate

theorem twoLevelPerfectCalculation :
    RootGeneratedFourTermPerfectCalculationAt
      twoLevelDeterminantProjection :=
  RootGeneratedFourTermPerfectCalculationAt.generate
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance

def twoLevelDeterminantState :
    RootGeneratedFourTermPerfectDeterminantStateAt
      twoLevelDeterminantProjection twoLevelPerfectCalculation :=
  RootGeneratedFourTermPerfectDeterminantStateAt.realize

noncomputable def twoLevelEulerReversalComplexEquiv :
    FourTermIntegralComplexEquivAt
      twoLevelPerfectComplex twoLevelPerfectComplex where
  e₀ := twoLevelEulerReversalEquiv stageZeroKernelReversalEquiv
  e₁ := twoLevelEulerReversalEquiv stageZeroReversalEquiv
  e₂ := twoLevelEulerReversalEquiv (LinearEquiv.refl ℤ ZeroTerm)
  e₃ := twoLevelEulerReversalEquiv (LinearEquiv.refl ℤ ZeroTerm)
  commute₀ := by
    apply LinearMap.ext
    intro value
    apply Prod.ext
    · change stageZeroReversal
          (StageZeroKernel.subtype value.1) =
        StageZeroKernel.subtype (stageZeroKernelReversal value.1)
      exact (stageZeroKernelReversal_subtype value.1).symm
    · change stageZeroReversal
          (StageZeroKernel.subtype value.1) +
          stageZeroReversal
            (StageZeroKernel.subtype value.2) =
        StageZeroKernel.subtype
            (stageZeroKernelReversal value.1) +
          StageZeroKernel.subtype
            (stageZeroKernelReversal value.2)
      rw [← stageZeroKernelReversal_subtype,
        ← stageZeroKernelReversal_subtype]
  commute₁ := by
    apply LinearMap.ext
    intro value
    simp [twoLevelPerfectComplex]
  commute₂ := by
    apply LinearMap.ext
    intro value
    simp [twoLevelPerfectComplex]

def twoLevelEulerReversalActionOccurrence : RootedAccountedUnfolding
    (FourTermIntegralComplexEquivAt
      twoLevelPerfectComplex twoLevelPerfectComplex) :=
  history.root.map fun _root => twoLevelEulerReversalComplexEquiv

def twoLevelDeterminantNaturality :
    RootGeneratedFourTermDeterminantNaturalityAt history.root
      twoLevelEulerReversalActionOccurrence :=
  RootGeneratedFourTermDeterminantNaturalityAt.generate

abbrev TwoLevelIntegralLine :=
  twoLevelDeterminantState.integralLine

noncomputable def twoLevelDeterminantLineEulerReversal :
    TwoLevelIntegralLine ≃ₗ[ℤ] TwoLevelIntegralLine :=
  twoLevelDeterminantNaturality.determinantLineTransport

theorem twoLevelEulerDeterminant_preserves_same_root :
    twoLevelDeterminantNaturality.root = history.root ∧
      twoLevelDeterminantProjection.root = history.root :=
  ⟨rfl, rfl⟩

theorem twoLevelEulerDeterminant_has_generated_unit :
    Nonempty
      (GradedIntegralDeterminantLine.CanonicalIntegralUnitTorsor
        TwoLevelIntegralLine) :=
  ⟨twoLevelDeterminantState.unitTorsor⟩

/-! ## Actual component bridge into the determinant action -/

noncomputable def completionReversalEquiv :
    history.CompletionCarrier ≃ₗ[ℤ] history.CompletionCarrier where
  toLinearMap := completionReversal
  invFun := completionReversal
  left_inv := completionReversal_involutive
  right_inv := completionReversal_involutive

theorem completionReversal_quotientUnitClassAt
    (cursor : Nat) (dualIndex : Fin 2) :
    completionReversal (quotientUnitClassAt cursor dualIndex) =
      quotientUnitClassAt cursor dualIndex.rev := by
  unfold quotientUnitClassAt completionReversal
    RootGeneratedCofinalHistoryAt.stageGeneratorToCompletion
    RootGeneratedCofinalHistoryAt.completionProjection
    RootGeneratedCofinalHistoryAt.stageGeneratorToClosure
  change Submodule.Quotient.mk
      (closureReversal ⟨liftEnvelope (basis .quotientUnit dualIndex), _⟩) =
    Submodule.Quotient.mk
      ⟨liftEnvelope (basis .quotientUnit dualIndex.rev), _⟩
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact freeReversal_liftEnvelope_basis .quotientUnit dualIndex

theorem completionReversal_normalizedComponentAt
    (cursor : Nat) (dualIndex : Fin 2) :
    completionReversal (normalizedComponentAt cursor dualIndex) =
      normalizedComponentAt cursor dualIndex.rev := by
  unfold normalizedComponentAt
  rw [map_nsmul, completionReversal_quotientUnitClassAt]

@[simp] theorem completionReversalEquiv_normalizedComponentAt
    (cursor : Nat) (dualIndex : Fin 2) :
    completionReversalEquiv (normalizedComponentAt cursor dualIndex) =
      normalizedComponentAt cursor dualIndex.rev :=
  completionReversal_normalizedComponentAt cursor dualIndex

def completionTwoLevelEulerReversal :
    TwoLevel history.CompletionCarrier ≃ₗ[ℤ]
      TwoLevel history.CompletionCarrier :=
  twoLevelEulerReversalEquiv completionReversalEquiv

def completionTwoLevelBoundary :
    TwoLevel history.CompletionCarrier →ₗ[ℤ]
      TwoLevel history.CompletionCarrier :=
  LinearMap.id - completionTwoLevelEulerReversal.toLinearMap

def completionTwoLevelSource (cursor : Nat) :
    TwoLevel history.CompletionCarrier :=
  (normalizedComponentAt cursor 0, normalizedComponentAt cursor 0)

def completionTwoLevelSum :
    TwoLevel history.CompletionCarrier →ₗ[ℤ]
      history.CompletionCarrier where
  toFun value := value.1 + value.2
  map_add' := by intro left right; simp; abel
  map_smul' := by intro scalar value; simp

theorem completionTwoLevelBoundary_apply (cursor : Nat) :
    completionTwoLevelBoundary (completionTwoLevelSource cursor) =
      (normalizedComponentAt cursor 0 -
          normalizedComponentAt cursor 1,
        normalizedComponentAt cursor 0 -
          (normalizedComponentAt cursor 1 +
            normalizedComponentAt cursor 1)) := by
  apply Prod.ext <;>
    simp [completionTwoLevelBoundary, completionTwoLevelSource,
      completionTwoLevelEulerReversal,
      twoLevelEulerReversalEquiv, twoLevelPointwiseEquiv,
      twoLevelPrefixEquiv]

/-- The chain-level two-exponent Euler boundary reads exactly as the actual
local full-Euler component constructed from exponent-zero and exponent-one
probes. -/
theorem actualLocalEulerComponent_is_determinantBoundary
    (cursor : Nat) :
    completionTwoLevelSum
        (completionTwoLevelBoundary (completionTwoLevelSource cursor)) =
      CanonicalUnitArithmeticUnitNormalizedEulerLocalRealization.twoLevelRealization
        cursor
        (CanonicalUnitArithmeticFactorizationEulerLocalLanding.component
          (scheduledFactor cursor)) := by
  rw [completionTwoLevelBoundary_apply,
    CanonicalUnitArithmeticUnitNormalizedEulerLocalRealization.twoLevelRealization_component]
  change
    (normalizedComponentAt cursor 0 - normalizedComponentAt cursor 1) +
        (normalizedComponentAt cursor 0 -
          (normalizedComponentAt cursor 1 +
            normalizedComponentAt cursor 1)) =
      2 • normalizedComponentAt cursor 0 -
        3 • normalizedComponentAt cursor 1
  module

def stageZeroClockGenerator : StageZeroGenerator :=
  ⟨Finsupp.single none 1, by
    have topMembership : (Finsupp.single none 1 : Lattice) ∈
        (⊤ : Submodule ℤ Lattice) := Submodule.mem_top
    simpa only [generatorStage_zero_eq_top] using topMembership⟩

theorem stageZeroClockGenerator_ne_zero :
    stageZeroClockGenerator ≠ 0 := by
  intro equality
  have atClock := congrArg (fun value : StageZeroGenerator => value.1 none)
    equality
  change (Finsupp.single none 1 : Lattice) none = 0 at atClock
  simp at atClock

theorem stageZeroReversal_clockGenerator :
    stageZeroReversal stageZeroClockGenerator =
      stageZeroClockGenerator := by
  apply Subtype.ext
  change freeReversal (Finsupp.single none 1 : Lattice) =
    Finsupp.single none 1
  simpa [stageZeroClockGenerator, clockMarker] using
    freeReversal_clockMarker 0

/-- Semantic kill test: deleting the Euler prefix leaves only pointwise
reversal, and the action changes on an actual generated degree-one atom. -/
theorem twoLevelEulerReversal_ne_bareReversal :
    twoLevelEulerReversalEquiv stageZeroReversalEquiv ≠
      twoLevelPointwiseEquiv stageZeroReversalEquiv := by
  intro equality
  have atInput := congrArg
    (fun equiv : TwoLevelGenerator ≃ₗ[ℤ] TwoLevelGenerator =>
      equiv (stageZeroClockGenerator, 0)) equality
  have secondCoordinate := congrArg Prod.snd atInput
  have clockZero : stageZeroClockGenerator = 0 := by
    simpa [twoLevelEulerReversalEquiv, twoLevelPointwiseEquiv,
      twoLevelPrefixEquiv, stageZeroReversal_clockGenerator] using
        secondCoordinate
  exact stageZeroClockGenerator_ne_zero clockZero

end

end CanonicalUnitArithmeticUnitNormalizedEulerDeterminantAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
