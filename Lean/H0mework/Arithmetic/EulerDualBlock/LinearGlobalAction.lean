import H0mework.Arithmetic.EulerDualBlock.WholeRelationDeterminant

/-!
# Block-linear global whole action and integral comparison

The common-coordinate complex is first globalized in
`ModuleCat BlockCoordinateRing`; no module structure is invented on the
integral limit.  Restriction of scalars is a right adjoint and preserves this
limit, producing the canonical comparison with the already framework-owned
integral global state.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalAction

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CategoryTheory
open CategoryTheory.Limits
open DerivedAdicCofiber

noncomputable section

noncomputable def localBlockLinearDiagram (seed : FactorizationPayload) :
    ℕᵒᵖ ⥤ IntegralCochainComplex BlockCoordinateRing :=
  Functor.ofOpSequence
    (X := fun stage => blockDirectComplex seed stage)
    (blockDirectRestriction seed)

abbrev BlockLinearGlobalState : IntegralCochainComplex BlockCoordinateRing :=
  limit (localBlockLinearDiagram seedOccurrence.root)

noncomputable def blockLinearGlobalRestriction (stage : ℕᵒᵖ) :
    BlockLinearGlobalState ⟶
      (localBlockLinearDiagram seedOccurrence.root).obj stage :=
  limit.π (localBlockLinearDiagram seedOccurrence.root) stage

noncomputable def blockLinearEulerNatTrans (seed : FactorizationPayload) :
    localBlockLinearDiagram seed ⟶ localBlockLinearDiagram seed :=
  NatTrans.ofOpSequence
    (blockDirectEulerAction seed)
    (fun stage => by
      simp only [localBlockLinearDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (blockDirectRestriction_action_square seed stage).symm)

noncomputable def blockLinearReversalNatTrans (seed : FactorizationPayload) :
    localBlockLinearDiagram seed ⟶ localBlockLinearDiagram seed :=
  NatTrans.ofOpSequence
    (blockDirectReversal seed)
    (fun stage => by
      simp only [localBlockLinearDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (blockDirectRestriction_reversal_square seed stage).symm)

noncomputable def blockLinearGlobalEulerAction :
    BlockLinearGlobalState ⟶ BlockLinearGlobalState :=
  limMap (blockLinearEulerNatTrans seedOccurrence.root)

noncomputable def blockLinearGlobalReversal :
    BlockLinearGlobalState ⟶ BlockLinearGlobalState :=
  limMap (blockLinearReversalNatTrans seedOccurrence.root)

theorem blockLinearGlobalEulerAction_restriction (stage : ℕᵒᵖ) :
    blockLinearGlobalEulerAction ≫ blockLinearGlobalRestriction stage =
      blockLinearGlobalRestriction stage ≫
        (blockLinearEulerNatTrans seedOccurrence.root).app stage :=
  limMap_π (blockLinearEulerNatTrans seedOccurrence.root) stage

theorem blockLinearGlobalReversal_restriction (stage : ℕᵒᵖ) :
    blockLinearGlobalReversal ≫ blockLinearGlobalRestriction stage =
      blockLinearGlobalRestriction stage ≫
        (blockLinearReversalNatTrans seedOccurrence.root).app stage :=
  limMap_π (blockLinearReversalNatTrans seedOccurrence.root) stage

theorem blockLinearGlobalEuler_reversal_commutes :
    blockLinearGlobalEulerAction ≫ blockLinearGlobalReversal =
      blockLinearGlobalReversal ≫ blockLinearGlobalEulerAction := by
  apply limit.hom_ext
  intro stage
  calc
    (blockLinearGlobalEulerAction ≫ blockLinearGlobalReversal) ≫
        blockLinearGlobalRestriction stage =
      blockLinearGlobalRestriction stage ≫
        ((blockLinearEulerNatTrans seedOccurrence.root).app stage ≫
          (blockLinearReversalNatTrans seedOccurrence.root).app stage) := by
        rw [Category.assoc, blockLinearGlobalReversal_restriction,
          ← Category.assoc, blockLinearGlobalEulerAction_restriction,
          Category.assoc]
    _ = blockLinearGlobalRestriction stage ≫
        ((blockLinearReversalNatTrans seedOccurrence.root).app stage ≫
          (blockLinearEulerNatTrans seedOccurrence.root).app stage) := by
        change blockLinearGlobalRestriction stage ≫
            (blockDirectEulerAction seedOccurrence.root stage.unop ≫
              blockDirectReversal seedOccurrence.root stage.unop) =
          blockLinearGlobalRestriction stage ≫
            (blockDirectReversal seedOccurrence.root stage.unop ≫
              blockDirectEulerAction seedOccurrence.root stage.unop)
        rw [blockDirectEuler_reversal_commutes]
    _ = (blockLinearGlobalReversal ≫ blockLinearGlobalEulerAction) ≫
        blockLinearGlobalRestriction stage := by
      symm
      rw [Category.assoc, blockLinearGlobalEulerAction_restriction,
        ← Category.assoc, blockLinearGlobalReversal_restriction,
        Category.assoc]

def blockLinearDiagramOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      (ℕᵒᵖ ⥤ IntegralCochainComplex BlockCoordinateRing)) :=
  seedOccurrence.map fun seed => (seed, localBlockLinearDiagram seed)

theorem blockLinearDiagramOccurrence_projects :
    blockLinearDiagramOccurrence.map Prod.fst = seedOccurrence := by
  unfold blockLinearDiagramOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

def blockLinearGlobalStateOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × IntegralCochainComplex BlockCoordinateRing) :=
  seedOccurrence.map fun owner => (owner, BlockLinearGlobalState)

theorem blockLinearGlobalStateOccurrence_projects :
    blockLinearGlobalStateOccurrence.map Prod.fst = seedOccurrence := by
  unfold blockLinearGlobalStateOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_exact_block_linear_global_owner (stage : ℕᵒᵖ) :
    blockLinearDiagramOccurrence.map Prod.fst = seedOccurrence ∧
      blockLinearGlobalStateOccurrence.map Prod.fst = seedOccurrence ∧
      blockLinearGlobalEulerAction ≫ blockLinearGlobalRestriction stage =
        blockLinearGlobalRestriction stage ≫
          (blockLinearEulerNatTrans seedOccurrence.root).app stage ∧
      blockLinearGlobalReversal ≫ blockLinearGlobalRestriction stage =
        blockLinearGlobalRestriction stage ≫
          (blockLinearReversalNatTrans seedOccurrence.root).app stage := by
  exact ⟨blockLinearDiagramOccurrence_projects,
    blockLinearGlobalStateOccurrence_projects,
    blockLinearGlobalEulerAction_restriction stage,
    blockLinearGlobalReversal_restriction stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
