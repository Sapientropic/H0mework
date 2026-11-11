import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.Relation.Write
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFullRBlockRelationInstall

open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement

namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction (BaseValue)
end F
namespace Pa
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa (CodeValue)
end Pa
namespace E
export OriginalKFullRBlockRelationWrite (npWord pnWord)
end E
namespace T
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (liftEvent)
end T

local instance baseGroups (initial : Nat) : ∀ target, AddCommGroup (F.BaseValue initial target) :=
  OriginalKSourceDifferentialResidualAction.L.groups (PairValue OriginalKFullSourceRAction.C.Value) initial

variable (initial : Nat) (Var : Unit → Type)
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

abbrev PairInventory :=
 SourceInventoryExecutionFeed.Inventory
  (V := PairValue (Pa.CodeValue initial)) (X := Var) (s := ())

def pairRelation (word : Formal ℤ (Pa.CodeValue initial) Var ()) :
    PresentedRelationEventAt (Expr (PairValue (Pa.CodeValue initial)) Var ()) :=
  .relation (SourceOperationScalarInventoryLift.liftMap (R := ℤ) word)

def pairWritten (source : PairInventory initial Var) (body : Expr (Pa.CodeValue initial) Var ()) :
    PairInventory initial Var :=
  match source with
  | .occur origin branches =>
      .occur origin (branches.append
        (.cons (.zero (pairRelation initial Var
          (E.npWord observation nontrivial half initial body)))
          (.cons (.zero (pairRelation initial Var
            (E.pnWord observation nontrivial half initial body))) .nil)))

theorem pairWritten_root (source : PairInventory initial Var) (body : Expr (Pa.CodeValue initial) Var ()) :
    (pairWritten initial Var observation nontrivial half source body).root = source.root := by
  cases source
  rfl

private theorem traceBranches_append {A : Type} (first second : AccountedBranches A) :
    RootedAccountedUnfolding.traceBranches (first.append second) =
      RootedAccountedUnfolding.traceBranches first ++ RootedAccountedUnfolding.traceBranches second := by
  cases first with
  | nil => rfl
  | cons head tail =>
      change head.trace ++ RootedAccountedUnfolding.traceBranches (tail.append second) =
        (head.trace ++ RootedAccountedUnfolding.traceBranches tail) ++ RootedAccountedUnfolding.traceBranches second
      rw [traceBranches_append tail second, List.append_assoc]

theorem pairWritten_trace (source : PairInventory initial Var) (body : Expr (Pa.CodeValue initial) Var ()) :
    (pairWritten initial Var observation nontrivial half source body).trace = source.trace ++
      [pairRelation initial Var (E.npWord observation nontrivial half initial body),
       pairRelation initial Var (E.pnWord observation nontrivial half initial body)] := by
  cases source with
  | occur origin branches =>
      change origin :: RootedAccountedUnfolding.traceBranches (branches.append _) = _
      rw [traceBranches_append]
      rfl

theorem pairWritten_preserves (source : PairInventory initial Var) (body : Expr (Pa.CodeValue initial) Var ()) :
    ∀ event ∈ source.trace, event ∈
      (pairWritten initial Var observation nontrivial half source body).trace := by
  intro event present
  rw [pairWritten_trace]
  exact List.mem_append_left _ present

def pair_np_occurrence (source : PairInventory initial Var) (body : Expr (Pa.CodeValue initial) Var ()) :
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence
      (pairWritten initial Var observation nontrivial half source body) :=
  ⟨source.trace, SourceOperationScalarInventoryLift.liftMap (R := ℤ)
      (E.npWord observation nontrivial half initial body),
    [pairRelation initial Var (E.pnWord observation nontrivial half initial body)],
    pairWritten_trace initial Var observation nontrivial half source body⟩

def pair_pn_occurrence (source : PairInventory initial Var) (body : Expr (Pa.CodeValue initial) Var ()) :
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence
      (pairWritten initial Var observation nontrivial half source body) := by
  refine ⟨source.trace ++ [pairRelation initial Var
      (E.npWord observation nontrivial half initial body)],
    SourceOperationScalarInventoryLift.liftMap (R := ℤ)
      (E.pnWord observation nontrivial half initial body), [], ?_⟩
  simpa only [pairRelation, List.append_assoc, List.singleton_append, List.append_nil] using
    pairWritten_trace initial Var observation nontrivial half source body

end OriginalKFullRBlockRelationInstall
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
