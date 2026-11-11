import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.Relation.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Words

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFullRBlockRelationWrite
open Complex RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction (BaseValue)
end F
namespace Pa
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa (CodeValue)
end Pa
namespace DR
export OriginalKSourceDifferentialResidualAction (sourceLiftOperator completeRSourceAction)
namespace L
export OriginalKSourceDifferentialResidualAction.L (Value groups)
end L
end DR
namespace P
export OriginalKSourceResidualRNativeSuccessor (sourcePaLift sourceNonPaLift)
end P
namespace E
export OriginalKFullRBlockRelationSource
  (PhysicalValue PhysicalBranches sourceP sourceN sourceR npAction npUnitSource np_action_source
   pnAction pnInverseSource pn_action_source)
end E
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR

local instance baseGroups (initial : Nat) : ∀ target, AddCommGroup (F.BaseValue initial target) :=
  DR.L.groups (PairValue OriginalKFullSourceRAction.C.Value) initial
local instance originGroups (initial : Nat) : ∀ target, AddCommGroup
    (DR.L.Value (F.BaseValue initial) 2 target) := DR.L.groups (F.BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ target, AddCommGroup
    (DR.L.Value (DR.L.Value (F.BaseValue initial) 2) 0 target) :=
  DR.L.groups (DR.L.Value (F.BaseValue initial) 2) 0

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)

private def baseLift (initial : Nat) (action : E.PhysicalBranches →+ E.PhysicalBranches) :=
  DR.sourceLiftOperator (W := PairValue OriginalKFullSourceRAction.C.Value) action initial

private theorem base_equations (initial : Nat)
    (value : PairValue (F.BaseValue initial) ()) :
    let p := baseLift initial E.sourceP.toLinearMap.toAddMonoidHom
    let r := baseLift initial (E.sourceR observation nontrivial half).toLinearMap.toAddMonoidHom
    let u := baseLift initial (E.npUnitSource observation nontrivial half).toLinearMap.toAddMonoidHom
    let v := baseLift initial (E.pnInverseSource observation nontrivial half).toAddMonoidHom
    r (p value) - p (r (p value)) = u value ∧
      p (r (value - p value)) = v value := by
  induction initial with
  | zero =>
      constructor
      · exact congrArg (fun action : E.PhysicalBranches →L[ℂ] E.PhysicalBranches => action value)
          (E.np_action_source observation nontrivial half)
      · exact LinearMap.congr_fun (E.pn_action_source observation nontrivial half) value
  | succ initial previous =>
      constructor
      · exact Prod.ext (previous value.1).1 (previous value.2).1
      · exact Prod.ext (previous value.1).2 (previous value.2).2

variable (initial : Nat)

def codeLift (action : E.PhysicalBranches →+ E.PhysicalBranches) :
    Pa.CodeValue initial () →+ Pa.CodeValue initial () :=
  DR.sourceLiftOperator (W := DR.L.Value (F.BaseValue initial) 2)
    (DR.sourceLiftOperator (W := F.BaseValue initial) (baseLift initial action) 2) 0

def npAction : Pa.CodeValue initial () →+ Pa.CodeValue initial () :=
  (P.sourceNonPaLift initial 2 0).comp
    ((DR.completeRSourceAction observation nontrivial half initial 2 0).comp
      (P.sourcePaLift initial 2 0))

def pnAction : Pa.CodeValue initial () →+ Pa.CodeValue initial () :=
  (P.sourcePaLift initial 2 0).comp
    ((DR.completeRSourceAction observation nontrivial half initial 2 0).comp
      (P.sourceNonPaLift initial 2 0))

def npSource : Pa.CodeValue initial () →+ Pa.CodeValue initial () :=
  codeLift initial (E.npUnitSource observation nontrivial half).toLinearMap.toAddMonoidHom

def pnSource : Pa.CodeValue initial () →+ Pa.CodeValue initial () :=
  codeLift initial (E.pnInverseSource observation nontrivial half).toAddMonoidHom

private theorem complete_equations (value : Pa.CodeValue initial ()) :
    npAction observation nontrivial half initial value = npSource observation nontrivial half initial value ∧
    pnAction observation nontrivial half initial value = pnSource observation nontrivial half initial value := by
  constructor
  · exact Prod.ext
      (Prod.ext (base_equations observation nontrivial half initial value.1.1).1
        (base_equations observation nontrivial half initial value.1.2).1)
      (Prod.ext (base_equations observation nontrivial half initial value.2.1).1
        (base_equations observation nontrivial half initial value.2.2).1)
  · exact Prod.ext
      (Prod.ext (base_equations observation nontrivial half initial value.1.1).2
        (base_equations observation nontrivial half initial value.1.2).2)
      (Prod.ext (base_equations observation nontrivial half initial value.2.1).2
        (base_equations observation nontrivial half initial value.2.2).2)

theorem np_action_source :
    npAction observation nontrivial half initial = npSource observation nontrivial half initial :=
  AddMonoidHom.ext fun value => (complete_equations observation nontrivial half initial value).1

theorem pn_action_source :
    pnAction observation nontrivial half initial = pnSource observation nontrivial half initial :=
  AddMonoidHom.ext fun value => (complete_equations observation nontrivial half initial value).2

variable {Var : Unit → Type}

def npCode (body : Expr (Pa.CodeValue initial) Var ()) : Expr (Pa.CodeValue initial) Var () :=
  .linear (s := ()) (t := ()) (P.sourceNonPaLift initial 2 0)
    (.linear (s := ()) (t := ()) (DR.completeRSourceAction observation nontrivial half initial 2 0)
      (.linear (s := ()) (t := ()) (P.sourcePaLift initial 2 0) body))

def pnCode (body : Expr (Pa.CodeValue initial) Var ()) : Expr (Pa.CodeValue initial) Var () :=
  .linear (s := ()) (t := ()) (P.sourcePaLift initial 2 0)
    (.linear (s := ()) (t := ()) (DR.completeRSourceAction observation nontrivial half initial 2 0)
      (.linear (s := ()) (t := ()) (P.sourceNonPaLift initial 2 0) body))

def npSourceCode (body : Expr (Pa.CodeValue initial) Var ()) : Expr (Pa.CodeValue initial) Var () :=
  .linear (s := ()) (t := ()) (npSource observation nontrivial half initial) body

def pnSourceCode (body : Expr (Pa.CodeValue initial) Var ()) : Expr (Pa.CodeValue initial) Var () :=
  .linear (s := ()) (t := ()) (pnSource observation nontrivial half initial) body

theorem np_code_eval_source (body : Expr (Pa.CodeValue initial) Var ())
    (environment : Env (Pa.CodeValue initial) Var) :
    (npCode observation nontrivial half initial body).eval environment =
      (npSourceCode observation nontrivial half initial body).eval environment :=
  DFunLike.congr_fun (np_action_source observation nontrivial half initial) (body.eval environment)

theorem pn_code_eval_source (body : Expr (Pa.CodeValue initial) Var ())
    (environment : Env (Pa.CodeValue initial) Var) :
    (pnCode observation nontrivial half initial body).eval environment =
      (pnSourceCode observation nontrivial half initial body).eval environment :=
  DFunLike.congr_fun (pn_action_source observation nontrivial half initial) (body.eval environment)

theorem np_code_effect_source (body : Expr (Pa.CodeValue initial) Var ())
    (environment increment : Env (Pa.CodeValue initial) Var) :
    (npCode observation nontrivial half initial body).effect environment increment =
      (npSourceCode observation nontrivial half initial body).effect environment increment := by
  have actual := Expr.eval_update (npCode observation nontrivial half initial body) environment increment
  have source := Expr.eval_update (npSourceCode observation nontrivial half initial body) environment increment
  rw [np_code_eval_source observation nontrivial half initial body environment,
    np_code_eval_source observation nontrivial half initial body (environment + increment)] at actual
  exact add_left_cancel (actual.symm.trans source)

theorem pn_code_effect_source (body : Expr (Pa.CodeValue initial) Var ())
    (environment increment : Env (Pa.CodeValue initial) Var) :
    (pnCode observation nontrivial half initial body).effect environment increment =
      (pnSourceCode observation nontrivial half initial body).effect environment increment := by
  have actual := Expr.eval_update (pnCode observation nontrivial half initial body) environment increment
  have source := Expr.eval_update (pnSourceCode observation nontrivial half initial body) environment increment
  rw [pn_code_eval_source observation nontrivial half initial body environment,
    pn_code_eval_source observation nontrivial half initial body (environment + increment)] at actual
  exact add_left_cancel (actual.symm.trans source)

def npWord (body : Expr (Pa.CodeValue initial) Var ()) : Formal ℤ (Pa.CodeValue initial) Var () :=
  Finsupp.single (npCode observation nontrivial half initial body) 1 -
    Finsupp.single (npSourceCode observation nontrivial half initial body) 1

def pnWord (body : Expr (Pa.CodeValue initial) Var ()) : Formal ℤ (Pa.CodeValue initial) Var () :=
  Finsupp.single (pnCode observation nontrivial half initial body) 1 -
    Finsupp.single (pnSourceCode observation nontrivial half initial body) 1

theorem np_word_eval (body : Expr (Pa.CodeValue initial) Var ())
    (environment : Env (Pa.CodeValue initial) Var) :
    evaluation (R := ℤ) environment (npWord observation nontrivial half initial body) = 0 := by
  simp only [npWord, map_sub, evaluation, Finsupp.linearCombination_single, one_smul]
  exact sub_eq_zero.mpr (np_code_eval_source observation nontrivial half initial body environment)

theorem pn_word_eval (body : Expr (Pa.CodeValue initial) Var ())
    (environment : Env (Pa.CodeValue initial) Var) :
    evaluation (R := ℤ) environment (pnWord observation nontrivial half initial body) = 0 := by
  simp only [pnWord, map_sub, evaluation, Finsupp.linearCombination_single, one_smul]
  exact sub_eq_zero.mpr (pn_code_eval_source observation nontrivial half initial body environment)

theorem np_code_source_distinct (body : Expr (Pa.CodeValue initial) Var ()) :
    npCode observation nontrivial half initial body ≠ npSourceCode observation nontrivial half initial body := by
  intro same
  have costs := congrArg remaining same
  simp only [npCode, npSourceCode, remaining] at costs
  omega

theorem pn_code_source_distinct (body : Expr (Pa.CodeValue initial) Var ()) :
    pnCode observation nontrivial half initial body ≠ pnSourceCode observation nontrivial half initial body := by
  intro same
  have costs := congrArg remaining same
  simp only [pnCode, pnSourceCode, remaining] at costs
  omega

abbrev Inventory := SourceInventoryExecutionFeed.Inventory (V := Pa.CodeValue initial) (X := Var) (s := ())

def written (source : Inventory initial (Var := Var)) (body : Expr (Pa.CodeValue initial) Var ()) :
    Inventory initial (Var := Var) :=
  match source with
  | .occur origin branches => .occur origin (branches.append
      (.cons (.zero (.relation (npWord observation nontrivial half initial body)))
        (.cons (.zero (.relation (pnWord observation nontrivial half initial body))) .nil)))

theorem written_root (source : Inventory initial (Var := Var)) (body : Expr (Pa.CodeValue initial) Var ()) :
    (written observation nontrivial half initial source body).root = source.root := by
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

theorem written_trace (source : Inventory initial (Var := Var)) (body : Expr (Pa.CodeValue initial) Var ()) :
    (written observation nontrivial half initial source body).trace = source.trace ++
      [.relation (npWord observation nontrivial half initial body),
        .relation (pnWord observation nontrivial half initial body)] := by
  cases source with
  | occur origin branches =>
      change origin :: RootedAccountedUnfolding.traceBranches (branches.append _) = _
      rw [traceBranches_append]
      rfl

theorem old_preserved (source : Inventory initial (Var := Var)) (body : Expr (Pa.CodeValue initial) Var ()) :
    ∀ event ∈ source.trace, event ∈ (written observation nontrivial half initial source body).trace := by
  intro event present
  rw [written_trace]
  exact List.mem_append_left _ present

def npOccurrence (source : Inventory initial (Var := Var)) (body : Expr (Pa.CodeValue initial) Var ()) :
    WR.RelationOccurrence (written observation nontrivial half initial source body) :=
  ⟨source.trace, npWord observation nontrivial half initial body,
    [.relation (pnWord observation nontrivial half initial body)],
    written_trace observation nontrivial half initial source body⟩

def pnOccurrence (source : Inventory initial (Var := Var)) (body : Expr (Pa.CodeValue initial) Var ()) :
    WR.RelationOccurrence (written observation nontrivial half initial source body) := by
  refine ⟨source.trace ++ [.relation (npWord observation nontrivial half initial body)],
    pnWord observation nontrivial half initial body, [], ?_⟩
  simpa only [List.append_assoc, List.singleton_append, List.append_nil] using
    written_trace observation nontrivial half initial source body

end OriginalKFullRBlockRelationWrite
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
