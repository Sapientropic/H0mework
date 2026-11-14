import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedFiniteCutoff
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Realization.Operations.Execution.InventoryVector.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Relations.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open OriginalRieszFinitePairing.CoPoisson.Ward SourceGeneratedQuadrature
open RootGeneratedDebtActivationJointSource.OwnerFree
open scoped Topology

namespace CountedFiniteNative

namespace Eval
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history original_material relation_boundary)
end Eval

abbrev Value (_ : Unit) := BurnolL2
abbrev Var (_ : Unit) := Unit
abbrev BankValue := InventoryVector.VectorValue (Fin 3) (Value := Value)

local instance : ∀ target, AddCommGroup (Value target) := fun _ =>
  inferInstanceAs (AddCommGroup BurnolL2)

def code (N : Nat) : Expr Value Var () :=
  .linear (s := ()) ((CountingDual.sourceCLM N).adjoint.toLinearMap.toAddMonoidHom) (.var (s := ()) ())

def cutoff (m : Nat) : Fin 3 → Nat :=
  ![m+1, doubledCut m+1, doubledCut (doubledCut m)+1]

private def words (m : Nat) : List (Fin 3 × Expr Value Var ()) :=
  [(0, code (cutoff m 0)), (1, code (cutoff m 1)), (2, code (cutoff m 2))]

def bankCode (m : Nat) : Expr BankValue Var () := InventoryVector.query (Fin 3) (words m)

private theorem bank_eval (m : Nat) (x : BurnolL2) (i : Fin 3) :
    (bankCode m).eval (InventoryVector.environment (Fin 3) (fun _ _ => x)) i =
      (CountingDual.sourceCLM (cutoff m i)).adjoint x := by
  unfold bankCode
  rw [InventoryVector.query_read]
  fin_cases i <;> simp [words, code, Expr.eval]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "after" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "born" => DirectRDivisionControls.bornRead observation nontrivial half depth (ordinal+1)

abbrev root := OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth (ordinal+1+1)
abbrev current := OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth (ordinal+1+1)

local notation "authority" => root observation nontrivial half depth ordinal
local notation "origin" => current observation nontrivial half depth ordinal

/-- The count bank reads the complete branch inventory at the literal Division birth. -/
def reader (m : Nat) (_actual : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := BankValue) (Var := Var) (sort := ()) :=
  ⟨InventoryVector.environment (Fin 3) (fun _ _ => born), bankCode m⟩

local notation "atCut" => reader observation nontrivial half depth ordinal

def count (m : Nat) : BankValue () := Eval.value authority origin (atCut m)

private theorem born_raw : @Eq BurnolL2 born after :=
  (Parent.Full.complete_of_branches observation nontrivial half _ _
    (OriginalKDirectRCofinalMaterial.actual_successor_branches observation nontrivial half depth
      (ordinal+1))).2.2.1.trans (D.raw_successor observation nontrivial half depth (ordinal+1)).symm

theorem count_source (m : Nat) (i : Fin 3) :
    @Eq BurnolL2 (count observation nontrivial half depth ordinal m i) (DualSource.source (cutoff m i) after) := by
  have evaluated := congrFun (Eval.value_source authority origin (atCut m)) i
  have read : @Eq BurnolL2 (count observation nontrivial half depth ordinal m i)
      ((CountingDual.sourceCLM (cutoff m i)).adjoint born) := evaluated.trans (bank_eval m born i)
  exact read.trans ((congrArg (CountingDual.sourceCLM (cutoff m i)).adjoint
    (born_raw observation nontrivial half depth ordinal)).trans (CountingDual.dual_eq_adjoint (cutoff m i) _).symm)

theorem count_paid_steps (m : Nat) : (Eval.trace authority origin (atCut m)).length = 12 := by
  exact (Eval.paid_history authority origin (atCut m)).trans (InventoryVector.query_charge (Fin 3) (words m))

-- Retain the complete dependent receipt without expanding it in editor suggestions.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "count_same_root"

/-- The actual source material and registered relation accompany whole-ledger and canonical next. -/
theorem count_same_root (m : Nat) :
    type_of% (Eval.original_material authority origin (atCut m)) ∧
    type_of% (Eval.relation_boundary (R := ℤ) authority origin (atCut m)) ∧
    type_of% (Relations.boundary_in_inventory authority origin (atCut m)
      (Calculation.targetRuntime authority origin (atCut m))) ∧
    type_of% (Calculation.target_factorizes authority origin (atCut m)) :=
  ⟨Eval.original_material authority origin (atCut m),
    Eval.relation_boundary (R := ℤ) authority origin (atCut m),
    Relations.boundary_in_inventory authority origin (atCut m) (Calculation.targetRuntime authority origin (atCut m)),
    Calculation.target_factorizes authority origin (atCut m)⟩

end CountedFiniteNative

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
