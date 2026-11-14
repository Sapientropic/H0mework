import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCellInverse

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCellHistory

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open OriginalRieszFinitePairing.CoPoisson.Ward
open RootGeneratedDebtActivationJointSource.OwnerFree
open scoped Topology

namespace Eval
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
  (value value_source trace paid_history original_material relation_boundary)
end Eval

abbrev CellValue := InventoryVector.VectorValue (Fin 2) (Value := CountedFiniteNative.Value)
abbrev Var := CountedFiniteNative.Var

def cutoff (N : Nat) : Fin 2 → Nat := ![N,N+1]

private def words (N : Nat) : List (Fin 2 × Expr CountedFiniteNative.Value Var ()) :=
  [(0, CountedFiniteNative.code N), (1, CountedFiniteNative.code (N+1))]

def cellCode (N : Nat) : Expr CellValue Var () := InventoryVector.query (Fin 2) (words N)

private theorem cell_eval (N : Nat) (x : BurnolL2) (i : Fin 2) :
    (cellCode N).eval (InventoryVector.environment (Fin 2) (fun _ _ => x)) i =
      (CountingDual.sourceCLM (cutoff N i)).adjoint x := by
  unfold cellCode
  rw [InventoryVector.query_read]
  fin_cases i <;> simp [words, cutoff, CountedFiniteNative.code, Expr.eval]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "after" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "born" => DirectRDivisionControls.bornRead observation nontrivial half depth (ordinal+1)
local notation "authority" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "origin" => CountedFiniteNative.current observation nontrivial half depth ordinal

/-- This continuation reads the original born inventory and records both adjacent cutoffs. -/
def reader (N : Nat) (_actual : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := CellValue) (Var := Var) (sort := ()) :=
  ⟨InventoryVector.environment (Fin 2) (fun _ _ => born), cellCode N⟩

local notation "readCell" => reader observation nontrivial half depth ordinal

def count (N : Nat) : CellValue () := Eval.value authority origin (readCell N)

open private born_raw from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedFiniteCutoffNative

theorem count_source (N : Nat) (i : Fin 2) :
    @Eq BurnolL2 (count observation nontrivial half depth ordinal N i) (DualSource.source (cutoff N i) after) := by
  have evaluated := congrFun (Eval.value_source authority origin (readCell N)) i
  have read : @Eq BurnolL2 (count observation nontrivial half depth ordinal N i)
      ((CountingDual.sourceCLM (cutoff N i)).adjoint born) := evaluated.trans (cell_eval N born i)
  exact read.trans ((congrArg (CountingDual.sourceCLM (cutoff N i)).adjoint
    (born_raw observation nontrivial half depth ordinal)).trans (CountingDual.dual_eq_adjoint (cutoff N i) _).symm)

theorem count_paid_steps (N : Nat) : (Eval.trace authority origin (readCell N)).length = 8 :=
  (Eval.paid_history authority origin (readCell N)).trans (InventoryVector.query_charge (Fin 2) (words N))

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "cell_same_root"

/-- The cell's exact authority retains its original material and its generated relation, whole and next. -/
theorem cell_same_root (N : Nat) :
    type_of% (Eval.original_material authority origin (readCell N)) ∧
    type_of% (Eval.relation_boundary (R := ℤ) authority origin (readCell N)) ∧
    type_of% (Relations.boundary_in_inventory authority origin (readCell N)
      (Calculation.targetRuntime authority origin (readCell N))) ∧
    type_of% (Calculation.target_factorizes authority origin (readCell N)) :=
  ⟨Eval.original_material authority origin (readCell N),
    Eval.relation_boundary (R := ℤ) authority origin (readCell N),
    Relations.boundary_in_inventory authority origin (readCell N) (Calculation.targetRuntime authority origin (readCell N)),
    Calculation.target_factorizes authority origin (readCell N)⟩

end CountedCellHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
