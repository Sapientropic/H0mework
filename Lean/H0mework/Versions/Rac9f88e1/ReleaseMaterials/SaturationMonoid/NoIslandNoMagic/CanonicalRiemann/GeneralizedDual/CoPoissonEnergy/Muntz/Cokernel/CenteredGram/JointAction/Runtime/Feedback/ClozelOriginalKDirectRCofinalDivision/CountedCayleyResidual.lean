import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyIncrement

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 180000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyIncrement

open BurnolPhysicalState Filter RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
open CofinalHistorySettlement SourceOperationPaidRelations
open RootGeneratedDebtActivationJointSource.OwnerFree
open scoped InnerProductSpace Topology

local notation "V" => CountedCellHistory.CellValue
local notation "X" => CountedCellHistory.Var

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "authority" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "origin" => CountedFiniteNative.current observation nontrivial half depth ordinal
local notation "readIn" => CountedCayleyProgramme.reader observation nontrivial half depth ordinal
local notation "point" "[" j "]" => D.raw observation nontrivial half depth j
local notation "out" "[" j "]" => CountedCayleyProgramme.output observation nontrivial half depth j
local notation "changeBy" => increment observation nontrivial half depth ordinal

namespace Eval
export CountedCayleyProgramme.Eval (trace relation_boundary updated_inverse_fibre)
end Eval

def residualRead (N : Nat) (positive : 0 < N) (n : Nat) : V () :=
  let old := raw authority origin (readIn N positive n)
  let target := evaluation (R := ℤ) (s := ()) (old.environment + changeBy N positive n)
  let relation := relationMap (R := ℤ) old.environment
    (Eval.trace authority origin (readIn N positive n)).relationWords
  (residualEquivRange target (canonicalResidual target relation)).val

/-- The installed inverse fibre of the original actual terminal reads the full adjacent source update. -/
theorem actual_residual (N : Nat) (positive : 0 < N) (n : Nat) :
    let values := residualRead observation nontrivial half depth ordinal N positive n
    (values 0,values 1) = out[ordinal+1] N positive n-out[ordinal] N positive n := by
  let old := raw authority origin (readIn N positive n)
  let delta := changeBy N positive n
  let trace := Eval.trace authority origin (readIn N positive n)
  let rel := relationMap (R := ℤ) old.environment trace.relationWords
  let effect := old.expression.effect old.environment delta
  have fibre : residualRead observation nontrivial half depth ordinal N positive n =
      effectEvaluator (R := ℤ) old.environment delta rel :=
    Eval.updated_inverse_fibre (R := ℤ) authority origin (readIn N positive n) delta
  have paid : rel = Finsupp.single old.expression 1 -
      Finsupp.single (.const (CountedCayleyProgramme.Eval.value authority origin (readIn N positive n))) 1 :=
    Eval.relation_boundary (R := ℤ) authority origin (readIn N positive n)
  have seen : effectEvaluator (R := ℤ) old.environment delta rel = effect := by
    rw [paid]
    simp only [effect, map_sub, effectEvaluator, Finsupp.linearCombination_single, one_smul,
      Expr.effect, sub_zero]
  exact (congrArg (fun values : V () => (values 0, values 1)) (fibre.trans seen)).trans
    (actual_effect observation nontrivial half depth ordinal N positive n)

/-- The actual terminal residual keeps the full physical increment through the finite entrance limit. -/
theorem actual_residual_tendsto (N : Nat) (positive : 0 < N) :
    Tendsto (fun n =>
      let values := residualRead observation nontrivial half depth ordinal N positive n
      (values 0,values 1)) atTop
      (𝓝 ((point[ordinal+1+1],point[ordinal+1+1+1])-(point[ordinal+1],point[ordinal+1+1]))) := by
  have first := CountedCayleyWriteback.actual_entrance observation nontrivial half depth ordinal N positive
  have second := CountedCayleyWriteback.actual_entrance observation nontrivial half depth (ordinal+1) N positive
  exact (second.sub first).congr' (Eventually.of_forall fun n =>
    (actual_residual observation nontrivial half depth ordinal N positive n).symm)

private theorem exposure_cast {environment : Env V X} {source first last : Expr V X ()}
    (trace : Trace environment source first) (endpoint : first = last) :
    exposure (Eq.mp (congrArg (fun expression => Trace environment source expression) endpoint) trace) =
      exposure trace := by
  cases endpoint
  rfl

/-- The terminal trace is exactly the exposure installed by the original runtime. -/
theorem installed_terminal_exposure (N : Nat) (positive : 0 < N) (n : Nat) :
    let runtime := Calculation.targetRuntime authority origin (readIn N positive n)
    let parent := CountedCayleyProgramme.terminalTrace observation nontrivial half depth ordinal N positive n
    exposure parent = Relations.exposure authority origin (readIn N positive n) runtime := by
  let runtime := Calculation.targetRuntime authority origin (readIn N positive n)
  let reader := readIn N positive n
  let parent := CountedCayleyProgramme.terminalTrace observation nontrivial half depth ordinal N positive n
  have endpoint := CountedCayleyProgramme.Eval.target_expression authority origin reader
  have same : exposure parent = exposure (Eval.trace authority origin reader) :=
    exposure_cast (Eval.trace authority origin reader) endpoint
  exact same.trans (Relations.complete_paid_events authority origin reader runtime).symm

/-- The complete cofinal relation closure is the installed terminal closure. -/
theorem installed_relation_closure (N : Nat) (positive : 0 < N) (n : Nat) :
    let runtime := Calculation.targetRuntime authority origin (readIn N positive n)
    let parent := CountedCayleyProgramme.terminalTrace observation nontrivial half depth ordinal N positive n
    let root := RootedAccountedUnfolding.zero ((authority).emitted origin)
    (prefixHistory root (exposure parent)).relationClosure =
      (Relations.history authority origin (readIn N positive n) runtime).relationClosure := by
  let runtime := Calculation.targetRuntime authority origin (readIn N positive n)
  let reader := readIn N positive n
  let parent := CountedCayleyProgramme.terminalTrace observation nontrivial half depth ordinal N positive n
  let root := RootedAccountedUnfolding.zero ((authority).emitted origin)
  have printed := installed_terminal_exposure observation nontrivial half depth ordinal N positive n
  have keeps (event : PresentedRelationEventAt (Expr V X ())) (present : event ∈ (exposure parent).trace) :
      event ∈ (Relations.exposure authority origin reader runtime).trace :=
    congrArg (fun observed => event ∈ observed.trace) printed ▸ present
  have reflects (event : PresentedRelationEventAt (Expr V X ()))
      (present : event ∈ (Relations.exposure authority origin reader runtime).trace) :
      event ∈ (exposure parent).trace :=
    congrArg (fun observed => event ∈ observed.trace) printed.symm ▸ present
  let emitted := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let actual := Relations.exposure authority origin reader runtime
  exact le_antisymm
    (relations_next root (exposure parent) emitted actual keeps)
    (relations_next emitted actual root (exposure parent) reflects)

/-- Recover child charges directly from the relation closure installed at the actual terminal. -/
def installedCountedFibre (N : Nat) (positive : 0 < N) (n : Nat) :=
  let fibre := CountedCayleyRelations.countedRelationFibre observation nontrivial half depth ordinal N positive n
  let closure := installed_relation_closure observation nontrivial half depth ordinal N positive n
  let into := Submodule.inclusion closure.le
  let back := Submodule.inclusion closure.ge
  (into.comp fibre.1,fibre.2.val.comp back)

theorem installed_counted_recover (N : Nat) (positive : 0 < N) (n : Nat) :
    let installed := installedCountedFibre observation nontrivial half depth ordinal N positive n
    Function.LeftInverse installed.2 installed.1 := by
  let fibre := CountedCayleyRelations.countedRelationFibre observation nontrivial half depth ordinal N positive n
  let closure := installed_relation_closure observation nontrivial half depth ordinal N positive n
  dsimp only
  intro relation
  have same : Submodule.inclusion closure.ge (Submodule.inclusion closure.le (fibre.1 relation)) =
      fibre.1 relation := Subtype.ext rfl
  exact (congrArg fibre.2.val same).trans (fibre.2.property relation)

end CountedCayleyIncrement
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
