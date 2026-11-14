import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyResidualInverse

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyResidualRecovery

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift
open RootGeneratedDebtActivationJointSource.OwnerFree
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open CountedCayleyResidualInverse (approximate approximate_succ)
open CountedCayleyResidualInverse.Geom (clock driveScale finite_zero)

open private liftExpr_remaining from H0mework.Realization.Operations.Execution.Coefficients.Words

local notation "V" => CountedCellHistory.CellValue
local notation "X" => CountedCellHistory.Var
local notation "Bank" => PairValue V
local notation "Resolvent" => burnolDirectRightResolventCLM
local notation "d" => sourceDamping

private def initial : Bank () →+ Bank () :=
  (AddMonoidHom.snd _ _).prod 0

private def advance (c : BurnolCompletedMellinCoordinate) : Bank () →+ Bank () :=
  let applyClock := InventoryVector.linear (Fin 2) (clock (Resolvent c) (d c)).toAddMonoidHom
  let applyDrive := InventoryVector.linear (Fin 2)
    ((driveScale (d c) • ContinuousLinearMap.id ℂ BurnolL2).toAddMonoidHom)
  let data := AddMonoidHom.fst (V ()) (V ())
  let current := AddMonoidHom.snd (V ()) (V ())
  data.prod (applyClock.comp current + applyDrive.comp data)

private def programme (c : BurnolCompletedMellinCoordinate) (seed : Expr Bank X ()) :
    Nat → Expr Bank X ()
  | 0 => .linear initial seed
  | rounds+1 => .linear (advance c) (programme c seed rounds)

private theorem programme_charge (c : BurnolCompletedMellinCoordinate) (seed : Expr Bank X ()) (m : Nat) :
    remaining (programme c seed m) = remaining seed+1+m := by
  induction m with
  | zero => rfl
  | succ m previous => simp only [programme, remaining, previous, Nat.add_succ]

private theorem programme_source (c : BurnolCompletedMellinCoordinate) (seed : Expr Bank X ())
    (environment : Env Bank X) (m : Nat) :
    let source := (seed.eval environment).2
    (programme c seed m).eval environment = (source,fun i => approximate c m (source i)) := by
  let source := (seed.eval environment).2
  induction m with
  | zero =>
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      change (0 : BurnolL2) = approximate c 0 (source i)
      simp only [approximate, finite_zero, zero_apply]
  | succ m previous =>
    change advance c ((programme c seed m).eval environment) = _
    rw [previous]
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      change clock (Resolvent c) (d c) (approximate c m (source i)) + driveScale (d c) • source i =
        approximate c (m+1) (source i)
      exact (approximate_succ c m (source i)).symm

private def retainedSeed {c : BurnolCompletedMellinCoordinate} {seed : Expr Bank X ()}
    {environment : Env Bank X} :
    (m : Nat) → {result : Bank ()} →
    (actual : Trace environment (programme c seed m) (.const result)) → Trace.SourceReceipt actual seed
  | 0, _, actual =>
    let cut := actual.splitLinear
    ⟨cut.input,cut.trace,.linear cut (.refl _)⟩
  | m+1, _, actual =>
    let cut := actual.splitLinear
    let inner := retainedSeed m cut.trace
    ⟨inner.value,inner.trace,.linear cut inner.retained⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "authority" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "origin" => CountedFiniteNative.current observation nontrivial half depth ordinal
local notation "readIn" => CountedCayleyProgramme.reader observation nontrivial half depth ordinal
local notation "delta" => CountedCayleyIncrement.increment observation nontrivial half depth ordinal
local notation "residual" => CountedCayleyIncrement.residualRead observation nontrivial half depth ordinal

/-- The source occurrence supplies the old bank and its actual adjacent environment increment. -/
def reader (N : Nat) (positive : 0 < N) (n m : Nat)
    (actual : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := Bank) (Var := X) (sort := ()) :=
  let old := readIn N positive n actual
  ⟨pairEnvironment old.environment (delta N positive n),
    programme c (liftExpr old.expression) m⟩

local notation "readBack" => reader observation nontrivial half depth ordinal

namespace Eval
export CountedCayleyProgramme.Eval
  (trace value value_source paid_history original_material relation_boundary relation_cochain target_expression)
end Eval

def terminal (N : Nat) (positive : 0 < N) (n m : Nat) : Bank () :=
  Eval.value authority origin (readBack N positive n m)

theorem terminal_source (N : Nat) (positive : 0 < N) (n m : Nat) :
    terminal observation nontrivial half depth ordinal N positive n m =
      (residual N positive n,fun i => approximate c m (residual N positive n i)) := by
  let old := raw authority origin (readIn N positive n)
  let increment := delta N positive n
  have residualEffect : old.expression.effect old.environment increment = residual N positive n := by
    let read := CountedCayleyIncrement.actual_residual observation nontrivial half depth ordinal N positive n
    let paid := CountedCayleyIncrement.actual_effect observation nontrivial half depth ordinal N positive n
    have pairs : (old.expression.effect old.environment increment 0,old.expression.effect old.environment increment 1) =
        (residual N positive n 0,residual N positive n 1) := paid.trans read.symm
    funext i
    fin_cases i
    · exact congrArg (Prod.fst : BurnolL2 × BurnolL2 → BurnolL2) pairs
    · exact congrArg (Prod.snd : BurnolL2 × BurnolL2 → BurnolL2) pairs
  have seed := congrArg Prod.snd (eval_liftExpr old.expression old.environment increment)
  unfold terminal
  rw [Eval.value_source]
  change (programme c (liftExpr old.expression) m).eval (pairEnvironment old.environment increment) = _
  rw [programme_source, seed, residualEffect]

def terminalTrace (N : Nat) (positive : 0 < N) (n m : Nat) :
    Trace (raw authority origin (readBack N positive n m)).environment
      (raw authority origin (readBack N positive n m)).expression
      (.const (terminal observation nontrivial half depth ordinal N positive n m)) := by
  unfold terminal
  rw [← Eval.target_expression authority origin (readBack N positive n m)]
  exact Eval.trace authority origin (readBack N positive n m)

/-- This is the paired birth calculation inside the actual finite inverse run. -/
def pairedChild (N : Nat) (positive : 0 < N) (n m : Nat) :
    Trace.SourceReceipt (terminalTrace observation nontrivial half depth ordinal N positive n m)
      (liftExpr (raw authority origin (readIn N positive n)).expression) :=
  retainedSeed m (terminalTrace observation nontrivial half depth ordinal N positive n m)

theorem paired_child_source (N : Nat) (positive : 0 < N) (n m : Nat) :
    let child := pairedChild observation nontrivial half depth ordinal N positive n m
    let source := raw authority origin (readIn N positive n)
    child.value = (Eval.value authority origin (readIn N positive n),
      source.expression.effect source.environment (delta N positive n)) ∧
    child.trace.length = 10+n := by
  let old := raw authority origin (readIn N positive n)
  let child := pairedChild observation nontrivial half depth ordinal N positive n m
  let increment := delta N positive n
  have birth : child.value = (liftExpr old.expression).eval (pairEnvironment old.environment increment) :=
    child.trace.sound.symm
  have paid : remaining old.expression = 10+n :=
    (Eval.paid_history authority origin (readIn N positive n)).symm.trans
      (CountedCayleyProgramme.paid_steps observation nontrivial half depth ordinal N positive n)
  exact ⟨birth.trans ((eval_liftExpr old.expression old.environment increment).trans
    (congrArg (fun value => (value,old.expression.effect old.environment increment))
      (Eval.value_source authority origin (readIn N positive n)).symm)),
    child.trace.length_to_const.trans ((liftExpr_remaining old.expression).trans paid)⟩

theorem paid_rounds (N : Nat) (positive : 0 < N) (n m : Nat) :
    (Eval.trace authority origin (readBack N positive n m)).length = 10+n+1+m := by
  let old := raw authority origin (readIn N positive n)
  have paid : remaining old.expression = 10+n :=
    (Eval.paid_history authority origin (readIn N positive n)).symm.trans
      (CountedCayleyProgramme.paid_steps observation nontrivial half depth ordinal N positive n)
  rw [Eval.paid_history]
  change remaining (programme c (liftExpr old.expression) m) = _
  rw [programme_charge, liftExpr_remaining, paid]

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_recovery"

/-- The original runtime records the complete relation of the finite recovery and emits its successor. -/
theorem actual_paid_recovery (N : Nat) (positive : 0 < N) (n m : Nat) :
    type_of% (paired_child_source observation nontrivial half depth ordinal N positive n m) ∧
    type_of% (paid_rounds observation nontrivial half depth ordinal N positive n m) ∧
    type_of% (Eval.original_material authority origin (readBack N positive n m)) ∧
    type_of% (Eval.relation_boundary (R := ℤ) authority origin (readBack N positive n m)) ∧
    type_of% (Relations.boundary_in_inventory authority origin (readBack N positive n m)
      (Calculation.targetRuntime authority origin (readBack N positive n m))) ∧
    type_of% (Calculation.target_factorizes authority origin (readBack N positive n m)) :=
  ⟨paired_child_source observation nontrivial half depth ordinal N positive n m,
    paid_rounds observation nontrivial half depth ordinal N positive n m,
    Eval.original_material authority origin (readBack N positive n m),
    Eval.relation_boundary (R := ℤ) authority origin (readBack N positive n m),
    Relations.boundary_in_inventory authority origin (readBack N positive n m)
      (Calculation.targetRuntime authority origin (readBack N positive n m)),
    Calculation.target_factorizes authority origin (readBack N positive n m)⟩

end CountedCayleyResidualRecovery
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
