import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.State
import H0mework.Realization.Operations.Execution.Run

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open SourceOperationEffects SourceOperationExecution

noncomputable section

variable {Occurrence : Type} (index : Nat) (indexInRange : 1 ≤ index)

def sourceAt (occurrence : Occurrence) : EffectiveSplitAt index :=
  (CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
    occurrence index indexInRange).source

/-- The occurrence tag and full chronological cursor share one free carrier. -/
abbrev PointAt := (occurrence : Occurrence) × StateAt (sourceAt index indexInRange occurrence)

def nextPoint (point : PointAt (Occurrence := Occurrence) index indexInRange) :
    PointAt (Occurrence := Occurrence) index indexInRange :=
  ⟨point.1, next point.2⟩

def initialPoint (occurrence : Occurrence) : PointAt (Occurrence := Occurrence) index indexInRange :=
  ⟨occurrence, initial (sourceAt index indexInRange occurrence)⟩

def runPoint : Nat → PointAt (Occurrence := Occurrence) index indexInRange →
    PointAt (Occurrence := Occurrence) index indexInRange
  | 0, point => point
  | count + 1, point => runPoint count (nextPoint index indexInRange point)

theorem runPoint_fibre (count : Nat)
    (point : PointAt (Occurrence := Occurrence) index indexInRange) :
    runPoint index indexInRange count point = ⟨point.1, run count point.2⟩ := by
  induction count generalizing point with
  | zero => rfl
  | succ count previous => exact previous (nextPoint index indexInRange point)

theorem runPoint_succ_right (count : Nat)
    (point : PointAt (Occurrence := Occurrence) index indexInRange) :
    runPoint index indexInRange (count + 1) point =
      nextPoint index indexInRange (runPoint index indexInRange count point) := by
  induction count generalizing point with
  | zero => rfl
  | succ count previous => exact previous (nextPoint index indexInRange point)

abbrev Value (_ : Unit) := PointAt (Occurrence := Occurrence) index indexInRange →₀ ℤ
abbrev Var (_ : Unit) := Unit
abbrev Programme := Expr (Value (Occurrence := Occurrence) index indexInRange) Var Unit.unit

def action : (PointAt (Occurrence := Occurrence) index indexInRange →₀ ℤ) →+
    (PointAt (Occurrence := Occurrence) index indexInRange →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ (nextPoint index indexInRange)).toAddMonoidHom

def sourceEnvironment (occurrence : Occurrence) :
    Env (Value (Occurrence := Occurrence) index indexInRange) Var :=
  fun _ _ => Finsupp.single (initialPoint index indexInRange occurrence) 1

def pulses : Nat → Programme (Occurrence := Occurrence) index indexInRange
  | 0 => .var Unit.unit
  | count + 1 => .linear (action index indexInRange) (pulses count)

def sourceProgramme (occurrence : Occurrence) : Programme (Occurrence := Occurrence) index indexInRange :=
  pulses index indexInRange (sourceFuel (sourceAt index indexInRange occurrence))

theorem pulses_eval (count : Nat) (occurrence : Occurrence) :
    (pulses index indexInRange count).eval (sourceEnvironment index indexInRange occurrence) =
      Finsupp.single (runPoint index indexInRange count
        (initialPoint index indexInRange occurrence)) 1 := by
  induction count with
  | zero => rfl
  | succ count previous =>
      simp only [pulses, Expr.eval, previous, action, LinearMap.toAddMonoidHom_coe,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, runPoint_succ_right]

theorem sourceProgramme_eval (occurrence : Occurrence) :
    (sourceProgramme index indexInRange occurrence).eval
        (sourceEnvironment index indexInRange occurrence) =
      Finsupp.single (⟨occurrence, .completed
        (generate (sourceAt index indexInRange occurrence))⟩ : PointAt (Occurrence := Occurrence) index indexInRange) 1 := by
  rw [sourceProgramme, pulses_eval, runPoint_fibre]
  simp only [initialPoint, run_source]

theorem pulses_budget (count : Nat) :
    SourceOperationExecution.remaining
      (pulses (Occurrence := Occurrence) index indexInRange count) = count + 1 := by
  induction count with
  | zero => rfl
  | succ count previous =>
      simp only [pulses, SourceOperationExecution.remaining, previous]

theorem sourceProgramme_budget (occurrence : Occurrence) :
    SourceOperationExecution.remaining (sourceProgramme index indexInRange occurrence) =
      sourceFuel (sourceAt index indexInRange occurrence) + 1 :=
  pulses_budget index indexInRange _

def sourceTrace (occurrence : Occurrence) :
    Trace (sourceEnvironment index indexInRange occurrence)
      (sourceProgramme index indexInRange occurrence)
      (.const ((sourceProgramme index indexInRange occurrence).eval
        (sourceEnvironment index indexInRange occurrence))) :=
  execution (sourceEnvironment index indexInRange occurrence)
    (sourceProgramme index indexInRange occurrence)

theorem sourceTrace_length (occurrence : Occurrence) :
    (sourceTrace index indexInRange occurrence).length =
      sourceFuel (sourceAt index indexInRange occurrence) + 1 :=
  (execution_length _ _).trans (sourceProgramme_budget index indexInRange occurrence)

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
