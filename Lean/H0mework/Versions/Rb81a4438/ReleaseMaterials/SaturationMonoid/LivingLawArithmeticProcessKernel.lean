import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawArithmeticFreeClosureKernel

/-!
# Canonical arithmetic process compiler

Deep derived arithmetic is compiled into a finite source-generated history of
local material operations.  The caller supplies no state, evaluator, trace,
normal form or result.  The material normal form is lossless: decoding it
recovers the exact mathematical occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ArithmeticProcess

open ArithmeticGeneration
open ArithmeticFreeClosure

universe u v

/-- Local operations of the canonical arithmetic material process. -/
inductive ArithmeticProcessStage : Type
  | material
  | parallelCoupling
  | jointInteraction
  | phaseShift
  | dualization
  | ledgerDebit
  deriving DecidableEq

/-- The material normal form is the same one-constructor exposure.  Process
names below are compatibility builders for its arithmetic directions, not a
second syntax universe. -/
abbrev ArithmeticProcessNormalForm : Type := DerivedArithmeticOccurrence

namespace ArithmeticProcessNormalForm

def material (history : UnitHistory) : ArithmeticProcessNormalForm :=
  .atom history

def parallelCoupling (left right : ArithmeticProcessNormalForm) :
    ArithmeticProcessNormalForm :=
  .parallel left right

def jointInteraction (left right : ArithmeticProcessNormalForm) :
    ArithmeticProcessNormalForm :=
  .joint left right

def phaseShift (prior : ArithmeticProcessNormalForm) :
    ArithmeticProcessNormalForm :=
  .shift prior

def dualization (prior : ArithmeticProcessNormalForm) :
    ArithmeticProcessNormalForm :=
  .dual prior

def ledgerDebit (source target : ArithmeticProcessNormalForm) :
    ArithmeticProcessNormalForm :=
  .cofiber source target

/-- Decoding is now the identity readout of the same exposure. -/
def toOccurrence (normalForm : ArithmeticProcessNormalForm) :
    DerivedArithmeticOccurrence :=
  normalForm

/-- Euler/K₀ readout of the physical process. -/
def eulerShadow (normalForm : ArithmeticProcessNormalForm) : Int :=
  normalForm.toOccurrence.eulerShadow

/-- Determinant readout of the same process. -/
def determinantShadow
    {Carrier : Type u} [CommGroup Carrier]
    (atomAt : UnitHistory → Carrier) :
    ArithmeticProcessNormalForm → Carrier :=
  fun normalForm => normalForm.toOccurrence.determinantShadow atomAt

theorem eulerShadow_eq_toOccurrence
    (normalForm : ArithmeticProcessNormalForm) :
    normalForm.eulerShadow = normalForm.toOccurrence.eulerShadow :=
  rfl

theorem determinantShadow_eq_toOccurrence
    {Carrier : Type u} [CommGroup Carrier]
    (atomAt : UnitHistory → Carrier)
    (normalForm : ArithmeticProcessNormalForm) :
    normalForm.determinantShadow atomAt =
      normalForm.toOccurrence.determinantShadow atomAt :=
  rfl

end ArithmeticProcessNormalForm

/-- Normalization is the identity face readout. -/
def normalize (occurrence : DerivedArithmeticOccurrence) :
    ArithmeticProcessNormalForm :=
  occurrence

/-- The process compiler is a lossless folding representation. -/
@[simp] theorem normalize_toOccurrence
    (occurrence : DerivedArithmeticOccurrence) :
    (normalize occurrence).toOccurrence = occurrence :=
  rfl

theorem normalize_injective : Function.Injective normalize := by
  intro left right equality
  exact equality

@[simp] theorem normalize_eulerShadow
    (occurrence : DerivedArithmeticOccurrence) :
    (normalize occurrence).eulerShadow = occurrence.eulerShadow := by
  rw [ArithmeticProcessNormalForm.eulerShadow_eq_toOccurrence,
    normalize_toOccurrence]

@[simp] theorem normalize_determinantShadow
    {Carrier : Type u} [CommGroup Carrier]
    (atomAt : UnitHistory → Carrier)
    (occurrence : DerivedArithmeticOccurrence) :
    (normalize occurrence).determinantShadow atomAt =
      occurrence.determinantShadow atomAt := by
  rw [ArithmeticProcessNormalForm.determinantShadow_eq_toOccurrence,
    normalize_toOccurrence]

def stageAtDirection : DerivedArithmeticDirection → ArithmeticProcessStage
  | .material _ => .material
  | .sibling => .parallelCoupling
  | .dependent => .jointInteraction
  | .phase => .phaseShift
  | .dual => .dualization
  | .frontier => .ledgerDebit

/-- Canonical post-order process history is a fold of the same exposure. -/
def stageHistory (occurrence : DerivedArithmeticOccurrence) :
    List ArithmeticProcessStage :=
  RootedAccountedUnfolding.fold
    (fun direction (children : List (List ArithmeticProcessStage)) =>
      List.flatten children ++ [stageAtDirection direction]) occurrence

def finalStage (occurrence : DerivedArithmeticOccurrence) :
    ArithmeticProcessStage :=
  stageAtDirection occurrence.root

@[simp] theorem stageHistory_getLast?
    (occurrence : DerivedArithmeticOccurrence) :
    (stageHistory occurrence).getLast? = some (finalStage occurrence) := by
  cases occurrence with
  | occur direction branches =>
      simp [stageHistory, finalStage, RootedAccountedUnfolding.root,
        RootedAccountedUnfolding.fold]

/-- Cost is itself an unindexed unit history; `Nat` appears only through its
cardinal shadow. -/
def historyCost : List ArithmeticProcessStage → UnitHistory
  | [] => .empty
  | _stage :: prior => .next (historyCost prior)

@[simp] theorem historyCost_cardinalShadow
    (history : List ArithmeticProcessStage) :
    (historyCost history).cardinalShadow = history.length := by
  induction history with
  | nil => rfl
  | cons stage prior inductionHypothesis =>
      change Nat.succ (historyCost prior).cardinalShadow =
        Nat.succ prior.length
      exact congrArg Nat.succ inductionHypothesis

/-- Zero-field generated process indexed by the mathematical occurrence. -/
structure SourceGeneratedArithmeticProcessAt
    (occurrence : DerivedArithmeticOccurrence) : Type where
  private mk ::

def compile (occurrence : DerivedArithmeticOccurrence) :
    SourceGeneratedArithmeticProcessAt occurrence :=
  ⟨⟩

namespace SourceGeneratedArithmeticProcessAt

def history
    {occurrence : DerivedArithmeticOccurrence}
    (_process : SourceGeneratedArithmeticProcessAt occurrence) :
    List ArithmeticProcessStage :=
  stageHistory occurrence

def cost
    {occurrence : DerivedArithmeticOccurrence}
    (process : SourceGeneratedArithmeticProcessAt occurrence) : UnitHistory :=
  historyCost process.history

def normalForm
    {occurrence : DerivedArithmeticOccurrence}
    (_process : SourceGeneratedArithmeticProcessAt occurrence) :
    ArithmeticProcessNormalForm :=
  normalize occurrence

@[simp] theorem normalForm_toOccurrence
    {occurrence : DerivedArithmeticOccurrence}
    (process : SourceGeneratedArithmeticProcessAt occurrence) :
    process.normalForm.toOccurrence = occurrence :=
  normalize_toOccurrence occurrence

@[simp] theorem normalForm_eulerShadow
    {occurrence : DerivedArithmeticOccurrence}
    (process : SourceGeneratedArithmeticProcessAt occurrence) :
    process.normalForm.eulerShadow = occurrence.eulerShadow :=
  normalize_eulerShadow occurrence

@[simp] theorem normalForm_determinantShadow
    {occurrence : DerivedArithmeticOccurrence}
    (process : SourceGeneratedArithmeticProcessAt occurrence)
    {Carrier : Type u} [CommGroup Carrier]
    (atomAt : UnitHistory → Carrier) :
    process.normalForm.determinantShadow atomAt =
      occurrence.determinantShadow atomAt :=
  normalize_determinantShadow atomAt occurrence

@[simp] theorem history_getLast?
    {occurrence : DerivedArithmeticOccurrence}
    (process : SourceGeneratedArithmeticProcessAt occurrence) :
    process.history.getLast? = some (finalStage occurrence) :=
  stageHistory_getLast? occurrence

theorem unique
    {occurrence : DerivedArithmeticOccurrence}
    (left right : SourceGeneratedArithmeticProcessAt occurrence) :
    left = right := by
  cases left
  cases right
  rfl

end SourceGeneratedArithmeticProcessAt

/-! ## Free-closure process -/

inductive FreeClosureProcessStage : Type
  | base
  | extend
  deriving DecidableEq

def freeClosureHistory
    {Base : Type u} {Direction : Type v} :
    FreeClosureAt Base Direction → List FreeClosureProcessStage
  | .base _ => [.base]
  | .extend _ prior => freeClosureHistory prior ++ [.extend]

def freeClosureFinalStage
    {Base : Type u} {Direction : Type v} :
    FreeClosureAt Base Direction → FreeClosureProcessStage
  | .base _ => .base
  | .extend _ _ => .extend

@[simp] theorem freeClosureHistory_getLast?
    {Base : Type u} {Direction : Type v}
    (node : FreeClosureAt Base Direction) :
    (freeClosureHistory node).getLast? =
      some (freeClosureFinalStage node) := by
  cases node <;> simp [freeClosureHistory, freeClosureFinalStage]

structure SourceGeneratedFreeClosureProcessAt
    {Base : Type u} {Direction : Type v}
    (node : FreeClosureAt Base Direction) : Type where
  private mk ::

def compileFreeClosure
    {Base : Type u} {Direction : Type v}
    (node : FreeClosureAt Base Direction) :
    SourceGeneratedFreeClosureProcessAt node :=
  ⟨⟩

namespace SourceGeneratedFreeClosureProcessAt

def history
    {Base : Type u} {Direction : Type v}
    {node : FreeClosureAt Base Direction}
    (_process : SourceGeneratedFreeClosureProcessAt node) :
    List FreeClosureProcessStage :=
  freeClosureHistory node

@[simp] theorem history_getLast?
    {Base : Type u} {Direction : Type v}
    {node : FreeClosureAt Base Direction}
    (process : SourceGeneratedFreeClosureProcessAt node) :
    process.history.getLast? =
      some (freeClosureFinalStage node) :=
  freeClosureHistory_getLast? node

theorem unique
    {Base : Type u} {Direction : Type v}
    {node : FreeClosureAt Base Direction}
    (left right : SourceGeneratedFreeClosureProcessAt node) :
    left = right := by
  cases left
  cases right
  rfl

end SourceGeneratedFreeClosureProcessAt
end ArithmeticProcess
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
