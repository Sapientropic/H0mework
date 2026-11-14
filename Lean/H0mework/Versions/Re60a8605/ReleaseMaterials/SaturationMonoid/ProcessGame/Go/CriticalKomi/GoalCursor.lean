import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.DecisionCursor
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.GoalBracket

/-!
The fixed original initial position drives its own threshold calculation.
Unfinished observations retain the exact query continuation; completed queries
retain both unilateral guarantees in a smaller integer bracket.  Only equal
certified bounds produce the final value and its executable policies.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.GoalCursor

structure State where
  bracket : GoalBracket.Bracket
  queryThreshold : Int
  query : DecisionCursor.Cursor queryThreshold (Frame.initial 19)
  query_valid : bracket.lower = bracket.upper ∨
    (bracket.lower ≤ queryThreshold ∧ queryThreshold < bracket.upper)
  received : List GoalBracket.InitialBound := []

/-- The first source inquiry constructs the executable eight-area guarantee.
The mathematical lower bound zero is a separate already-paid fact. -/
def initialStrategyThreshold : Int := 2 * 8 - 361 - 1

def initial : State where
  bracket := GoalBracket.initial
  queryThreshold := initialStrategyThreshold
  query := DecisionCursor.initial19 initialStrategyThreshold
  query_valid := by right; constructor <;> decide

/-- Queue actual original-initial strategy data. Source producers call this
mouth after constructing their certificate, at any unilateral margin. -/
def State.receive (current : State) (bound : GoalBracket.InitialBound) : State :=
  { current with received := current.received ++ [bound] }

def State.receiveCertificate (current : State) {colour : Polarity} {value : Int}
    (certificate : Certificate colour value (Frame.initial 19)) : State :=
  current.receive (GoalBracket.InitialBound.ofCertificate certificate)

/-- Only an improved cut restarts its query. Weaker data and unchanged cuts
retain the previously generated original query continuation. -/
def absorb (current : State) (bound : GoalBracket.InitialBound) : ExactInitialMargin ⊕ State :=
  if bound.Improves current.bracket then
    let nextBracket := current.bracket.absorb bound
    if settled : nextBracket.lower = nextBracket.upper then
      .inl (nextBracket.finish settled)
    else
      .inr {
        bracket := nextBracket
        queryThreshold := nextBracket.cut
        query := if same : nextBracket.cut = current.queryThreshold then
          same ▸ current.query else DecisionCursor.initial19 nextBracket.cut
        query_valid := .inr (nextBracket.cut_bounds (by
          have ordered := nextBracket.lower_le_upper
          omega))
        received := current.received
      }
  else .inr current

def advance (current : State) : ExactInitialMargin ⊕ State :=
  match current.received with
  | bound :: later => absorb {current with received := later} bound
  | [] =>
      if settled : current.bracket.lower = current.bracket.upper then
        .inl (current.bracket.finish settled)
      else
        match DecisionCursor.emit current.query with
        | .inr next => .inr {current with query := next}
        | .inl answer => .inr (current.receive (GoalBracket.InitialBound.ofAnswer answer))

theorem advance_receipt (current : State) (bound : GoalBracket.InitialBound)
    (later : List GoalBracket.InitialBound) (received : current.received = bound :: later) :
    advance current = absorb {current with received := later} bound := by
  simp only [advance, received]

theorem absorb_not_improving (current : State) (bound : GoalBracket.InitialBound)
    (stable : ¬ bound.Improves current.bracket) : absorb current bound = .inr current := by
  simp only [absorb, stable, ↓reduceIte]

theorem query_answer_improves (current : State)
    (answer : Answer current.queryThreshold (Frame.initial 19))
    (unsettled : current.bracket.lower ≠ current.bracket.upper) :
    (GoalBracket.InitialBound.ofAnswer answer).Improves current.bracket := by
  have bounds := current.query_valid.resolve_left unsettled
  cases answer with
  | white certificate => exact bounds.2
  | black certificate =>
      change current.bracket.lower < current.queryThreshold + 1
      omega

theorem advance_generated_receipt (current : State)
    (answer : Answer current.queryThreshold (Frame.initial 19))
    (empty : current.received = []) (unsettled : current.bracket.lower ≠ current.bracket.upper)
    (emitted : DecisionCursor.emit current.query = .inl answer) :
    advance current = .inr (current.receive (GoalBracket.InitialBound.ofAnswer answer)) := by
  simp only [advance, empty, unsettled, ↓reduceDIte, emitted]

/-- Calculation support distinguishes an unfinished native query from an actual answer. -/
inductive Current where
  | calculating (state : State)
  | solved (solution : ExactInitialMargin)

def generatedNext (current : State) : Current :=
  match advance current with
  | .inl solution => .solved solution
  | .inr next => .calculating next

def seed : Current := .calculating initial

/-- Fuel observes source computation; it does not alter the mathematical terminal criterion. -/
def observe : Nat → Current → Current
  | 0, current => current
  | _ + 1, .solved solution => .solved solution
  | fuel + 1, .calculating state => observe fuel (generatedNext state)

theorem observe_zero (current : Current) : observe 0 current = current := rfl

theorem solved_stable (fuel : Nat) (solution : ExactInitialMargin) :
    observe fuel (.solved solution) = .solved solution := by
  cases fuel <;> rfl

end SaturationMonoid.ProcessGame.Go.CriticalKomi.GoalCursor
