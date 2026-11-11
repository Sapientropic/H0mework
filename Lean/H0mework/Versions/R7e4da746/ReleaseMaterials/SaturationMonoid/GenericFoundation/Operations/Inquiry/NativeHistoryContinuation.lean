import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.NativeHistoryLookup

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootInquiryCompletion.SourceNativeInquiryRuntime

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable {runtime : SourceNativeInquiryRuntime process}

/-- A stored history is determined by its sealed starting state and length. -/
theorem HistoryAt.eq_runFrom {fuel : Nat} {state : runtime.State} (history : HistoryAt runtime fuel state) :
    history = runFrom fuel state := by
  induction history with
  | exhausted => rfl
  | @step fuel state activated tail previous =>
    calc
      HistoryAt.step activated tail =
        HistoryAt.step activated (runFrom fuel activated.nextState) :=
        congrArg (HistoryAt.step activated) previous
      _ = runFrom (fuel+1) state := by
        simp only [runFrom]

-- Explicit elimination keeps the stored state field in the generated code.
@[noinline] private def storedStart {fuel : Nat} {state : runtime.State}
    (history : HistoryAt runtime fuel state) : runtime.State :=
  HistoryAt.casesOn (motive := fun _ _ _ => runtime.State) history
    (fun reached => reached) (fun {_} {current} _ _ => current)

private theorem stored_start_eq {fuel : Nat} {state : runtime.State}
    (history : HistoryAt runtime fuel state) : storedStart history = state := by
  cases history <;> rfl

private def withStoredStart {fuel : Nat} {state : runtime.State}
    (history : HistoryAt runtime fuel state) : HistoryAt runtime fuel (storedStart history) :=
  Eq.mp (congrArg (HistoryAt runtime fuel) (stored_start_eq history).symm) history

/-- Look up an exact occurrence by reading stored states along the path. -/
def HistoryAt.storedOccurrenceAt {fuel : Nat} {state : runtime.State}
    (history : HistoryAt runtime fuel state) : Fin fuel → ActivatedAt runtime :=
  Nat.rec (motive := fun fuel => ∀ {state : runtime.State},
      HistoryAt runtime fuel state → Fin fuel → ActivatedAt runtime)
    (fun {_} _ => Fin.elim0)
    (fun _ previous {_} history i => by
      cases history with
      | step activated tail =>
        exact Fin.cases ⟨_,activated⟩ (previous (withStoredStart tail)) i)
    fuel history

private theorem occurrenceAt_cast {fuel : Nat} {old new : runtime.State} (same : old = new)
    (history : HistoryAt runtime fuel old) (i : Fin fuel) :
    (Eq.mp (congrArg (HistoryAt runtime fuel) same) history).occurrenceAt i = history.occurrenceAt i := by
  cases same
  rfl

theorem HistoryAt.stored_occurrence_eq {fuel : Nat} {state : runtime.State}
    (history : HistoryAt runtime fuel state) (i : Fin fuel) :
    history.storedOccurrenceAt i = history.occurrenceAt i := by
  induction fuel generalizing state with
  | zero => exact Fin.elim0 i
  | succ fuel previous =>
    cases history with
    | step activated tail =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change (withStoredStart tail).storedOccurrenceAt j = tail.occurrenceAt j
        rw [previous]
        exact occurrenceAt_cast (stored_start_eq tail).symm tail j

/-- Reuse the stored activations and start new execution only at the reached tail state. -/
def HistoryAt.continueFor {fuel : Nat} {state : runtime.State} (history : HistoryAt runtime fuel state)
    (extra : Nat) : HistoryAt runtime (extra+fuel) state :=
  Nat.rec (motive := fun fuel => ∀ {state : runtime.State},
      HistoryAt runtime fuel state → HistoryAt runtime (extra+fuel) state)
    (fun {_} history =>
      Eq.mp (congrArg (HistoryAt runtime extra) (stored_start_eq history))
        (runFrom extra (storedStart history)))
    (fun fuel previous {_} history => by
      cases history with
      | step activated tail =>
        exact .step activated
          (Eq.mp (congrArg (HistoryAt runtime (extra+fuel)) (stored_start_eq tail))
            (previous (withStoredStart tail))))
    fuel history

/-- Extend to an absolute horizon by generating precisely the missing suffix. -/
def HistoryAt.extendTo {fuel : Nat} {state : runtime.State} (history : HistoryAt runtime fuel state)
    (total : Nat) (within : fuel ≤ total) : HistoryAt runtime total state :=
  Eq.mp (congrArg (fun length => HistoryAt runtime length state) (Nat.sub_add_cancel within))
    (history.continueFor (total-fuel))

theorem HistoryAt.extendTo_prefix {fuel : Nat} {state : runtime.State} (history : HistoryAt runtime fuel state)
    (total : Nat) (within : fuel ≤ total) :
    (history.extendTo total within).prefix fuel within = history := by
  rw [(history.extendTo total within).eq_runFrom,prefix_runFrom]
  exact history.eq_runFrom.symm

end RootInquiryCompletion.SourceNativeInquiryRuntime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
