import H0mework.Versions.Rdf421ff6.Foundation.Runtime.Inquiry

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootInquiryCompletion
namespace SourceNativeInquiryRuntime

variable {process : SourceNativeInquiryEngineProcess.{u}}

abbrev ActivatedAt (runtime : SourceNativeInquiryRuntime process) :=
  Σ state : runtime.State, ExactActivatedInquiryOccurrenceAt state

/-- Read a stored token and its dependent runtime state from the same finite execution. -/
def HistoryAt.occurrenceAt {runtime : SourceNativeInquiryRuntime process}
    {fuel : Nat} {state : runtime.State} (history : HistoryAt runtime fuel state) :
    Fin fuel → ActivatedAt runtime :=
  Nat.rec (motive := fun fuel => ∀ {state : runtime.State},
      HistoryAt runtime fuel state → Fin fuel → ActivatedAt runtime)
    (fun {_} _ => Fin.elim0)
    (fun _ prior {_} history i => by
      cases history with
      | step activated tail => exact Fin.cases ⟨_,activated⟩ (prior tail) i)
    fuel history

/-- The finite execution exposes the exact canonical token at each stored address. -/
theorem occurrenceAt_runFrom (runtime : SourceNativeInquiryRuntime process)
    (start fuel : Nat) (i : Fin fuel) :
    (runFrom fuel (runtime.stateAt start)).occurrenceAt i =
      ⟨runtime.stateAt (start+i.val),(runtime.stateAt (start+i.val)).tick⟩ := by
  induction fuel generalizing start with
  | zero => exact Fin.elim0 i
  | succ fuel prior =>
    refine Fin.cases ?_ (fun next => ?_) i
    · change (⟨runtime.stateAt start,(runtime.stateAt start).tick⟩ : ActivatedAt runtime) =
        ⟨runtime.stateAt (start+0),(runtime.stateAt (start+0)).tick⟩
      rw [Nat.add_zero]
    · change (runFrom fuel (runtime.stateAt (start+1))).occurrenceAt next =
        ⟨runtime.stateAt (start+next.succ.val),(runtime.stateAt (start+next.succ.val)).tick⟩
      rw [prior]
      rw [show start+1+next.val=start+next.succ.val by simp only [Fin.val_succ]; omega]

theorem occurrenceAt_run (runtime : SourceNativeInquiryRuntime process) (fuel : Nat) (i : Fin fuel) :
    (runtime.run fuel).occurrenceAt i = ⟨runtime.stateAt i.val,(runtime.stateAt i.val).tick⟩ := by
  have stored := occurrenceAt_runFrom runtime 0 fuel i
  rw [Nat.zero_add i.val] at stored
  exact stored

/-- Restrict the stored execution to an earlier length, preserving the actual dependent tokens. -/
def HistoryAt.prefix {runtime : SourceNativeInquiryRuntime process}
    {fuel : Nat} {state : runtime.State} (history : HistoryAt runtime fuel state)
    (length : Nat) (within : length ≤ fuel) : HistoryAt runtime length state :=
  Nat.rec (motive := fun length => ∀ {fuel : Nat} {state : runtime.State},
      HistoryAt runtime fuel state → length ≤ fuel → HistoryAt runtime length state)
    (fun {_ state} _ _ => .exhausted state)
    (fun length prior {_ _} history within => by
      cases history with
      | exhausted => exact False.elim (Nat.not_succ_le_zero length within)
      | step activated tail => exact .step activated (prior tail (Nat.le_of_succ_le_succ within)))
    length history within

theorem prefix_runFrom (runtime : SourceNativeInquiryRuntime process) (state : runtime.State)
    (fuel length : Nat) (within : length ≤ fuel) :
    (runFrom fuel state).prefix length within = runFrom length state := by
  induction fuel generalizing state length with
  | zero =>
    have empty : length = 0 := Nat.eq_zero_of_le_zero within
    subst length
    rfl
  | succ fuel prior =>
    cases length with
    | zero => rfl
    | succ length =>
      change HistoryAt.step state.tick
          ((runFrom fuel state.tick.nextState).prefix length (Nat.le_of_succ_le_succ within)) =
        HistoryAt.step state.tick (runFrom length state.tick.nextState)
      rw [prior]

/-- Extract a subexecution with its actual dependent starting state. -/
def HistoryAt.window {runtime : SourceNativeInquiryRuntime process}
    {fuel : Nat} {state : runtime.State} (history : HistoryAt runtime fuel state)
    (offset length : Nat) (within : offset+length ≤ fuel) :
    Σ reached : runtime.State, HistoryAt runtime length reached :=
  Nat.rec (motive := fun offset => ∀ {fuel : Nat} {state : runtime.State},
      HistoryAt runtime fuel state → offset+length ≤ fuel →
        Σ reached : runtime.State, HistoryAt runtime length reached)
    (fun {_ state} history within => ⟨state,history.prefix length (Nat.zero_add length ▸ within)⟩)
    (fun _ prior {_ _} history within => by
      cases history with
      | exhausted => omega
      | step _ tail => exact prior tail (by omega))
    offset history within

theorem window_runFrom (runtime : SourceNativeInquiryRuntime process) (start fuel offset length : Nat)
    (within : offset+length ≤ fuel) :
    (runFrom fuel (runtime.stateAt start)).window offset length within =
      ⟨runtime.stateAt (start+offset),runFrom length (runtime.stateAt (start+offset))⟩ := by
  induction fuel generalizing start offset with
  | zero =>
    have empty : offset = 0 := by omega
    have none : length = 0 := by omega
    subst offset
    subst length
    rfl
  | succ fuel previous =>
    cases offset with
    | zero =>
      change (⟨runtime.stateAt start,(runFrom (fuel+1) (runtime.stateAt start)).prefix length _⟩ :
          Σ reached : runtime.State, HistoryAt runtime length reached) = _
      rw [prefix_runFrom,Nat.add_zero start]
    | succ offset =>
      change (runFrom fuel (runtime.stateAt (start+1))).window offset length _ = _
      rw [previous]
      rw [show start+1+offset = start+(offset+1) by omega]

theorem window_run (runtime : SourceNativeInquiryRuntime process) (fuel offset length : Nat)
    (within : offset+length ≤ fuel) :
    (runtime.run fuel).window offset length within =
      ⟨runtime.stateAt offset,runFrom length (runtime.stateAt offset)⟩ := by
  have stored := window_runFrom runtime 0 fuel offset length within
  rw [Nat.zero_add offset] at stored
  exact stored

end SourceNativeInquiryRuntime
end RootInquiryCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
