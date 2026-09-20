import H0mework.Realization.SourceComparison.Recovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.SourceComparison

universe u v
variable {source : Dynamics.{u}} {target : Dynamics.{v}}

def emittedPayload (source : Dynamics.{u}) (index : ℕ) : Sigma source.EventAt :=
  ⟨currentAt source index, source.emit (currentAt source index)⟩

def Map.payload (map : Map source target) (actual : Sigma source.EventAt) : Sigma target.EventAt :=
  ⟨map.state actual.1, map.event actual.2⟩

theorem Map.payload_generated (map : Map source target) (index : ℕ) :
    map.payload (emittedPayload source index) = emittedPayload target index := by
  unfold payload emittedPayload
  rw [map.emitted, map.generated]

/-- Complete finite actual input records retain their source states and
events. In particular, repeated states do not merge distinct visits. -/
def trace (source : Dynamics.{u}) (index : ℕ) : List (Sigma source.EventAt) :=
  (List.range (index+1)).map (emittedPayload source)

theorem trace_length (source : Dynamics.{u}) (index : ℕ) : (trace source index).length = index+1 := by
  simp only [trace, List.length_map, List.length_range]

theorem trace_injective (source : Dynamics.{u}) : Function.Injective (trace source) := by
  intro first last same
  have lengths := congrArg List.length same
  simpa only [trace_length, Nat.add_right_cancel_iff] using lengths

theorem Map.trace_generated (map : Map source target) (index : ℕ) :
    (trace source index).map map.payload = trace target index := by
  simp only [trace, List.map_map, Function.comp_def, map.payload_generated]

abbrev History (source : Dynamics.{u}) := Set.range (trace source)

def historyAt (source : Dynamics.{u}) (index : ℕ) : History source :=
  ⟨trace source index, index, rfl⟩

def Map.history (map : Map source target) (past : History source) : History target :=
  ⟨past.val.map map.payload, by
    rcases past.property with ⟨index, same⟩
    exact ⟨index, (map.trace_generated index).symm.trans (congrArg (List.map map.payload) same)⟩⟩

theorem Map.history_at (map : Map source target) (index : ℕ) :
    map.history (historyAt source index) = historyAt target index :=
  Subtype.ext (map.trace_generated index)

def historyRecovery (forward : Map source target) (backward : Map target source) :
    History source ≃ History target where
  toFun := forward.history
  invFun := backward.history
  left_inv past := by
    rcases past with ⟨_, index, rfl⟩
    change backward.history (forward.history (historyAt source index)) = historyAt source index
    rw [forward.history_at, backward.history_at]
  right_inv past := by
    rcases past with ⟨_, index, rfl⟩
    change forward.history (backward.history (historyAt target index)) = historyAt target index
    rw [backward.history_at, forward.history_at]

def visit (past : History source) := RawGeneratedRoot.visitAt source (past.val.length-1)

theorem visit_at (index : ℕ) : visit (historyAt source index) = RawGeneratedRoot.visitAt source index := by
  simp only [visit, historyAt, trace_length, Nat.add_sub_cancel]

theorem Map.history_length (map : Map source target) (past : History source) :
    (map.history past).val.length = past.val.length := List.length_map _

theorem Map.history_current (map : Map source target) (past : History source) :
    map.state (visit past).current = (visit (map.history past)).current := by
  change map.state (RawGeneratedRoot.visitAt source (past.val.length-1)).current =
    (RawGeneratedRoot.visitAt target ((map.history past).val.length-1)).current
  rw [map.history_length, RawGeneratedRoot.visit_current, RawGeneratedRoot.visit_current, map.generated]

theorem Map.history_update (map : Map source target) (past : History source) :
    map.state (source.update (source.emit (visit past).current)) =
      target.update (target.emit (visit (map.history past)).current) := by
  exact (map.updated _).trans
    ((congrArg target.update (map.emitted (visit past).current)).trans
      (congrArg (fun current => target.update (target.emit current)) (map.history_current past)))

theorem Map.whole_row (map : Map source target) (past : History source) :
    (RawGeneratedRoot.generatedSuccessor source (source.emit (visit past).current)).ledgerEvolution.destination
        (RawGeneratedRoot.entry source (visit past).current) =
      ⟨RawGeneratedRoot.entry source (source.update (source.emit (visit past).current)),
        .transferred (source.emit (visit past).current) rfl rfl (Nat.le_refl _)⟩ ∧
    (RawGeneratedRoot.generatedSuccessor target (target.emit (visit (map.history past)).current)).ledgerEvolution.destination
        (RawGeneratedRoot.entry target (visit (map.history past)).current) =
      ⟨RawGeneratedRoot.entry target (target.update (target.emit (visit (map.history past)).current)),
        .transferred (target.emit (visit (map.history past)).current) rfl rfl (Nat.le_refl _)⟩ ∧
    map.state (RawGeneratedRoot.generatedSuccessor source (source.emit (visit past).current)).targetCurrent =
      (RawGeneratedRoot.generatedSuccessor target (target.emit (visit (map.history past)).current)).targetCurrent := by
  exact ⟨RawGeneratedRoot.generated_ledger source _, RawGeneratedRoot.generated_ledger target _, map.history_update past⟩

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.SourceComparison
