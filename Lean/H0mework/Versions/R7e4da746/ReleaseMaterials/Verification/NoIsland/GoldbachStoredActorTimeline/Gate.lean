import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Timeline

set_option autoImplicit false
noncomputable section

universe r u m

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

open SourceOperationEffects SourceOperationRuntime SourceOperationScalarRelations

private theorem indexed_material_is_the_original_pair_and_environments
    {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
    {Sorts : Type u} {Value Var : Sorts → Type (max r u)} [∀ s, AddCommGroup (Value s)]
    {Material : Type m} [AddCommGroup Material]
    (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)
    {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    let table := history.storedTimeline readMaterial
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate (runtime.advance i.val)
    (table.get i.castSucc,table.get i.succ) =
        (readMaterial (runtime.advance i.val).state, readMaterial (runtime.advance (i.val+1)).state) ∧
    timelineEnvironments environment table i =
        (oldEnvironment readMaterial environment stage,incrementEnvironment readMaterial environment stage) :=
  ⟨(history.stored_timeline_adjacent readMaterial i).trans
      (congrArg (Prod.map readMaterial readMaterial) (history.stored_pair_actual i)),
    timeline_environments_actual environment readMaterial history i⟩

#eval IO.println "CP598_CONTROL + indexed_material_is_the_original_pair_and_environments"

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Timeline
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActuality
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirect

set_option cleanup.letToHave false in
private theorem complete_readout_preserves_every_original_pulse (depth : Nat) :
    let readout := sourceReadout depth
    (∀ i : Fin (budget depth),
      let stage := SourceGeneratedRuntimeMaterialStageAt.generate ((mathTail depth).advance i.val)
      readout.1 i = (oldEnvironment (readMaterial depth) (environment depth) stage,
        incrementEnvironment (readMaterial depth) (environment depth) stage) ∧
        type_of% (stored_actor_increment depth i.val i.isLt)) ∧
    (∀ count : Nat, (within : count ≤ budget depth) → type_of% (stored_actor_prefix depth count within)) ∧
    (∀ i : Fin (budget depth+1), type_of% (stored_whole_and_next depth i)) :=
  ⟨fun i => ⟨source_readout_pulse depth i, stored_actor_increment depth i.val i.isLt⟩,
    fun count within => stored_actor_prefix depth count within, fun i => stored_whole_and_next depth i⟩

#eval IO.println "CP598_CONTROL + complete_readout_preserves_every_original_pulse"

private def livePulse (depth bound : Nat) (within : bound < budget depth) (i : Fin (bound+1)) :
    Fin (budget depth) :=
  ⟨i.val,Nat.lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) within⟩

private abbrev pulseRuntime (depth : Nat) (pulse : Fin (budget depth)) :=
  (mathTail depth).advance pulse.val

private abbrev nextPulseEvaluation (depth : Nat) (pulse : Fin (budget depth)) :=
  Fibre.evaluation (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth)
    (pulseRuntime depth pulse).tick.next

set_option cleanup.letToHave false in
private theorem same_readout_feeds_character_cochain_and_pulse_recovery
    (depth bound : Nat) (within : bound < budget depth)
    (word : Consumer.Formal depth) (i : Fin (bound+1))
    (target : SourceOperationLogic.Fibre
      (nextPulseEvaluation depth (livePulse depth bound within i))
      (SourceOperationLogic.q (nextPulseEvaluation depth (livePulse depth bound within i)) word)) :
    let pulse := livePulse depth bound within i
    let runtime := pulseRuntime depth pulse
    let readout := sourceReadout depth
    let reads := readout.1 pulse
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    let inventory := updateInventory (R := ℤ) (s := Unit.unit) reads.1 reads.2
    Character.stageRead (readMaterial depth) (environment depth) (mathTail depth) bound
        (Consumer.sourceField depth word) i = inventory word ∧
    SourceOperationScalarCochain.cochain (R := ℤ) (s := Unit.unit) reads.1 reads.2 =
      SourceOperationScalarCochain.cochain (R := ℤ) (s := Unit.unit)
        (oldEnvironment (readMaterial depth) (environment depth) stage)
        (incrementEnvironment (readMaterial depth) (environment depth) stage) ∧
    Fibre.recover (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth) runtime
      (SourceOperationLogic.FibreLift.liftingResidual
        (Fibre.actualMorphism (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth) runtime)
        word target) = inventory (target.val-word) := by
  let pulse := livePulse depth bound within i
  let runtime := pulseRuntime depth pulse
  let readout := sourceReadout depth
  let reads := readout.1 pulse
  let inventory : Consumer.Formal depth →ₗ[ℤ] Material depth × Material depth :=
    updateInventory (R := ℤ) (s := Unit.unit) reads.1 reads.2
  have first : Fibre.firstStage (R := ℤ) (s := Unit.unit)
      (readMaterial depth) (environment depth) runtime = inventory :=
    (pulse_inventory_actual depth pulse).symm
  have cochain := congrArg (fun pair : type_of% reads =>
    SourceOperationScalarCochain.cochain (R := ℤ) (s := Unit.unit) pair.1 pair.2) (source_readout_pulse depth pulse)
  have recovery := Fibre.recover_liftingResidual (R := ℤ) (s := Unit.unit)
    (readMaterial depth) (environment depth) runtime word target
  exact ⟨source_character_from_full depth bound within word i, cochain,
    recovery.trans (congrArg (fun map : Consumer.Formal depth →ₗ[ℤ] Material depth × Material depth =>
      map (target.val-word)) first)⟩

#eval IO.println "CP598_CONTROL + same_readout_feeds_character_cochain_and_pulse_recovery"

private def OriginalDisposition (depth : Nat) (terminal : Material depth) : Prop :=
  (∃ reached : ReachedAt (Registered.actor depth).rooted.rootSource.source,
    terminal = Finsupp.single
      (some (⟨(Registered.runtime depth).emittedOccurrence,.completed (.inl reached)⟩ : Registered.Point depth)) 1 ∧
    ∃ generated : PrimePairActualitySettlementAt (directRuntimeActuality depth),
      generatePrimePairActualityDisposition (directRuntimeActuality depth) = .settlement generated) ∨
  (∃ exhausted : ExhaustedAt (Registered.actor depth).rooted.rootSource.source,
    terminal = Finsupp.single
      (some (⟨(Registered.runtime depth).emittedOccurrence,.completed (.inr exhausted)⟩ : Registered.Point depth)) 1 ∧
    ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
      generatePrimePairActualityDisposition (directRuntimeActuality depth) = .obstruction generated)

set_option cleanup.letToHave false in
private theorem the_same_readout_supplies_terminal_material_and_original_receipt (depth : Nat) :
    let readout := sourceReadout depth
    readout.2 = storedFinal depth ∧ OriginalDisposition depth readout.2 ∧
      type_of% (Registered.receipt depth) := by
  refine ⟨source_readout_terminal depth,?_,Registered.receipt depth⟩
  rw [source_readout_terminal]
  exact stored_consumes_original_disposition depth

#eval IO.println "CP598_CONTROL + the_same_readout_supplies_terminal_material_and_original_receipt"

private def bindIndex (depth : Nat) : Fin (budget depth + 1) := ⟨0, Nat.succ_pos _⟩

private theorem exact_bind_cells_are_distinct (depth : Nat) :
    (fullTable depth).get (bindIndex depth).castSucc ≠
      (fullTable depth).get (bindIndex depth).succ := by
  intro same
  let bind := bindIndex depth
  have pair := (fullHistory depth).stored_timeline_adjacent (readMaterial depth) bind
  have old := (congrArg Prod.fst pair).trans (stored_seed_material depth)
  have new := (congrArg Prod.snd pair).trans (stored_actor_prefix depth 0 (Nat.zero_le _))
  have atUnbound := congrArg (fun value : Material depth => value none) ((old.symm.trans same).trans new)
  simp at atUnbound

#eval IO.println "CP598_CONTROL - exact_bind_cells_are_distinct"
#eval IO.println "CP598_GATE_PASS positive=4 negative=1"

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
