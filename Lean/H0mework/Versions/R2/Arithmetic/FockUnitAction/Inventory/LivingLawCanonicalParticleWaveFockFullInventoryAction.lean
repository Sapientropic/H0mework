import H0mework.Versions.R2.Arithmetic.FockDynamics.AtomicState

/-!
# Actual terminal selection from the complete current inventory

All prime-factor repair/emission siblings belong to the existing source
inventory. Select a terminal target from it when present; otherwise consume
the existing unordered physical selector, including its emission when repair
is only a label exchange. No terminal is an input.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockFullInventoryAction

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open CanonicalUnitArithmeticFullFactorRepairReachabilityProducer
open ParticleWaveFockAtomicProcess
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

abbrev InventoryTerminalActionAt {index : Nat}
    (source : EffectiveSplitAt index) :=
  Sigma fun channel : FactorDecayChannelAt source =>
    PrimePairTerminalAt channel.target

noncomputable def channelTerminalRead {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    Option (PrimePairTerminalAt channel.target) :=
  match (fullFactorDecayLaw index).classify channel.target with
  | .inl terminal => some terminal
  | .inr _ => none

noncomputable def firstTerminalAction {index : Nat}
    {source : EffectiveSplitAt index} :
    List (FactorDecayChannelAt source) →
      Option (InventoryTerminalActionAt source)
  | [] => none
  | channel :: rest =>
      match channelTerminalRead channel with
      | some terminal => some ⟨channel, terminal⟩
      | none => firstTerminalAction rest

noncomputable def completeInventoryTerminalAction {index : Nat}
    (source : EffectiveSplitAt index) :
    Option (InventoryTerminalActionAt source) :=
  firstTerminalAction (completeApplicableInventory source).toList

theorem fullFactorDecayClassify_isTerminal_of_terminal {index : Nat}
    {state : EffectiveSplitAt index}
    (terminal : PrimePairTerminalAt state) :
    ∃ generated : PrimePairTerminalAt state,
      (fullFactorDecayLaw index).classify state = .inl generated := by
  refine ⟨terminal, ?_⟩
  simp [fullFactorDecayLaw, fullFactorDecayClassify, fullFactorRepairLaw,
    terminal.leftPrime, terminal.rightPrime]

theorem firstTerminalAction_some_of_mem {index : Nat}
    {source : EffectiveSplitAt index}
    (channels : List (FactorDecayChannelAt source))
    (channel : FactorDecayChannelAt source)
    (channelMem : channel ∈ channels)
    (terminal : PrimePairTerminalAt channel.target) :
    ∃ selected : InventoryTerminalActionAt source,
      firstTerminalAction channels = some selected := by
  induction channels with
  | nil => simp at channelMem
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at channelMem
      unfold firstTerminalAction
      unfold channelTerminalRead
      generalize classifierEq :
        (fullFactorDecayLaw index).classify head.target = outcome
      cases outcome with
      | inl generated => exact ⟨⟨head, generated⟩, rfl⟩
      | inr step =>
          rcases channelMem with headEq | tailMem
          · subst head
            obtain ⟨generated, terminalEq⟩ :=
              fullFactorDecayClassify_isTerminal_of_terminal terminal
            rw [classifierEq] at terminalEq
            contradiction
          · exact inductionHypothesis tailMem

theorem completeInventoryTerminalAction_some_of_channel {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source)
    (terminal : PrimePairTerminalAt channel.target) :
    ∃ selected : InventoryTerminalActionAt source,
      completeInventoryTerminalAction source = some selected := by
  apply firstTerminalAction_some_of_mem
    (completeApplicableInventory source).toList channel
  · exact Finset.mem_toList.mpr (mem_completeApplicableInventory channel)
  · exact terminal

abbrev TerminalFirstActorOutcomeAt {index : Nat}
    (source : EffectiveSplitAt index) :=
  Sigma fun target : EffectiveSplitAt index =>
    GeneratedPathAt (fullFactorDecayLaw index) source target ×
      (PrimePairTerminalAt target ⊕ Unit)

/-- The complete inventory keeps terminal priority.  A nonterminal update
uses the already-generated physical action, not the repair-only spine. -/
noncomputable def terminalFirstActor {index : Nat}
    (source : EffectiveSplitAt index) :
    TerminalFirstActorOutcomeAt source :=
  match fullPhysicalFactorDecayClassify source with
  | .inl selected => ⟨source, .nil, .inl selected.terminal⟩
  | .inr fallback =>
      match completeInventoryTerminalAction source with
      | some selected =>
          ⟨selected.1.target,
            (GeneratedPathAt.nil : GeneratedPathAt
              (fullFactorDecayLaw index) source source).snoc selected.1,
            .inl selected.2⟩
      | none =>
          ⟨fallback.channel.target,
            (GeneratedPathAt.nil : GeneratedPathAt
              (fullFactorDecayLaw index) source source).snoc fallback.channel,
            .inr ()⟩

theorem terminalFirstActor_hasTerminal_of_channel {index : Nat}
    (source : EffectiveSplitAt index)
    (channel : FactorDecayChannelAt source)
    (terminal : PrimePairTerminalAt channel.target) :
    ∃ target : EffectiveSplitAt index,
      ∃ path : GeneratedPathAt (fullFactorDecayLaw index) source target,
        ∃ generated : PrimePairTerminalAt target,
          terminalFirstActor source = ⟨target, path, .inl generated⟩ := by
  unfold terminalFirstActor
  generalize classifierEq :
    fullPhysicalFactorDecayClassify source = outcome
  cases outcome with
  | inl selected => exact ⟨source, .nil, selected.terminal, rfl⟩
  | inr fallback =>
      obtain ⟨selected, selectedEq⟩ :=
        completeInventoryTerminalAction_some_of_channel channel terminal
      rw [selectedEq]
      exact ⟨selected.1.target, _, selected.2, rfl⟩

theorem terminalFirstActor_terminal_or_physicalStep {index : Nat}
    (source : EffectiveSplitAt index)
    (fallback : PhysicalProgressChannelAt source)
    (classifierEq :
      fullPhysicalFactorDecayClassify source = .inr fallback) :
    (∃ target : EffectiveSplitAt index,
      ∃ path : GeneratedPathAt (fullFactorDecayLaw index) source target,
        ∃ generated : PrimePairTerminalAt target,
          terminalFirstActor source = ⟨target, path, .inl generated⟩) ∨
      terminalFirstActor source =
        ⟨fallback.channel.target,
          (GeneratedPathAt.nil : GeneratedPathAt
            (fullFactorDecayLaw index) source source).snoc fallback.channel,
          .inr ()⟩ := by
  unfold terminalFirstActor
  simp only [classifierEq]
  generalize selectedEq :
    completeInventoryTerminalAction source = selected
  cases selected with
  | none => exact .inr rfl
  | some terminalAction =>
      exact .inl ⟨terminalAction.1.target, _, terminalAction.2, rfl⟩

theorem terminalFirstActor_terminal_or_classifierStep {index : Nat}
    (source : EffectiveSplitAt index)
    (fallback : FactorDecayChannelAt source)
    (classifierEq :
      (fullFactorDecayLaw index).classify source = .inr fallback)
    (physicalProgress : fallback.IsPhysicalProgress) :
    (∃ target : EffectiveSplitAt index,
      ∃ path : GeneratedPathAt (fullFactorDecayLaw index) source target,
        ∃ generated : PrimePairTerminalAt target,
          terminalFirstActor source = ⟨target, path, .inl generated⟩) ∨
      terminalFirstActor source =
        ⟨fallback.target,
          (GeneratedPathAt.nil : GeneratedPathAt
            (fullFactorDecayLaw index) source source).snoc fallback,
          .inr ()⟩ := by
  generalize physicalEq : fullPhysicalFactorDecayClassify source = outcome
  cases outcome with
  | inl selected =>
      have impossible := selected.classifier_eq.symm.trans classifierEq
      contradiction
  | inr selected =>
      obtain ⟨alternative, fallbackEq⟩ :=
        generatedRepairAlternativeOfClassifiedStep source fallback classifierEq
      have channelEq : selected.channel = fallback := by
        rw [fallbackEq]
        exact selected.channel_eq_preferredRepair alternative
          (classifierEq.trans (congrArg Sum.inr fallbackEq))
          (fallbackEq ▸ physicalProgress)
      rcases terminalFirstActor_terminal_or_physicalStep source selected
          physicalEq with terminal | step
      · exact .inl terminal
      · exact .inr (step.trans (congrArg
          (fun channel : FactorDecayChannelAt source =>
            (⟨channel.target,
              (GeneratedPathAt.nil : GeneratedPathAt
                (fullFactorDecayLaw index) source source).snoc channel,
              .inr ()⟩ : TerminalFirstActorOutcomeAt source)) channelEq))

/-- An unresolved actor head changes the unordered particle state.  In
particular, swapping the ordered labels cannot be its continuation. -/
theorem terminalFirstActor_continuation_isPhysicalProgress {index : Nat}
    (source : EffectiveSplitAt index)
    (unsettled : (terminalFirstActor source).2.2 = .inr ()) :
    unorderedSplitKey (terminalFirstActor source).1 ≠
      unorderedSplitKey source := by
  unfold terminalFirstActor at unsettled ⊢
  generalize physicalEq : fullPhysicalFactorDecayClassify source = outcome
    at unsettled ⊢
  cases outcome with
  | inl selected => contradiction
  | inr selected =>
      generalize inventoryEq : completeInventoryTerminalAction source = action
        at unsettled ⊢
      cases action with
      | none => exact selected.physicalProgress
      | some terminalAction => contradiction


end
end ParticleWaveFockFullInventoryAction
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
