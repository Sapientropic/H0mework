import H0mework.Versions.Rb81a4438.Realization.JointEffect.PassiveController
import H0mework.Foundation.Runtime.EffectDynamics

/-!
# Why a passive dependent face is not a recursive active effect

The legacy recursive-effect next requires an actual effect change, an
operational-state change, or a strict budget debit.  A static natural
dependent face has none of these.  It can use the legacy interface only by
producing an obstruction already present in the fixed network vocabulary;
that is impossible uniformly because the vocabulary may be empty.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointLegacyEffectNoGo

open RootLawDependentJointTransition

universe u

private theorem terminal_and_successor_false
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source.source occurrence}
    {entry : OpenResponsibilityAt N
      (source.source.toRootSource.account.supportOf occurrence)}
    (successor : SourceNativeEffectGeneratedSuccessorAt occurrence generated)
    (terminal : SourceNativeEffectTerminalAt generated entry) : False := by
  cases generated with
  | nativeWrite => exact PEmpty.elim terminal
  | relationWrite => exact PEmpty.elim terminal
  | continuedTransport => exact PEmpty.elim terminal
  | borromeanRedirect => exact PEmpty.elim terminal
  | faithfulTerminal => exact PEmpty.elim successor

theorem obstruction_nonempty_of_nonterminal_no_progress
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {eventVocabulary : SourceNativeEffectEventVocabulary source}
    {D : SourceNativeEffectDynamicalVocabulary eventVocabulary}
    {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {current : V.Current}
    {occurrence : SourceNativeEffectOccurrenceAt eventVocabulary current}
    {active : D.ActiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt source.source occurrence.lower}
    (successor : SourceNativeEffectGeneratedSuccessorAt
      occurrence.lower generated)
    (noProgress : ∀
        (effectSuccessor : SourceNativeEffectGeneratedSuccessorAt
          occurrence.lower generated)
        (targetActive : D.ActiveAt
          (eventVocabulary.emit effectSuccessor.targetOccurrence)),
      IsEmpty (SourceNativeRecursiveEffectProgressAt D occurrence active
        (eventVocabulary.emit effectSuccessor.targetOccurrence) targetActive))
    (disposition : SourceNativeEffectDynamicalDispositionAt
      D calculus occurrence active generated) :
    Nonempty (N.ObstructionAt
      (source.source.toRootSource.account.supportOf occurrence.lower)) := by
  cases disposition with
  | settled terminal =>
      exact False.elim (terminal_and_successor_false successor terminal)
  | next row effectSuccessor targetActive target_classify_eq ledgerTransport
      effect_commutes operational_commutes progress =>
      exact False.elim ((noProgress effectSuccessor targetActive).false progress)
  | cut row effectSuccessor obstruction demandEntry_eq disposition_commutes =>
      exact ⟨obstruction⟩

theorem no_effect_disposition_of_empty_obstruction_and_no_progress
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {eventVocabulary : SourceNativeEffectEventVocabulary source}
    {D : SourceNativeEffectDynamicalVocabulary eventVocabulary}
    {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {current : V.Current}
    {occurrence : SourceNativeEffectOccurrenceAt eventVocabulary current}
    {active : D.ActiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt source.source occurrence.lower}
    (successor : SourceNativeEffectGeneratedSuccessorAt
      occurrence.lower generated)
    (noProgress : ∀
        (effectSuccessor : SourceNativeEffectGeneratedSuccessorAt
          occurrence.lower generated)
        (targetActive : D.ActiveAt
          (eventVocabulary.emit effectSuccessor.targetOccurrence)),
      IsEmpty (SourceNativeRecursiveEffectProgressAt D occurrence active
        (eventVocabulary.emit effectSuccessor.targetOccurrence) targetActive))
    [IsEmpty (N.ObstructionAt
      (source.source.toRootSource.account.supportOf occurrence.lower))] :
    IsEmpty (SourceNativeEffectDynamicalDispositionAt
      D calculus occurrence active generated) :=
  ⟨fun disposition => by
    obtain ⟨obstruction⟩ :=
      obstruction_nonempty_of_nonterminal_no_progress
        successor noProgress disposition
    exact isEmptyElim obstruction⟩

/-- No residual can be turned into every possible obstruction language. -/
theorem no_free_obstruction_reifier
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {sourceEvolution targetEvolution : H →ₗᵢ[ℂ] H}
    (residual : EvolutionResidualAt sourceEvolution targetEvolution) :
    IsEmpty (∀ Obstruction : Type u,
      EvolutionResidualAt sourceEvolution targetEvolution → Obstruction) := by
  constructor
  intro reify
  exact Fin.elim0 (reify (ULift.{u, 0} (Fin 0)) residual).down

end RootLawDependentJointLegacyEffectNoGo
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
