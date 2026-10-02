import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaDeclarations.Actual
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.ActualOrigin.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaActual
open MotherArenaNetwork
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def outputKey {base : M} {h : MotherArenaVocabulary.Check base}
    {c : (V base h).Current} : EvolutionAt (V base h) c → Nat × B
  | .nativeWrite w => (1, w.val)
  | .relationWrite w => (2, w.val)
  | .continuedTransport w => (3, w.val)
  | .borromeanRedirect w => (4, w.val)
  | .faithfulTerminal w => (5, w.val)

theorem outputKey_injective {base : M} {h : MotherArenaVocabulary.Check base}
    {c : (V base h).Current} : Function.Injective (outputKey (c := c)) := by
  intro a b same
  cases a <;> cases b <;> simp_all [outputKey] <;> exact Subtype.ext same

theorem outputKey_nonzero {base : M} {h : MotherArenaVocabulary.Check base}
    {c : (V base h).Current} (value : EvolutionAt (V base h) c) :
    (outputKey value).1 ≠ 0 := by
  cases value <;> simp only [outputKey, ne_eq, Nat.reduceEqDiff, not_false_eq_true]

theorem compileGraph_key (base events : M) (h : MotherArenaVocabulary.Check base)
    {c : (V base h).Current} (event : EventAt base events c) (value : EvolutionAt (V base h) c) :
    compileGraph base events h event value ↔
      r3 events (outputKey value).1 c.val event.val (outputKey value).2 := by
  cases value <;> rfl

abbrev Presentation {Original Generated : Vocabulary.{0}}
    (p : MotherArenaVocabulary.Presentation Original Generated)
    (original : ActualEventAlgebra Original) (generated : ActualEventAlgebra Generated) :=
  MotherActualOrigin.Presentation p original generated

namespace Encoding
variable {base : MotherArenaHigher.Material rank} {h : MotherArenaVocabulary.Check base} {Original : Vocabulary.{0}}
    (p : MotherArenaVocabulary.Presentation Original (V base h))
    (original : ActualEventAlgebra Original) (encode : (Sigma original.OccurrenceAt) ↪ MotherArenaHigher.Base rank)

def graph (tag : Nat) (code : B) : Prop :=
  let pair := (MotherArenaHigher.unpair rank) code
  let tail := (MotherArenaHigher.unpair rank) pair.2
  if tag = 0 then
    ∃ c e, (p.current c).val = pair.1 ∧ encode ⟨c, e⟩ = pair.2
  else
    ∃ c e, (p.current c).val = pair.1 ∧ encode ⟨c, e⟩ = tail.1 ∧
      outputKey (p.evolution c (original.compile e)) = (tag, tail.2)

def reader (code : B) (tag : Nat) : ℝ := if graph p original encode tag code then 0 else 1

theorem reader_bit {events : M} (hm : (MotherArenaHigher.read rank) events = reader p original encode)
    (tag : Nat) (code : B) : bit events tag code ↔ graph p original encode tag code := by
  by_cases seen : graph p original encode tag code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

def eventEquiv {events : M} (hm : (MotherArenaHigher.read rank) events = reader p original encode)
    (c : Original.Current) : original.OccurrenceAt c ≃ EventAt base events (p.current c) :=
  MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk c).trans encode)
    (fun b => r2 events 0 (p.current c).val b) (by
      intro b
      rw [r2, reader_bit p original encode hm]
      simp only [graph, (MotherArenaHigher.unpair_pair rank)]
      change (∃ c' e, (p.current c').val = (p.current c).val ∧ encode ⟨c', e⟩ = b) ↔
        ∃ e, encode ⟨c, e⟩ = b
      constructor
      · rintro ⟨c', e, hc, he⟩
        have same := p.current.injective (Subtype.ext hc)
        cases same
        exact ⟨e, he⟩
      · rintro ⟨e, he⟩
        exact ⟨c, e, rfl, he⟩)

theorem graph_at {events : M} (hm : (MotherArenaHigher.read rank) events = reader p original encode)
    (c : Original.Current) (event : original.OccurrenceAt c)
    (value : EvolutionAt (V base h) (p.current c)) :
    compileGraph base events h (eventEquiv p original encode hm c event) value ↔
      value = p.evolution c (original.compile event) := by
  rw [compileGraph_key, r3, reader_bit p original encode hm]
  simp only [graph, if_neg (outputKey_nonzero value), (MotherArenaHigher.unpair_pair rank)]
  change (∃ c' e, (p.current c').val = (p.current c).val ∧ encode ⟨c', e⟩ = encode ⟨c, event⟩ ∧
    outputKey (p.evolution c' (original.compile e)) = outputKey value) ↔ _
  constructor
  · rintro ⟨c', e, hc, he, output⟩
    have same := p.current.injective (Subtype.ext hc)
    cases same
    have same := ((Function.Embedding.sigmaMk c).trans encode).injective he
    cases same
    exact (outputKey_injective output).symm
  · intro same
    cases same
    exact ⟨c, event, rfl, rfl, rfl⟩

theorem checked {events : M} (hm : (MotherArenaHigher.read rank) events = reader p original encode) :
    Check base events h := by
  intro c event
  obtain ⟨c, rfl⟩ := p.current.surjective c
  obtain ⟨event, rfl⟩ := (eventEquiv p original encode hm c).surjective event
  exact ⟨_, (graph_at p original encode hm c event _).mpr rfl,
    fun value selected => (graph_at p original encode hm c event value).mp selected⟩

def presentation {events : M} (hm : (MotherArenaHigher.read rank) events = reader p original encode) :
    Presentation p original (actual base events h (checked p original encode hm)) where
  event := eventEquiv p original encode hm
  compile_commutes := fun c event =>
    compile_eq base events h (checked p original encode hm) _ _
      ((graph_at p original encode hm c event _).mpr rfl)

end Encoding

theorem vocabulary_check {base : M} {W : Vocabulary.{0}}
    (formed : MotherArenaVocabulary.formVocabulary base = some W) : MotherArenaVocabulary.Check base := by
  unfold MotherArenaVocabulary.formVocabulary at formed
  split at formed
  · assumption
  · cases formed

theorem every_embedded_actual (Original : Vocabulary.{0}) (original : ActualEventAlgebra Original)
    (vocabularyCode : MotherVocabularyOrigin.Total Original ↪ B)
    (eventCode : Sigma original.OccurrenceAt ↪ B) :
    ∃ m : M, ∃ W : Vocabulary.{0}, ∃ generated : ActualEventAlgebra W,
      ∃ p : MotherArenaVocabulary.Presentation Original W,
        formActual m = some ⟨W, generated⟩ ∧ Nonempty (Presentation p original generated) := by
  obtain ⟨base, W, formedV, ⟨p⟩⟩ := MotherArenaDeclarations.every_vocabulary_on_rank Original vocabularyCode
  have checkV := vocabulary_check formedV
  have same : W = V base checkV := Option.some.inj (formedV.symm.trans (vocabulary_formed base checkV))
  cases same
  obtain ⟨events, hm⟩ := (MotherArenaHigher.read_surjective rank) (Encoding.reader p original eventCode)
  exact ⟨(MotherArenaHigher.pack rank) (base, events), V base checkV,
    actual base events checkV (Encoding.checked p original eventCode hm), p,
    formed base events checkV (Encoding.checked p original eventCode hm),
    ⟨Encoding.presentation p original eventCode hm⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaActual
