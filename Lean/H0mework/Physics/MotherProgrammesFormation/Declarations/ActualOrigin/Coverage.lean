import H0mework.Physics.MotherProgrammesFormation.Declarations.ActualOrigin.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActualOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

def outputKey {base : M} {h : MotherVocabularyOrigin.Check base}
    {c : (V base h).Current} : EvolutionAt (V base h) c → Nat × B
  | .nativeWrite w => (1, w.val)
  | .relationWrite w => (2, w.val)
  | .continuedTransport w => (3, w.val)
  | .borromeanRedirect w => (4, w.val)
  | .faithfulTerminal w => (5, w.val)

theorem outputKey_injective {base : M} {h : MotherVocabularyOrigin.Check base}
    {c : (V base h).Current} : Function.Injective (outputKey (c := c)) := by
  intro a b same
  cases a <;> cases b <;> simp_all [outputKey] <;> exact Subtype.ext same

theorem outputKey_nonzero {base : M} {h : MotherVocabularyOrigin.Check base}
    {c : (V base h).Current} (value : EvolutionAt (V base h) c) :
    (outputKey value).1 ≠ 0 := by
  cases value <;> simp only [outputKey, ne_eq, Nat.reduceEqDiff, not_false_eq_true]

theorem compileGraph_key (base events : M) (h : MotherVocabularyOrigin.Check base)
    {c : (V base h).Current} (event : EventAt base events c) (value : EvolutionAt (V base h) c) :
    compileGraph base events h event value ↔
      r3 events (outputKey value).1 c.val event.val (outputKey value).2 := by
  cases value <;> rfl

structure Presentation {Original Generated : Vocabulary.{0}}
    (p : MotherVocabularyOrigin.Presentation Original Generated)
    (original : ActualEventAlgebra Original) (generated : ActualEventAlgebra Generated) where
  event : ∀ c, original.OccurrenceAt c ≃ generated.OccurrenceAt (p.current c)
  compile_commutes : ∀ c e, generated.compile (event c e) = p.evolution c (original.compile e)

namespace Encoding
variable {base : M} {h : MotherVocabularyOrigin.Check base} {Original : Vocabulary.{0}}
    (p : MotherVocabularyOrigin.Presentation Original (V base h))
    (original : ActualEventAlgebra Original) (encode : (Sigma original.OccurrenceAt) ↪ B)

def graph (tag : Nat) (code : B) : Prop :=
  let pair := MotherHigherLawFamily.unpair code
  let tail := MotherHigherLawFamily.unpair pair.2
  if tag = 0 then
    ∃ c e, (p.current c).val = pair.1 ∧ encode ⟨c, e⟩ = pair.2
  else
    ∃ c e, (p.current c).val = pair.1 ∧ encode ⟨c, e⟩ = tail.1 ∧
      outputKey (p.evolution c (original.compile e)) = (tag, tail.2)

def reader (code : B) (tag : Nat) : ℝ := if graph p original encode tag code then 0 else 1

theorem reader_bit {events : M} (hm : MotherHigherLawFormation.read events = reader p original encode)
    (tag : Nat) (code : B) : bit events tag code ↔ graph p original encode tag code := by
  by_cases seen : graph p original encode tag code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

def eventEquiv {events : M} (hm : MotherHigherLawFormation.read events = reader p original encode)
    (c : Original.Current) : original.OccurrenceAt c ≃ EventAt base events (p.current c) :=
  MotherNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk c).trans encode)
    (fun b => r2 events 0 (p.current c).val b) (by
      intro b
      rw [r2, reader_bit p original encode hm]
      simp only [graph, MotherHigherLawFamily.unpair_pair]
      change (∃ c' e, (p.current c').val = (p.current c).val ∧ encode ⟨c', e⟩ = b) ↔
        ∃ e, encode ⟨c, e⟩ = b
      constructor
      · rintro ⟨c', e, hc, he⟩
        have same := p.current.injective (Subtype.ext hc)
        cases same
        exact ⟨e, he⟩
      · rintro ⟨e, he⟩
        exact ⟨c, e, rfl, he⟩)

theorem graph_at {events : M} (hm : MotherHigherLawFormation.read events = reader p original encode)
    (c : Original.Current) (event : original.OccurrenceAt c)
    (value : EvolutionAt (V base h) (p.current c)) :
    compileGraph base events h (eventEquiv p original encode hm c event) value ↔
      value = p.evolution c (original.compile event) := by
  rw [compileGraph_key, r3, reader_bit p original encode hm]
  simp only [graph, if_neg (outputKey_nonzero value), MotherHigherLawFamily.unpair_pair]
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

theorem checked {events : M} (hm : MotherHigherLawFormation.read events = reader p original encode) :
    Check base events h := by
  intro c event
  obtain ⟨c, rfl⟩ := p.current.surjective c
  obtain ⟨event, rfl⟩ := (eventEquiv p original encode hm c).surjective event
  exact ⟨_, (graph_at p original encode hm c event _).mpr rfl,
    fun value selected => (graph_at p original encode hm c event value).mp selected⟩

def presentation {events : M} (hm : MotherHigherLawFormation.read events = reader p original encode) :
    Presentation p original (actual base events h (checked p original encode hm)) where
  event := eventEquiv p original encode hm
  compile_commutes := fun c event =>
    compile_eq base events h (checked p original encode hm) _ _
      ((graph_at p original encode hm c event _).mpr rfl)

end Encoding

theorem vocabulary_check {base : M} {W : Vocabulary.{0}}
    (formed : MotherVocabularyOrigin.formVocabulary base = some W) : MotherVocabularyOrigin.Check base := by
  unfold MotherVocabularyOrigin.formVocabulary at formed
  split at formed
  · assumption
  · cases formed

theorem every_embedded_actual (Original : Vocabulary.{0}) (original : ActualEventAlgebra Original)
    (vocabularyCode : MotherVocabularyOrigin.Total Original ↪ B)
    (eventCode : Sigma original.OccurrenceAt ↪ B) :
    ∃ m : M, ∃ W : Vocabulary.{0}, ∃ generated : ActualEventAlgebra W,
      ∃ p : MotherVocabularyOrigin.Presentation Original W,
        formActual m = some ⟨W, generated⟩ ∧ Nonempty (Presentation p original generated) := by
  obtain ⟨base, W, formedV, ⟨p⟩⟩ := MotherVocabularyOrigin.every_jointly_embedded_vocabulary Original vocabularyCode
  have checkV := vocabulary_check formedV
  have same : W = V base checkV := Option.some.inj (formedV.symm.trans (vocabulary_formed base checkV))
  cases same
  obtain ⟨events, hm⟩ := MotherHigherLawFormation.read_surjective (Encoding.reader p original eventCode)
  exact ⟨MotherHigherLawValue.pack (base, events), V base checkV,
    actual base events checkV (Encoding.checked p original eventCode hm), p,
    formed base events checkV (Encoding.checked p original eventCode hm),
    ⟨Encoding.presentation p original eventCode hm⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActualOrigin
