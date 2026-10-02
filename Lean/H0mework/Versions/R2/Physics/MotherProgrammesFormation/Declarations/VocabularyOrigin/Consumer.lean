import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.VocabularyOrigin.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.VocabularyOrigin.Evolution

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherVocabularyOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def Field (V : Vocabulary.{0}) : Fin 10 → Type
  | 0 => V.Current
  | 1 => V.Anchor
  | 2 => V.Incidence
  | 3 => V.Lineage
  | 4 => Σ c, V.NativeWriteAt c
  | 5 => Σ c, V.RelationWriteAt c
  | 6 => Σ c, V.ContinuedTransportAt c
  | 7 => Σ c, V.BorromeanRedirectAt c
  | 8 => Σ c, V.FaithfulTerminalAt c
  | _ => V.cofinal.Event

abbrev Total (V : Vocabulary.{0}) := Sigma (Field V)

def Encoding.ofTotal {V : Vocabulary.{0}} (encode : Total V ↪ B) : Encoding V where
  current := (Function.Embedding.sigmaMk 0).trans encode
  anchor := (Function.Embedding.sigmaMk 1).trans encode
  incidence := (Function.Embedding.sigmaMk 2).trans encode
  lineage := (Function.Embedding.sigmaMk 3).trans encode
  native := (Function.Embedding.sigmaMk 4).trans encode
  relation := (Function.Embedding.sigmaMk 5).trans encode
  continued := (Function.Embedding.sigmaMk 6).trans encode
  redirect := (Function.Embedding.sigmaMk 7).trans encode
  terminal := (Function.Embedding.sigmaMk 8).trans encode
  cofinal := (Function.Embedding.sigmaMk 9).trans encode

/-- The original declaration enters coverage through its entire dependent
total; the factory itself receives only the formed mother material. -/
theorem every_jointly_embedded_vocabulary (V : Vocabulary.{0}) (encode : Total V ↪ B) :
    ∃ m : M, ∃ W : Vocabulary.{0},
      formVocabulary m = some W ∧ Nonempty (Presentation V W) :=
  every_embedded_vocabulary V (.ofTotal encode)

/-- One material and complete declaration presentation precede every original
event algebra. The original compiler is a downstream consumer: all events,
all branch payloads and the exact next current survive the exchange. -/
theorem formed_vocabulary_consumes_full_original_actual
    (V : Vocabulary.{0}) (encode : Total V ↪ B) :
    ∃ m : M, ∃ W : Vocabulary.{0}, ∃ p : Presentation V W,
      formVocabulary m = some W ∧
      ∀ (original : ActualEventAlgebra V) (c : V.Current)
        (event : original.OccurrenceAt c),
        (p.actual original).compile (p.actualEvent original c event) =
            p.evolution c (original.compile event) ∧
        (p.evolution c).symm
            ((p.actual original).compile (p.actualEvent original c event)) =
          original.compile event ∧
        ((p.actual original).compile (p.actualEvent original c event)).kind =
          (original.compile event).kind ∧
        ((p.actual original).compile (p.actualEvent original c event)).nextCurrent? =
          Option.map p.current (original.compile event).nextCurrent? := by
  obtain ⟨m, W, formed, ⟨p⟩⟩ := every_jointly_embedded_vocabulary V encode
  refine ⟨m, W, p, formed, ?_⟩
  intro original c event
  refine ⟨p.actual_compile original event, ?_, ?_, ?_⟩
  · rw [p.actual_compile, Equiv.symm_apply_apply]
  · rw [p.actual_compile, p.evolution_kind]
  · rw [p.actual_compile]
    exact (p.evolution_next (original.compile event)).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherVocabularyOrigin
