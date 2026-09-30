import H0mework.Physics.MotherProgrammesFormation.Declarations.VocabularyOrigin.Presentation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherVocabularyOrigin
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def Presentation.mapEvolution {V W : Vocabulary.{0}} (p : Presentation V W) {c : V.Current} :
    EvolutionAt V c → EvolutionAt W (p.current c)
  | .nativeWrite w => .nativeWrite (p.native c w)
  | .relationWrite w => .relationWrite (p.relation c w)
  | .continuedTransport w => .continuedTransport (p.continued c w)
  | .borromeanRedirect w => .borromeanRedirect (p.redirect c w)
  | .faithfulTerminal w => .faithfulTerminal (p.terminal c w)

def Presentation.restoreEvolution {V W : Vocabulary.{0}} (p : Presentation V W) {c : V.Current} :
    EvolutionAt W (p.current c) → EvolutionAt V c
  | .nativeWrite w => .nativeWrite ((p.native c).symm w)
  | .relationWrite w => .relationWrite ((p.relation c).symm w)
  | .continuedTransport w => .continuedTransport ((p.continued c).symm w)
  | .borromeanRedirect w => .borromeanRedirect ((p.redirect c).symm w)
  | .faithfulTerminal w => .faithfulTerminal ((p.terminal c).symm w)

def Presentation.evolution {V W : Vocabulary.{0}} (p : Presentation V W) (c : V.Current) :
    EvolutionAt V c ≃ EvolutionAt W (p.current c) where
  toFun := p.mapEvolution
  invFun := p.restoreEvolution
  left_inv := by intro value; cases value <;> simp only [mapEvolution, restoreEvolution, Equiv.symm_apply_apply]
  right_inv := by intro value; cases value <;> simp only [mapEvolution, restoreEvolution, Equiv.apply_symm_apply]

theorem Presentation.evolution_kind {V W : Vocabulary.{0}} (p : Presentation V W)
    {c : V.Current} (value : EvolutionAt V c) : (p.evolution c value).kind = value.kind := by
  cases value <;> rfl

theorem Presentation.evolution_next {V W : Vocabulary.{0}} (p : Presentation V W)
    {c : V.Current} (value : EvolutionAt V c) :
    Option.map p.current value.nextCurrent? = (p.evolution c value).nextCurrent? := by
  cases value with
  | nativeWrite w => exact congrArg some (p.native_eq c w).symm
  | relationWrite w => exact congrArg some (p.relation_eq c w).symm
  | continuedTransport w => exact congrArg some (p.continued_eq c w).symm
  | borromeanRedirect w => exact congrArg some (p.redirect_eq c w).symm
  | faithfulTerminal => rfl

/-- The original event family and its full compile function are one dependent
section; current reindexing transports the entire section. -/
structure EventProgram (V : Vocabulary.{0}) (c : V.Current) : Type 1 where
  Event : Type
  compile : Event → EvolutionAt V c

def Presentation.programImage {V W : Vocabulary.{0}} (p : Presentation V W)
    (original : ActualEventAlgebra V) (c : V.Current) : EventProgram W (p.current c) where
  Event := original.OccurrenceAt c
  compile := fun event => p.evolution c (original.compile event)

def Presentation.program {V W : Vocabulary.{0}} (p : Presentation V W)
    (original : ActualEventAlgebra V) : (c : W.Current) → EventProgram W c :=
  Equiv.piCongrLeft _ p.current (p.programImage original)

theorem Presentation.program_at {V W : Vocabulary.{0}} (p : Presentation V W)
    (original : ActualEventAlgebra V) (c : V.Current) :
    p.program original (p.current c) = p.programImage original c :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

def Presentation.actual {V W : Vocabulary.{0}} (p : Presentation V W)
    (original : ActualEventAlgebra V) : ActualEventAlgebra W where
  OccurrenceAt := fun c => (p.program original c).Event
  compile := fun {c} event => (p.program original c).compile event

def Presentation.actualEvent {V W : Vocabulary.{0}} (p : Presentation V W)
    (original : ActualEventAlgebra V) (c : V.Current) :
    original.OccurrenceAt c ≃ (p.actual original).OccurrenceAt (p.current c) :=
  Equiv.cast (congrArg EventProgram.Event (p.program_at original c)).symm

theorem Presentation.actual_compile {V W : Vocabulary.{0}} (p : Presentation V W)
    (original : ActualEventAlgebra V) {c : V.Current} (event : original.OccurrenceAt c) :
    (p.actual original).compile (p.actualEvent original c event) =
      p.evolution c (original.compile event) := by
  have compile_equal {c : W.Current} {left right : EventProgram W c} (same : left = right) (e : right.Event) :
      left.compile (Eq.mp (congrArg EventProgram.Event same.symm) e) = right.compile e := by
    cases same
    rfl
  exact compile_equal (p.program_at original c) event

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherVocabularyOrigin
