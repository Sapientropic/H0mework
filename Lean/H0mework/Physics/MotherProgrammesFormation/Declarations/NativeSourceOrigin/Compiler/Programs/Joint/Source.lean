import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Joint.Equivalences

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open MotherNetworkOrigin (Program SelectedProgram)
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : Transitions original} {formed : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p old) formed)
    (rows : LedgerWriteRowSourceAt original old.exactTransitionAt)

def rowImage (context : WriteContext original) : Program (RowOutput formed (writeContextEquiv p context)) where
  Event := WriteEvents rows context
  compile := fun event => rowOutputEquiv p q context (rows.compileEvolution event, rows.compileExact event)

def remainderImage (context : RemainderContext original) : SelectedProgram (RemainderOutput formed (remainderContextEquiv p context)) where
  Event := RemainderEvents rows context
  emit := rows.transportedRemainderSource.emit? context.1.2 context.2
  compile := fun event => remainderOutputEquiv p q context
    ⟨rows.transportedRemainderSource.compileEvolution event, rows.transportedRemainderSource.compileExact event⟩

def rowProgram : (context : WriteContext generated) → Program (RowOutput formed context) :=
  Equiv.piCongrLeft _ (writeContextEquiv p) (rowImage p q rows)

def remainderProgram : (context : RemainderContext generated) → SelectedProgram (RemainderOutput formed context) :=
  Equiv.piCongrLeft _ (remainderContextEquiv p) (remainderImage p q rows)

theorem rowProgram_at (context : WriteContext original) :
    rowProgram p q rows (writeContextEquiv p context) = rowImage p q rows context :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem remainderProgram_at (context : RemainderContext original) :
    remainderProgram p q rows (remainderContextEquiv p context) = remainderImage p q rows context :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

/-- The complete original programme is reindexed as whole source sections.
Its event types and selectors remain part of those sections. -/
def sourceWrite : LedgerWriteRowSourceAt generated formed.exactTransitionAt where
  IncidenceOccurrenceAt := fun {current} event {target} a b => (rowProgram p q rows ⟨current, event, target, a, b⟩).Event
  compileEvolution := fun {current} {event} {target} {a} {b} value =>
    ((rowProgram p q rows ⟨current, event, target, a, b⟩).compile value).1
  compileExact := fun {current} {event} {target} {a} {b} value =>
    ((rowProgram p q rows ⟨current, event, target, a, b⟩).compile value).2
  transportedRemainderSource := {
    OccurrenceAt := fun {current} event target => (remainderProgram p q rows (⟨current, event⟩, target)).Event
    emit? := fun {current} event target => (remainderProgram p q rows (⟨current, event⟩, target)).emit
    compileEvolution := fun {current} {event} {target} value =>
      ((remainderProgram p q rows (⟨current, event⟩, target)).compile value).1
    compileExact := fun {current} {event} {target} value =>
      ((remainderProgram p q rows (⟨current, event⟩, target)).compile value).2 }

def rowEventEquiv (context : WriteContext original) :
    WriteEvents rows context ≃ WriteEvents (sourceWrite p q rows) (writeContextEquiv p context) :=
  Equiv.cast (congrArg Program.Event (rowProgram_at p q rows context)).symm

def remainderEventEquiv (context : RemainderContext original) :
    RemainderEvents rows context ≃ RemainderEvents (sourceWrite p q rows) (remainderContextEquiv p context) :=
  Equiv.cast (congrArg (fun programme : SelectedProgram (RemainderOutput formed (remainderContextEquiv p context)) => programme.Event)
    (remainderProgram_at p q rows context)).symm

theorem row_compile (context : WriteContext original) (event : WriteEvents rows context) :
    ((sourceWrite p q rows).compileEvolution (rowEventEquiv p q rows context event),
      (sourceWrite p q rows).compileExact (rowEventEquiv p q rows context event)) =
        rowOutputEquiv p q context (rows.compileEvolution event, rows.compileExact event) :=
  Program.compile_input (rowProgram_at p q rows context) event

theorem remainder_compile (context : RemainderContext original) (event : RemainderEvents rows context) :
    (⟨(sourceWrite p q rows).transportedRemainderSource.compileEvolution (remainderEventEquiv p q rows context event),
      (sourceWrite p q rows).transportedRemainderSource.compileExact (remainderEventEquiv p q rows context event)⟩ :
        RemainderOutput formed (remainderContextEquiv p context)) =
      remainderOutputEquiv p q context
        ⟨rows.transportedRemainderSource.compileEvolution event, rows.transportedRemainderSource.compileExact event⟩ :=
  SelectedProgram.compile_input (remainderProgram_at p q rows context) event

theorem remainder_emit (context : RemainderContext original) :
    Option.map (remainderEventEquiv p q rows context) (rows.transportedRemainderSource.emit? context.1.2 context.2) =
      (sourceWrite p q rows).transportedRemainderSource.emit? (remainderContextEquiv p context).1.2 (remainderContextEquiv p context).2 :=
  SelectedProgram.emit_input (remainderProgram_at p q rows context)

def totalEquiv : WriteTotal rows ≃ WriteTotal (sourceWrite p q rows) :=
  Equiv.sumCongr (Equiv.sigmaCongr (writeContextEquiv p) (rowEventEquiv p q rows))
    (Equiv.sigmaCongr (remainderContextEquiv p) (remainderEventEquiv p q rows))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
