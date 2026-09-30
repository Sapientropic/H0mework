import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {old generated : Transitions source} (p : TransitionPresentation old generated)

def certificationEquiv (point : Point source) (target : N.Support)
    (whole : LedgerWriteEvolutionAt N ⟨point.2.1⟩ ⟨target⟩) :
    ExactLedgerWriteCertificationAt N ⟨point.2.1⟩ ⟨target⟩ (old.exactTransitionAt point.2) whole ≃
      ExactLedgerWriteCertificationAt N ⟨point.2.1⟩ ⟨target⟩ (generated.exactTransitionAt point.2) whole where
  toFun := fun cert => {
    destination := fun a => p.exact ⟨point.1, point.2, target, a, (whole.destination a).1⟩ (cert.destination a)
    origin := fun b => p.exact ⟨point.1, point.2, target, (whole.origin b).1, b⟩ (cert.origin b) }
  invFun := fun cert => {
    destination := fun a => (p.exact ⟨point.1, point.2, target, a, (whole.destination a).1⟩).symm (cert.destination a)
    origin := fun b => (p.exact ⟨point.1, point.2, target, (whole.origin b).1, b⟩).symm (cert.origin b) }
  left_inv := by
    intro cert
    cases cert
    dsimp only
    congr 1 <;> funext entry <;> exact Equiv.symm_apply_apply _ _
  right_inv := by
    intro cert
    cases cert
    dsimp only
    congr 1 <;> funext entry <;> exact Equiv.apply_symm_apply _ _

/-- The entire existing source program is transported, including its
unselected remainder family and both complete certification sections. -/
def writeSource (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) :
    LedgerWriteRowSourceAt source generated.exactTransitionAt where
  IncidenceOccurrenceAt := rows.IncidenceOccurrenceAt
  compileEvolution := rows.compileEvolution
  compileExact := fun {current} {event} {target} {a} {b} value =>
    p.exact ⟨current, event, target, a, b⟩ (rows.compileExact value)
  transportedRemainderSource := {
    OccurrenceAt := rows.transportedRemainderSource.OccurrenceAt
    emit? := rows.transportedRemainderSource.emit?
    compileEvolution := rows.transportedRemainderSource.compileEvolution
    compileExact := fun {current} {event} {target} value =>
      certificationEquiv p ⟨current, event⟩ target (rows.transportedRemainderSource.compileEvolution value)
        (rows.transportedRemainderSource.compileExact value) }

def writeSealEquiv (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (context : WriteContext source) :
    GeneratedLedgerWriteRowAt rows context.2.1 context.2.2.2.1 context.2.2.2.2 ≃
      rows.IncidenceOccurrenceAt context.2.1 context.2.2.2.1 context.2.2.2.2 where
  toFun := fun row => row.event
  invFun := rows.generate
  left_inv := by
    rintro ⟨event, evolution, evolutionEq, exactValue, exactEq⟩
    cases evolutionEq
    cases exactEq
    rfl
  right_inv := fun _ => rfl

def writeRowEquiv (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (context : WriteContext source) :
    GeneratedLedgerWriteRowAt rows context.2.1 context.2.2.2.1 context.2.2.2.2 ≃
      GeneratedLedgerWriteRowAt (writeSource p rows) context.2.1 context.2.2.2.1 context.2.2.2.2 :=
  (writeSealEquiv rows context).trans (writeSealEquiv (writeSource p rows) context).symm

theorem writeRow_evolution (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (context : WriteContext source)
    (row : GeneratedLedgerWriteRowAt rows context.2.1 context.2.2.2.1 context.2.2.2.2) :
    (writeRowEquiv p rows context row).evolution = row.evolution := row.evolution_eq

theorem writeRow_exact (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (context : WriteContext source)
    (row : GeneratedLedgerWriteRowAt rows context.2.1 context.2.2.2.1 context.2.2.2.2) :
    (writeRowEquiv p rows context row).exact = p.exact context row.exact := congrArg (p.exact context) row.exact_eq

theorem writeRow_incidence (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (context : WriteContext source)
    (row : GeneratedLedgerWriteRowAt rows context.2.1 context.2.2.2.1 context.2.2.2.2) :
    generated.exact_incidence (writeRowEquiv p rows context row).exact =
      p.incidence (incidenceContext context) (old.exact_incidence row.exact) := by
  exact (congrArg (generated.project context) (writeRow_exact p rows context row)).trans
    (p.project context row.exact)

def remainder (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (point : Point source)
    (target : CompleteLiveLedgerAt N) (value : GeneratedLedgerTransportedRemainderAt rows point.2 target) :
    GeneratedLedgerTransportedRemainderAt (writeSource p rows) point.2 target :=
  (writeSource p rows).generateTransportedRemainder point.2 target value.event value.selected

def remainderEquiv (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (point : Point source)
    (target : CompleteLiveLedgerAt N) :
    GeneratedLedgerTransportedRemainderAt rows point.2 target ≃
      GeneratedLedgerTransportedRemainderAt (writeSource p rows) point.2 target where
  toFun := remainder p rows point target
  invFun := fun value => rows.generateTransportedRemainder point.2 target value.event value.selected
  left_inv := by intro value; cases value; rfl
  right_inv := by intro value; cases value; rfl

theorem remainder_generate (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (point : Point source)
    (target : CompleteLiveLedgerAt N) :
    Option.map (remainder p rows point target) (rows.generateTransportedRemainder? point.2 target) =
      (writeSource p rows).generateTransportedRemainder? point.2 target := by
  unfold LedgerWriteRowSourceAt.generateTransportedRemainder?
  dsimp only [writeSource]
  split <;> rfl

theorem remainder_evolution (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (point : Point source)
    (target : CompleteLiveLedgerAt N) (value : GeneratedLedgerTransportedRemainderAt rows point.2 target) :
    (remainder p rows point target value).evolution = value.evolution := rfl

theorem remainder_certification (rows : LedgerWriteRowSourceAt source old.exactTransitionAt) (point : Point source)
    (target : CompleteLiveLedgerAt N) (value : GeneratedLedgerTransportedRemainderAt rows point.2 target) :
    (certificationEquiv p point target.support value.evolution).symm
      (remainder p rows point target value).exact = value.exact :=
  (certificationEquiv p point target.support value.evolution).symm_apply_apply value.exact

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
