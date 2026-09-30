import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Section
import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.Whole

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

private theorem event_cast_support {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) {c d : V.Current} (same : c = d)
    (event : source.toRootSource.actual.OccurrenceAt c) :
    (Equiv.cast (congrArg source.toRootSource.actual.OccurrenceAt same) event).1 = event.1 := by
  cases same
  rfl

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)

/-- Source and target support follow the exact original events. Both full
ledger tables and every terminal entry are transported by the signed network
consumer; a current cast changes no support or receipt. -/
def ledgerForEquiv {current : V.Current} (event : original.toRootSource.actual.OccurrenceAt current)
    (branch : EvolutionAt V current) (target : TargetFor original branch) :
    LedgerFor original event branch target ≃
      LedgerFor generated (p.event current event) (v.evolution current branch) (targetEquiv p branch target) := by
  cases branch with
  | nativeWrite write =>
      have targetSupport := (event_cast_support generated (v.native_eq current write).symm
        (p.event (V.nativeTarget write) target)).trans (p.support_eq (V.nativeTarget write) target)
      exact (n.wholeLedgerEquiv event.1 target.1).trans (Equiv.cast
        (congrArg₂ (fun s t : G.Support => LedgerWriteEvolutionAt G ⟨s⟩ ⟨t⟩)
          (p.support_eq current event).symm targetSupport.symm))
  | relationWrite write =>
      have targetSupport := (event_cast_support generated (v.relation_eq current write).symm
        (p.event (V.relationTarget write) target)).trans (p.support_eq (V.relationTarget write) target)
      exact (n.wholeLedgerEquiv event.1 target.1).trans (Equiv.cast
        (congrArg₂ (fun s t : G.Support => LedgerWriteEvolutionAt G ⟨s⟩ ⟨t⟩)
          (p.support_eq current event).symm targetSupport.symm))
  | continuedTransport write =>
      have targetSupport := (event_cast_support generated (v.continued_eq current write).symm
        (p.event (V.continuedTarget write) target)).trans (p.support_eq (V.continuedTarget write) target)
      exact (n.wholeLedgerEquiv event.1 target.1).trans (Equiv.cast
        (congrArg₂ (fun s t : G.Support => LedgerWriteEvolutionAt G ⟨s⟩ ⟨t⟩)
          (p.support_eq current event).symm targetSupport.symm))
  | borromeanRedirect write =>
      have targetSupport := (event_cast_support generated (v.redirect_eq current write).symm
        (p.event (V.redirectTarget write) target)).trans (p.support_eq (V.redirectTarget write) target)
      exact (n.wholeLedgerEquiv event.1 target.1).trans (Equiv.cast
        (congrArg₂ (fun s t : G.Support => LedgerWriteEvolutionAt G ⟨s⟩ ⟨t⟩)
          (p.support_eq current event).symm targetSupport.symm))
  | faithfulTerminal terminal =>
      exact (n.wholeTerminalEquiv event.1).trans (Equiv.cast
        (congrArg (fun s : G.Support => LedgerTerminalEvolutionAt G ⟨s⟩) (p.support_eq current event).symm))

/-- One whole dependent target/ledger pair is carried through the actual
compile equality. The complete original Compilation value is recovered. -/
def fullCompilationEquiv {current : V.Current} (event : original.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt original event ≃
      SourceNativeLedgerEvolutionAt generated (p.event current event) :=
  (compilationEquiv original event).trans
    ((bodyEquiv original event (original.toRootSource.actual.compile event)).trans
      ((Equiv.sigmaCongr (targetEquiv p (original.toRootSource.actual.compile event))
        (fun target => ledgerForEquiv p event _ target)).trans
        ((Equiv.cast (congrArg
          (fun branch : EvolutionAt W (v.current current) =>
            Sigma (LedgerFor generated (p.event current event) branch))
          (p.compile_eq current event).symm)).trans
          ((bodyEquiv generated (p.event current event)
            (generated.toRootSource.actual.compile (p.event current event))).symm.trans
            (compilationEquiv generated (p.event current event)).symm))))

def compilationSectionEquiv : CompilationSection original ≃ CompilationSection generated :=
  Equiv.piCongr (pointEquiv p) (fun point => fullCompilationEquiv p point.2)

def originalCompilations (compiler : SourceNativeLedgerCompiler original) : CompilationSection original :=
  fun point => compiler.compile point.2

theorem compilationSection_at (sectionValue : CompilationSection original)
    (point : Sigma original.toRootSource.actual.OccurrenceAt) :
    compilationSectionEquiv p sectionValue (pointEquiv p point) = fullCompilationEquiv p point.2 (sectionValue point) :=
  Equiv.piCongr_apply_apply _ _ _ _

theorem full_original_compilation_recovers (compiler : SourceNativeLedgerCompiler original)
    (point : Sigma original.toRootSource.actual.OccurrenceAt) :
    (fullCompilationEquiv p point.2).symm
      (compilationSectionEquiv p (originalCompilations compiler) (pointEquiv p point)) = compiler.compile point.2 := by
  rw [compilationSection_at, Equiv.symm_apply_apply]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
