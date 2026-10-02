import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Branch
import H0mework.Foundation.Ledger.SourceCompiler

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def TargetFor {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V)
    {current : V.Current} : EvolutionAt V current → Type
  | .nativeWrite write => source.toRootSource.actual.OccurrenceAt (V.nativeTarget write)
  | .relationWrite write => source.toRootSource.actual.OccurrenceAt (V.relationTarget write)
  | .continuedTransport write => source.toRootSource.actual.OccurrenceAt (V.continuedTarget write)
  | .borromeanRedirect write => source.toRootSource.actual.OccurrenceAt (V.redirectTarget write)
  | .faithfulTerminal _ => PUnit

def branchTarget {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    (branch : EvolutionAt V current) : BranchData source event branch → TargetFor source branch := by
  cases branch
  · exact Sigma.fst
  · exact Sigma.fst
  · exact Sigma.fst
  · exact Sigma.fst
  · exact fun _ => .unit

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)

def targetEquiv {current : V.Current} (branch : EvolutionAt V current) :
    TargetFor original branch ≃ TargetFor generated (v.evolution current branch) := by
  cases branch with
  | nativeWrite write =>
      exact (p.event _).trans (Equiv.cast
        (congrArg generated.toRootSource.actual.OccurrenceAt (v.native_eq current write).symm))
  | relationWrite write =>
      exact (p.event _).trans (Equiv.cast
        (congrArg generated.toRootSource.actual.OccurrenceAt (v.relation_eq current write).symm))
  | continuedTransport write =>
      exact (p.event _).trans (Equiv.cast
        (congrArg generated.toRootSource.actual.OccurrenceAt (v.continued_eq current write).symm))
  | borromeanRedirect write =>
      exact (p.event _).trans (Equiv.cast
        (congrArg generated.toRootSource.actual.OccurrenceAt (v.redirect_eq current write).symm))
  | faithfulTerminal => exact Equiv.refl _

def targetAtEquiv {current : V.Current} (event : original.toRootSource.actual.OccurrenceAt current) :
    TargetFor original (original.toRootSource.actual.compile event) ≃
      TargetFor generated (generated.toRootSource.actual.compile (p.event current event)) :=
  (targetEquiv p _).trans (Equiv.cast
    (congrArg (TargetFor generated) (p.compile_eq current event).symm))

def pointEquiv : Sigma original.toRootSource.actual.OccurrenceAt ≃
    Sigma generated.toRootSource.actual.OccurrenceAt := Equiv.sigmaCongr v.current p.event

abbrev TargetSection {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V) :=
  (point : Sigma source.toRootSource.actual.OccurrenceAt) → TargetFor source (source.toRootSource.actual.compile point.2)

def targetSectionEquiv : TargetSection original ≃ TargetSection generated :=
  Equiv.piCongr (pointEquiv p) (fun point => targetAtEquiv p point.2)

theorem targetSection_at (sectionValue : TargetSection original)
    (point : Sigma original.toRootSource.actual.OccurrenceAt) :
    targetSectionEquiv p sectionValue (pointEquiv p point) = targetAtEquiv p point.2 (sectionValue point) :=
  Equiv.piCongr_apply_apply _ _ _ _

/-- All target occurrences are read from the full original compiler at their
own event; no emitter or future-query table is consulted. -/
def originalTargets {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) : TargetSection source :=
  fun point => branchTarget source point.2 _ (compilationEquiv source point.2 (compiler.compile point.2))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
