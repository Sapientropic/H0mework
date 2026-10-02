import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Consumer
import H0mework.Foundation.Ledger.Evolution

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current)

/-- The already generated structural branch fixes its full payload and target
current. Its remaining ledger data retain the actual target occurrence and
the entire ledger, or the entire terminal discharge. -/
def BranchData : EvolutionAt V current → Type
  | .nativeWrite write => Σ target : source.toRootSource.actual.OccurrenceAt (V.nativeTarget write),
      LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target.1⟩
  | .relationWrite write => Σ target : source.toRootSource.actual.OccurrenceAt (V.relationTarget write),
      LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target.1⟩
  | .continuedTransport write => Σ target : source.toRootSource.actual.OccurrenceAt (V.continuedTarget write),
      LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target.1⟩
  | .borromeanRedirect write => Σ target : source.toRootSource.actual.OccurrenceAt (V.redirectTarget write),
      LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target.1⟩
  | .faithfulTerminal _ => LedgerTerminalEvolutionAt N ⟨event.1⟩

abbrev BranchGraph := Σ branch : EvolutionAt V current,
  {_data : BranchData source event branch // source.toRootSource.actual.compile event = branch}

def toGraph : SourceNativeLedgerEvolutionAt source event → BranchGraph source event
  | .nativeWrite write structural target whole => ⟨.nativeWrite write, ⟨⟨target, whole⟩, structural⟩⟩
  | .relationWrite write structural target whole => ⟨.relationWrite write, ⟨⟨target, whole⟩, structural⟩⟩
  | .continuedTransport write structural target whole => ⟨.continuedTransport write, ⟨⟨target, whole⟩, structural⟩⟩
  | .borromeanRedirect write structural target whole => ⟨.borromeanRedirect write, ⟨⟨target, whole⟩, structural⟩⟩
  | .faithfulTerminal terminal structural whole => ⟨.faithfulTerminal terminal, ⟨whole, structural⟩⟩

def fromGraph : BranchGraph source event → SourceNativeLedgerEvolutionAt source event
  | ⟨.nativeWrite write, ⟨⟨target, whole⟩, structural⟩⟩ => .nativeWrite write structural target whole
  | ⟨.relationWrite write, ⟨⟨target, whole⟩, structural⟩⟩ => .relationWrite write structural target whole
  | ⟨.continuedTransport write, ⟨⟨target, whole⟩, structural⟩⟩ => .continuedTransport write structural target whole
  | ⟨.borromeanRedirect write, ⟨⟨target, whole⟩, structural⟩⟩ => .borromeanRedirect write structural target whole
  | ⟨.faithfulTerminal terminal, ⟨whole, structural⟩⟩ => .faithfulTerminal terminal structural whole

def graphEquiv : SourceNativeLedgerEvolutionAt source event ≃ BranchGraph source event where
  toFun := toGraph source event
  invFun := fromGraph source event
  left_inv := by intro value; cases value <;> rfl
  right_inv := by
    rintro ⟨branch, ⟨data, structural⟩⟩
    cases branch <;> rfl

private def fixedFibreEquiv {A : Type} (B : A → Type) (a : A) :
    (Σ b, {_data : B b // a = b}) ≃ B a where
  toFun := fun ⟨_, ⟨data, same⟩⟩ => Eq.mpr (congrArg B same) data
  invFun := fun data => ⟨a, ⟨data, rfl⟩⟩
  left_inv := by rintro ⟨b, ⟨data, same⟩⟩; cases same; rfl
  right_inv := fun _ => rfl

/-- Eliminate structural_eq at the exact original event without discarding
any full compilation data or adding a new structural-branch choice. -/
def compilationEquiv : SourceNativeLedgerEvolutionAt source event ≃
    BranchData source event (source.toRootSource.actual.compile event) :=
  (graphEquiv source event).trans (fixedFibreEquiv _ _)

theorem full_compilation_recovery (compiled : SourceNativeLedgerEvolutionAt source event) :
    (compilationEquiv source event).symm (compilationEquiv source event compiled) = compiled :=
  (compilationEquiv source event).symm_apply_apply compiled

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
