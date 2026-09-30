import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaCompiler.WholeRows
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Body

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
open MotherArenaNetwork MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} (coordinates : LedgerCoordinates (rank := rank) N)

def destinationGraph (material : M) (context : B) {s t : N.Support}
    (entry : OpenResponsibilityAt N s) (output : Destination s t entry) : Prop :=
  let key := destinationKey coordinates output
  r3 material key.1 context (coordinates.entry s entry) key.2

def originGraph (material : M) (context : B) {s t : N.Support}
    (entry : OpenResponsibilityAt N t) (output : Origin s t entry) : Prop :=
  let key := originKey coordinates output
  r3 material (3 + key.1) context (coordinates.entry t entry) key.2

structure WriteCheck (material : M) (context : B) (s t : N.Support) : Prop where
  destination : ∀ entry : OpenResponsibilityAt N s, ∃! output : Destination s t entry,
    destinationGraph coordinates material context entry output
  origin : ∀ entry : OpenResponsibilityAt N t, ∃! output : Origin s t entry,
    originGraph coordinates material context entry output

/-- Two independent full tables preserve legitimate split/merge. Neither table
is obtained by inverting the other or dropping an unselected stored row. -/
def write (material : M) (context : B) (s t : N.Support)
    (checked : WriteCheck coordinates material context s t) : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩ where
  destination := fun entry => Classical.choose (checked.destination entry)
  origin := fun entry => Classical.choose (checked.origin entry)

def formWrite (material : M) (context : B) (s t : N.Support) : Option (LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩) :=
  if checked : WriteCheck coordinates material context s t then some (write coordinates material context s t checked)
  else none

def TerminalCheck (material : M) (context : B) (s : N.Support) : Prop :=
  ∀ entry : OpenResponsibilityAt N s, ∃! receipt : N.DispositionAt s .supportSettlement,
    r3 material 6 context (coordinates.entry s entry) (coordinates.settlement s receipt)

def terminal (material : M) (context : B) (s : N.Support)
    (checked : TerminalCheck coordinates material context s) : LedgerTerminalEvolutionAt N ⟨s⟩ where
  discharge := fun entry => ⟨Classical.choose (checked entry)⟩

def formTerminal (material : M) (context : B) (s : N.Support) : Option (LedgerTerminalEvolutionAt N ⟨s⟩) :=
  if checked : TerminalCheck coordinates material context s then some (terminal coordinates material context s checked)
  else none

variable {V : Vocabulary.{0}} (source : SourceNativeSource N V)

def WholeCheck (material : M) (context : B) {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current) :
    (branch : EvolutionAt V current) → TargetFor source branch → Prop
  | .nativeWrite _, target => WriteCheck coordinates material context event.1 target.1
  | .relationWrite _, target => WriteCheck coordinates material context event.1 target.1
  | .continuedTransport _, target => WriteCheck coordinates material context event.1 target.1
  | .borromeanRedirect _, target => WriteCheck coordinates material context event.1 target.1
  | .faithfulTerminal _, _ => TerminalCheck coordinates material context event.1

def whole (material : M) (context : B) {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current) (branch : EvolutionAt V current)
    (target : TargetFor source branch) (checked : WholeCheck coordinates source material context event branch target) :
    LedgerFor source event branch target := by
  cases branch
  · exact write coordinates material context _ _ checked
  · exact write coordinates material context _ _ checked
  · exact write coordinates material context _ _ checked
  · exact write coordinates material context _ _ checked
  · exact terminal coordinates material context _ checked

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
