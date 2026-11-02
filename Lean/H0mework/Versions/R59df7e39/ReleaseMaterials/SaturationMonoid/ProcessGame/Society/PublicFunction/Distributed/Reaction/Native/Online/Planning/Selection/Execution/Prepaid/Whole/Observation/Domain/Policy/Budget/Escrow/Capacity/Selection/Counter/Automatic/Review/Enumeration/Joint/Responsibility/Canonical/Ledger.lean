import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Source

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {generatedSource : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue generatedSource.snapshot} {all : Candidates generatedSource catalogue} {owner : Ready all}
  (made : Generated owner) (index : Index prepared) (first : First made)

abbrev Code := Fin (ProgrammeSource.registrationSize (oldInput made index)+2+1)
def oldAt (tick : Nat) (row : ProgrammeWorld.Row (ProgrammeSource.registrationSize (oldInput made index))) :=
  ProgrammeSource.sourceEntry (oldInput made index) (oldCurrent made index tick) row

theorem oldAt_row (tick : Nat) (row : ProgrammeWorld.Row (ProgrammeSource.registrationSize (oldInput made index))) :
    (oldAt made index tick row).1 = row := by
  obtain ⟨current,past,same⟩ := oldCurrent_running made index tick
  dsimp only [oldAt]
  rw [same]
  rfl

theorem oldAt_claim (tick : Nat) (row : ProgrammeWorld.Row (ProgrammeSource.registrationSize (oldInput made index))) :
    (oldAt made index tick row).claim = ProgrammeWorld.claim row := by
  obtain ⟨current,past,same⟩ := oldCurrent_running made index tick
  dsimp only [oldAt]
  rw [same]
  rfl

def oldBudget : ProgrammeWorld.Row (ProgrammeSource.registrationSize (oldInput made index)) → Nat
  | .obstruction => 0
  | _ => 1

theorem oldAt_budget (tick : Nat) (row : ProgrammeWorld.Row (ProgrammeSource.registrationSize (oldInput made index))) :
    (oldAt made index tick row).progressBudget = oldBudget made index row := by
  obtain ⟨current,past,same⟩ := oldCurrent_running made index tick
  dsimp only [oldAt]
  rw [same]
  cases row <;> rfl

def entryAt (tick : Nat) : Code made index → OpenResponsibilityAt (N made index) (supportAt made index tick) :=
  Fin.cases (debtEntry (law := law owner) _ (state made tick))
    (fun code => oldEntry (law := law owner) (state? := some (state made tick))
      (oldAt made index tick (ProgrammeSource.rowAt (oldInput made index) code)))

def key : Code made index → (N made index).Responsibility :=
  Fin.cases (.inr owner) (fun code => .inl (ProgrammeSource.rowAt (oldInput made index) code))
def claimKey : Code made index → (N made index).Claim :=
  Fin.cases (.inr owner) (fun code => .inl (ProgrammeWorld.claim (ProgrammeSource.rowAt (oldInput made index) code)))

theorem entryAt_key (tick : Nat) (code : Code made index) : (entryAt made index tick code).1 = key made index code := by
  refine Fin.cases rfl (fun code => ?_) code
  exact congrArg Sum.inl (oldAt_row made index tick _)

theorem entryAt_claim (tick : Nat) (code : Code made index) : (entryAt made index tick code).claim = claimKey made index code := by
  refine Fin.cases rfl (fun code => ?_) code
  exact congrArg Sum.inl (oldAt_claim made index tick _)

def rowEvolution (tick : Nat) (code : Code made index) :
    LedgerEntryEvolutionAt (N made index) (entryAt made index tick code) (entryAt made index (tick+1) code) := by
  refine Fin.cases ?_ (fun code => ?_) code
  · exact .transferred (receipt made index tick) rfl rfl (budget_never_refills made tick)
  · refine .transferred (inheritedReceipt made index tick) rfl
      ((entryAt_claim made index tick code.succ).trans (entryAt_claim made index (tick+1) code.succ).symm) ?_
    change (oldAt made index (tick+1) _).progressBudget ≤ (oldAt made index tick _).progressBudget
    rw [oldAt_budget,oldAt_budget]


def indexOf {tick : Nat} (entry : OpenResponsibilityAt (N made index) (supportAt made index tick)) : Code made index :=
  match entry.1 with
  | .inl row => (ProgrammeSource.rowIndex (oldInput made index) row).succ
  | .inr _ => 0

theorem open_subsingleton (support : (N made index).Support) (responsibility : (N made index).Responsibility) :
    Subsingleton ((N made index).OpenAt support responsibility) := by
  rcases support with ⟨base,active⟩
  cases responsibility with
  | inl old => exact ProgrammeRestructuring.open_subsingleton (oldInput made index) base old
  | inr debt => cases active <;> dsimp only [N,ExtendedNetwork,extendedNetwork,DebtOpenAt] <;> infer_instance

theorem entry_ext {tick : Nat} {left right : OpenResponsibilityAt (N made index) (supportAt made index tick)}
    (same : left.1 = right.1) : left = right := by
  rcases left with ⟨left,opened⟩;rcases right with ⟨right,other⟩
  cases same
  have equal := (open_subsingleton made index (supportAt made index tick) left).elim opened other
  cases equal
  rfl

theorem entry_index {tick : Nat} (entry : OpenResponsibilityAt (N made index) (supportAt made index tick)) :
    entryAt made index tick (indexOf made index entry) = entry := by
  apply entry_ext made index
  rw [entryAt_key]
  rcases entry with ⟨row,opened⟩
  cases row with
  | inl old => exact congrArg Sum.inl (ProgrammeSource.rowAt_index (oldInput made index) old)
  | inr debt => rcases opened with ⟨⟨same⟩⟩;cases same;rfl

theorem old_index_at (code : Fin (ProgrammeSource.registrationSize (oldInput made index)+2)) :
    ProgrammeSource.rowIndex (oldInput made index) (ProgrammeSource.rowAt (oldInput made index) code) = code := by
  refine Fin.cases rfl (fun code => ?_) code
  exact Fin.cases rfl (fun _ => rfl) code

theorem index_entry (tick : Nat) (code : Code made index) : indexOf made index (entryAt made index tick code) = code := by
  have equal := entryAt_key made index tick code
  change (match (entryAt made index tick code).1 with
    | .inl row => (ProgrammeSource.rowIndex (oldInput made index) row).succ
    | .inr _ => 0) = code
  rw [equal]
  refine Fin.cases rfl (fun code => ?_) code
  exact congrArg Fin.succ (old_index_at made index code)

inductive RawRowAt : {tick : Nat} → (occurrence : (source made index first).toRootSource.actual.OccurrenceAt tick) →
    {targetSupport : (N made index).Support} →
    OpenResponsibilityAt (N made index) ((source made index first).toRootSource.account.supportOf occurrence) → OpenResponsibilityAt (N made index) targetSupport → Type
  | generated (tick : Nat) (code : Code made index) : RawRowAt (emitted made index first tick)
      (entryAt made index tick code) (entryAt made index (tick+1) code)

def rowSource : LedgerWriteRowSourceAt (source made index first) (RawRowAt made index first) where
  IncidenceOccurrenceAt := RawRowAt made index first
  compileEvolution := by
    intro tick occurrence support before after event
    cases event with
    | generated code => exact rowEvolution made index _ code
  compileExact := fun event => event

def rows (tick : Nat) : FiniteGeneratedLedgerWriteRowsAt (rowSource made index first)
    (emitted made index first tick) ⟨supportAt made index (tick+1)⟩ where
  size := ProgrammeSource.registrationSize (oldInput made index)+2+1
  sourceEntryAt := entryAt made index tick
  targetEntryAt := entryAt made index (tick+1)
  rowAt := fun code => (rowSource made index first).generate (.generated tick code)

def coverage (tick : Nat) : LedgerCompleteFiniteCoverageAt (rows made index first tick) where
  destinationIndex := indexOf made index
  originIndex := indexOf made index
  destination_sound := entry_index made index
  origin_sound := entry_index made index

def patch (tick : Nat) : FiniteGeneratedLedgerWritePatchAt (rowSource made index first)
    (emitted made index first tick) ⟨supportAt made index (tick+1)⟩ :=
  .complete (rows made index first tick) (coverage made index first tick)

theorem destination_exact (tick : Nat) (entry : OpenResponsibilityAt (N made index) (supportAt made index tick)) :
    (((patch made index first tick).toLedgerWriteEvolution).destination entry).1 =
      entryAt made index (tick+1) (indexOf made index entry) := rfl

theorem origin_exact (tick : Nat) (entry : OpenResponsibilityAt (N made index) (supportAt made index (tick+1))) :
    (((patch made index first tick).toLedgerWriteEvolution).origin entry).1 =
      entryAt made index tick (indexOf made index entry) := rfl

theorem destination_injective (tick : Nat) : Function.Injective
    (fun entry => (((patch made index first tick).toLedgerWriteEvolution).destination entry).1) := by
  intro left right same
  change entryAt made index (tick+1) (indexOf made index left) = entryAt made index (tick+1) (indexOf made index right) at same
  have codes := congrArg (indexOf made index) same
  rw [index_entry,index_entry] at codes
  exact (entry_index made index left).symm.trans ((congrArg (entryAt made index tick) codes).trans (entry_index made index right))

theorem origin_injective (tick : Nat) : Function.Injective
    (fun entry => (((patch made index first tick).toLedgerWriteEvolution).origin entry).1) := by
  intro left right same
  change entryAt made index tick (indexOf made index left) = entryAt made index tick (indexOf made index right) at same
  have codes := congrArg (indexOf made index) same
  rw [index_entry,index_entry] at codes
  exact (entry_index made index left).symm.trans ((congrArg (entryAt made index (tick+1)) codes).trans (entry_index made index right))

def terminalRowSource : LedgerTerminalRowSourceAt (source made index first) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def ledgerCompiler : SourceNativeLedgerCompiler (source made index first) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := RawRowAt made index first
  exact_incidence := fun _ => ()
  exact_lineage := fun _ => rfl
  writeRowSource := rowSource made index first
  terminalRowSource := terminalRowSource made index first
  compile := by
    intro tick occurrence
    cases occurrence_eq_emitted made index first occurrence
    exact .nativeWrite () rfl (emitted made index first (tick+1)) (patch made index first tick).toLedgerWriteEvolution
  compilePatch := by
    intro tick occurrence
    cases occurrence_eq_emitted made index first occurrence
    exact ⟨patch made index first tick,rfl⟩

def ledgerSource : SourceNativeLedgerSource (N made index) (V made index) where
  source := source made index first
  ledgerCompiler := ledgerCompiler made index first

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical
