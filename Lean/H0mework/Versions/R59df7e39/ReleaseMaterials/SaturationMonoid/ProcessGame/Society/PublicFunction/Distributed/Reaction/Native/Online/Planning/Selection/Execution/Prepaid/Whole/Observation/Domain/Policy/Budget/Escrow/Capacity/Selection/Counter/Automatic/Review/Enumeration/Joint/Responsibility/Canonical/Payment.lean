import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Runtime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Payment
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {generatedSource : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue generatedSource.snapshot} {all : Candidates generatedSource catalogue} {owner : Ready all}
  (made : Generated owner) (index : Index prepared) (first : First made)


abbrev Width := ProgrammeSource.registrationSize (oldInput made index)+2+1
abbrev Row (code : Code made index) := GeneratedLedgerWriteRowAt (rowSource made index first)
  (emitted made index first 0) (entryAt made index 0 code) (entryAt made index 1 code)
abbrev Patch := FiniteGeneratedLedgerWritePatchAt (rowSource made index first)
  (emitted made index first 0) ⟨supportAt made index 1⟩
def row (code : Code made index) : Row made index first code :=
  (rowSource made index first).generate (.generated 0 code)
def units := Width made index+1

def table (cache : (code : Code made index) → Row made index first code) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource made index first) (emitted made index first 0) ⟨supportAt made index 1⟩ where
  size := Width made index
  sourceEntryAt := entryAt made index 0
  targetEntryAt := entryAt made index 1
  rowAt := cache

def assemble (cache : (code : Code made index) → Row made index first code) : Patch made index first :=
  .complete (table made index first cache) {
    destinationIndex := indexOf made index
    originIndex := indexOf made index
    destination_sound := entry_index made index
    origin_sound := entry_index made index }

theorem assemble_exact (cache : (code : Code made index) → Row made index first code)
    (actual : ∀ code,cache code = row made index first code) :
    assemble made index first cache = patch made index first 0 := by
  have same : cache = row made index first := funext actual
  cases same
  rfl

/-- The only executable constructor sequence: every row, then complete-patch assembly. -/
inductive Operation where
  | row (code : Code made index)
  | assemble

def operation (ordinal : Fin (units made index)) : Operation made index :=
  if inside : ordinal.val < Width made index then .row ⟨ordinal.val,inside⟩ else .assemble

structure Cursor where
  private mk ::
  done : Nat
  bounded : done ≤ units made index
  reserved : done ≤ made.unused
  cache : (code : Code made index) → code.val < done → Row made index first code
  cache_exact : ∀ code inside,cache code inside = row made index first code
  output : Option (Patch made index first)
  output_exact : output = if Width made index < done then some (patch made index first 0) else none
  work : List (Fin (units made index))
  ordered : work.map Fin.val = List.range done

def initial : Cursor made index first :=
  ⟨0,by unfold units;omega,Nat.zero_le _,fun code inside => by omega,
    (by intro code inside;omega),none,by simp,[],rfl⟩

namespace Cursor
variable {made index first}
def step (before : Cursor made index first) : Cursor made index first :=
  if credit : before.done < made.unused then
    if inside : before.done < Width made index then
      let current : Code made index := ⟨before.done,inside⟩
      let generated := row made index first current
      let cache : (code : Code made index) → code.val < before.done+1 → Row made index first code := fun code bounded =>
        if old : code.val < before.done then before.cache code old
        else by
          have same : code = current := Fin.ext (by dsimp only [current];omega)
          exact same.symm ▸ generated
      ⟨before.done+1,by unfold units;omega,by omega,cache,(by
          intro code bounded
          dsimp only [cache]
          split
          · exact before.cache_exact _ _
          · rename_i old
            have same : code = current := Fin.ext (by dsimp only [current];omega)
            cases same
            rfl),none,(by simp only [Nat.not_lt.mpr (by omega : before.done+1 ≤ Width made index),if_false]),
        before.work++[⟨before.done,by unfold units;omega⟩],by
          rw [List.map_append,before.ordered,List.map_singleton,List.range_succ]⟩
    else if sealing : before.done = Width made index then
      let cache := fun code : Code made index => before.cache code (by rw [sealing];exact code.isLt)
      let complete := assemble made index first cache
      ⟨before.done+1,by unfold units;omega,by omega,(fun code _ => cache code),(by intro code _;exact before.cache_exact _ _),
        some complete,(by
          simp only [show Width made index < before.done+1 by omega,if_true,Option.some.injEq]
          exact assemble_exact made index first cache (fun code => before.cache_exact code _)),
        before.work++[⟨before.done,by unfold units;omega⟩],by
          rw [List.map_append,before.ordered,List.map_singleton,List.range_succ]⟩
    else before
  else before

def run : Nat → Cursor made index first → Cursor made index first
  | 0,before => before
  | n+1,before => if before.done < min made.unused (units made index) then run n before.step else before

theorem work_length (cursor : Cursor made index first) : cursor.work.length = cursor.done := by
  have same := congrArg List.length cursor.ordered
  simpa only [List.length_map,List.length_range] using same

theorem step_done (before : Cursor made index first) :
    before.step.done = if before.done < made.unused ∧ before.done < units made index then before.done+1 else before.done := by
  dsimp only [step]
  split
  · rename_i credit
    split
    · rename_i inside
      rw [if_pos ⟨credit,by unfold units;omega⟩]
    · rename_i inside
      split
      · rename_i sealing
        rw [if_pos ⟨credit,by unfold units;omega⟩]
      · rename_i sealing
        rw [if_neg (by intro both;unfold units at both;omega)]
  · rename_i credit
    rw [if_neg (by intro both;exact credit both.1)]

theorem run_done (n : Nat) (before : Cursor made index first) :
    (run n before).done = min (before.done+n) (min made.unused (units made index)) := by
  induction n generalizing before with
  | zero =>
      dsimp only [run]
      have a := before.bounded;have b := before.reserved
      omega
  | succ n ih =>
      dsimp only [run]
      split
      · rw [ih,step_done]
        split <;> omega
      · have a := before.bounded;have b := before.reserved
        omega

end Cursor

def execute : Cursor made index first := Cursor.run made.unused (initial made index first)
theorem spent_exact : (execute made index first).done = min made.unused (units made index) := by
  unfold execute
  rw [Cursor.run_done]
  change min (0+made.unused) (min made.unused (units made index)) = _
  omega

structure Built where
  private mk ::
  construction : Cursor made index first
  generated : construction = execute made index first
  patch : Patch made index first
  produced : construction.output = some patch

inductive Result where
  | ready (paid : Built made index first)
  | shortfall (construction : Cursor made index first) (generated : construction = execute made index first)
      (absent : construction.output = none) (short : made.unused < units made index)

def produce : Result made index first :=
  let construction := execute made index first
  match produced : construction.output with
  | some patch => .ready ⟨construction,rfl,patch,produced⟩
  | none => .shortfall construction rfl produced (by
      have actual := construction.output_exact
      rw [produced] at actual
      have count := spent_exact made index first
      by_contra enough
      have all : construction.done = units made index := by change (execute made index first).done = _;omega
      rw [all] at actual
      have positive : Width made index < units made index := by unfold units;omega
      rw [if_pos positive] at actual
      cases actual)

namespace Built
variable {made index first} (paid : Built made index first)
theorem patch_exact : paid.patch = Canonical.patch made index first 0 := by
  have actual := paid.construction.output_exact
  rw [paid.produced] at actual
  split at actual
  · exact Option.some.inj actual
  · cases actual

include paid in
theorem enough : units made index ≤ made.unused := by
  have actual := paid.construction.output_exact
  rw [paid.produced] at actual
  split at actual
  · rename_i complete
    have bounded := paid.construction.bounded
    have reserved := paid.construction.reserved
    unfold units at *
    omega
  · cases actual
end Built

namespace Cursor
variable {made index first} (cursor : Cursor made index first)
def ordinal (event : Fin cursor.work.length) : Nat := Review.offset owner+made.spent+event.val

def slot (event : Fin cursor.work.length) :
    Fin (((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).bill.units) :=
  ⟨cursor.ordinal event,by
    rw [((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).size]
    have a := cursor.reserved;have b := made.one_tail_covers_all_phases
    have c := Review.offset_is_covered_by_the_same_invoice owner
    have d := event.isLt;have length := cursor.work_length
    dsimp only [ordinal,Review.capacity] at *
    omega⟩

theorem distinct_slots : Function.Injective cursor.slot := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  dsimp only [slot,ordinal] at values
  omega

theorem separate_from_prior_work (old : Fin made.execution.work.length) (event : Fin cursor.work.length) :
    cursor.slot event ≠ made.slot index old := by
  intro same
  have values := congrArg Fin.val same
  have bounded := old.isLt
  change Review.offset owner+made.execution.work.length+event.val = Review.offset owner+old.val at values
  omega

theorem separate_from_old_tokens (old : owner.release.Token) (event : Fin cursor.work.length) :
    cursor.slot event ≠ owner.release.slot index old := by
  intro same
  have values := congrArg Fin.val same
  have bounded := Review.every_old_work_slot_precedes_the_new_tail owner old
  change Review.offset owner+made.execution.work.length+event.val = owner.release.ordinal old at values
  omega

theorem every_actual_constructor_has_a_successful_prepaid_slot (event : Fin cursor.work.length) :
    ((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).bill.payment.succeeded = true ∧
    (cursor.slot event).val = Review.offset owner+made.execution.work.length+event.val :=
  ⟨((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).paid,rfl⟩

def operations : List (Operation made index) := cursor.work.map (operation made index)
def residual : List (Operation made index) := ((List.finRange (units made index)).drop cursor.done).map (operation made index)

theorem complete_work_partition : cursor.work.length+cursor.residual.length = units made index := by
  rw [cursor.work_length]
  simp only [residual,List.length_map,List.length_drop,List.length_finRange]
  have bounded := cursor.bounded
  omega

theorem all_native_receipt_slots_are_separate (receipt : NativePayment.At made)
    (native : Fin receipt.packet.receipt.checked.work.length) (event : Fin cursor.work.length) :
    cursor.slot event ≠ receipt.slot index native :=
  cursor.separate_from_prior_work (receipt.creditEvent native) event

end Cursor

theorem zero_credit_preserves_the_empty_constructor (empty : made.unused = 0) :
    execute made index first = initial made index first := by simp only [execute,empty,Cursor.run]

theorem shortfall_residual_is_exact (construction : Cursor made index first)
    (actual : construction = execute made index first) (short : made.unused < units made index) :
    construction.done = made.unused ∧ construction.residual.length = units made index-made.unused := by
  subst construction
  have count := spent_exact made index first
  constructor
  · omega
  · simp only [Cursor.residual,List.length_map,List.length_drop,List.length_finRange]
    omega


end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Payment
