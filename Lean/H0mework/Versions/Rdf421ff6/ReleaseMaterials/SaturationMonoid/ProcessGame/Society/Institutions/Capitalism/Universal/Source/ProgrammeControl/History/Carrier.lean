import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.Root.TraceOrigin

/-! This is a finite read of already generated root history.  Words are
never flattened and executed again: each entry keeps its original visit,
local instruction index and exact before-state, including the source clock.
The additional ordinal records order inside the read, not event identity. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program ProgrammeFace ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Kernel.AssetAuthority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev Visit := ActualBirth.Visit input
abbrev Address := (visit : Visit input) × RootFace.Item input visit

namespace Address
def raw (address : Address input) := address.2.val
def origin (address : Address input) := RootFace.original input address.1 address.2

omit [DecidableEq Port] in
theorem exact_original (address : Address input) :
    (address.origin input).instruction? input = some (address.raw input) :=
  RootFace.original_decodes_exact_item input address.1 address.2

def disposition (address : Address input) := (address.origin input).disposition input
end Address

def wordAddresses (visit : Visit input) : List (Address input) :=
  (Registered.traceItems input visit.current).attach.map fun item => ⟨visit, item⟩

private def priorAddresses : {current : (Root.ProgrammeSource.V input).Current} →
    (ActualBirth.root input).ReachableAt current → List (Address input)
  | _, .initial => []
  | _, .step prior _ => priorAddresses prior ++ wordAddresses input ⟨_, prior⟩

/-- The endpoint itself is excluded.  It may be the financial process's
next not-yet-executed word; no fact from that word enters this read. -/
def addressesBefore (endpoint : Visit input) : List (Address input) :=
  priorAddresses input endpoint.history

omit [DecidableEq Port] in
theorem addressesBefore_next (visit : Visit input)
    {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((ActualBirth.root input).evolutionAt visit.current).nextCurrent? = some target) :
    addressesBefore input (visit.next nextEq) = addressesBefore input visit ++ wordAddresses input visit := rfl

omit [DecidableEq Port] in
private theorem transportPrior (P : Visit input → Prop)
    (step : ∀ (visit : Visit input) {next : (Root.ProgrammeSource.V input).Current}
      (nextEq : ((ActualBirth.root input).evolutionAt visit.current).nextCurrent? = some next),
      P visit → P (visit.next nextEq)) :
    {current : (Root.ProgrammeSource.V input).Current} →
    (history : (ActualBirth.root input).ReachableAt current) →
    (address : Address input) → address ∈ priorAddresses input history → P address.1 → P ⟨current, history⟩
  | _, .initial, _, member, _ => False.elim (List.not_mem_nil member)
  | _, .step prior nextEq, address, member, holds => by
      apply step ⟨_, prior⟩ nextEq
      rcases List.mem_append.mp member with previous | here
      · exact transportPrior P step prior address previous holds
      · obtain ⟨item, _, same⟩ := List.mem_map.mp here
        have visitEq := congrArg (fun located : Address input => located.1) same
        exact Eq.mpr (congrArg P visitEq) holds

omit [DecidableEq Port] in
/-- Same-root successor transport is inherited from the original history;
the finite read creates neither a replacement occurrence nor an identity. -/
theorem address_before_transports (P : Visit input → Prop)
    (step : ∀ (visit : Visit input) {next : (Root.ProgrammeSource.V input).Current}
      (nextEq : ((ActualBirth.root input).evolutionAt visit.current).nextCurrent? = some next),
      P visit → P (visit.next nextEq))
    (endpoint : Visit input) (address : Address input)
    (member : address ∈ addressesBefore input endpoint) (holds : P address.1) : P endpoint :=
  transportPrior input P step endpoint.history address member holds

abbrev Entry (endpoint : Visit input) :=
  { located : Nat × Address input // located ∈ (addressesBefore input endpoint).zipIdx.map Prod.swap }

namespace Entry
def position {endpoint : Visit input} (entry : Entry input endpoint) : Nat := entry.val.1
def address {endpoint : Visit input} (entry : Entry input endpoint) : Address input := entry.val.2
def raw {endpoint : Visit input} (entry : Entry input endpoint) := (entry.address input).raw input
def origin {endpoint : Visit input} (entry : Entry input endpoint) := (entry.address input).origin input

omit [DecidableEq Port] in
theorem original_visit_and_local_index {endpoint : Visit input} (entry : Entry input endpoint) :
    (entry.origin input).visit = (entry.address input).1 ∧
    (entry.origin input).traceIndex? = some (entry.raw input).index ∧
    (entry.origin input).instruction? input = some (entry.raw input) :=
  ⟨rfl, rfl, (entry.address input).exact_original input⟩

omit [DecidableEq Port] in
theorem original_before_and_clock {endpoint : Visit input} (entry : Entry input endpoint) :
    (entry.raw input).before = (entry.address input).2.val.before ∧
    (entry.raw input).before.clock = (entry.address input).2.val.before.clock := ⟨rfl, rfl⟩
end Entry

def entries (endpoint : Visit input) : List (Entry input endpoint) :=
  ((addressesBefore input endpoint).zipIdx.map Prod.swap).attach

def target (endpoint : Visit input) := Root.ProgrammeSource.rawCurrent input endpoint.current

def parties (endpoint : Visit input) : List Party :=
  ((addressesBefore input endpoint).flatMap (fun address => itemParties input.law (address.raw input))).dedup

def actual (visit : Visit input) : Visit input := visit.next rfl

omit [DecidableEq Port] in
theorem actual_includes_original_word (visit : Visit input) :
    addressesBefore input (actual input visit) = addressesBefore input visit ++ wordAddresses input visit := rfl

#print axioms addressesBefore_next
#print axioms Entry.original_visit_and_local_index
#print axioms Entry.original_before_and_clock

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History
