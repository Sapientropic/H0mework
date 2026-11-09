import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Path.State
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Same
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Admission.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open Quantities.Execution (next query)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  {claim : ClaimAt source attack community key}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  (current : State claim past)

local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)

structure Step (input : Input) where
  emission : Emission current.resident
  next : State claim (past ++ [input])
  generated : emission.next = next.resident.erase
  keepsAddress : HEq (emission.forwardAddress current.address) next.address

namespace Step

variable (input : Option (Compile.RawInput Party Good Port Technology Instrument))

private def finish (atTarget : Attached claim (past ++ [input]) (cutAfter claim past input))
    (action : Emission current.resident) (generated : action.next = atTarget.resident.erase)
    (kept : HEq (action.forwardAddress current.address) atTarget.address) : Step current input where
  emission := action
  next := atTarget.rebase (original_snoc claim past input)
  generated := generated.trans (atTarget.rebase_erase (original_snoc claim past input)).symm
  keepsAddress := kept.trans (atTarget.rebase_address (original_snoc claim past input)).symm

variable {current input} in
def forwardAddress (edge : Step current input) (address : Address current.world) : Address edge.next.world :=
  cast (congrArg (fun visit : AnyAuthoritativeRootCurrent => Address visit.N) edge.generated)
    (edge.emission.forwardAddress address)

theorem the_written_address_is_the_transported_address (edge : Step current input) :
    edge.forwardAddress current.address = edge.next.address :=
  eq_of_heq ((cast_heq _ _).trans edge.keepsAddress)

private theorem same_address {N M J : WorldRelationNetwork}
    {law : DebtActivationLaw} (shape : Shape law N J) (same : M = N) :
    let carried : Shape law M J := same.symm ▸ shape
    (shape.repairKey, shape.repairClaim) = (carried.repairKey, carried.repairClaim) := by cases same; rfl

private def material (ready : ¬ NativeWork (query (originalAt claim past) input)) : Step current input :=
  let edge := History.originalEdge (originalAt claim past) input (.inl ready)
  let position := current.position.publish input
  let motion := current.position.publication input
  let waiting := Birth.Carry.waiting position.phase
  let balance := recordedDue source attack (past ++ [input]) community key
  finish current input
    ⟨position, current.world, Same.afterShape (shape := current.shape) edge,
      Same.landed current.resident edge motion waiting⟩
    (.sequential (Same.generated current.resident edge motion waiting balance))
    (Same.actual_write_generates_the_next_resident current.resident edge motion waiting balance)
    (heq_of_eq (same_address current.shape edge.sameNetwork))

private def accounting (work : NativeWork (query (originalAt claim past) input))
    (absent : registrationAt (query (originalAt claim past) input) = none) : Step current input :=
  let edge := History.originalEdge (originalAt claim past) input (.inr absent)
  let position := current.position.account input (native_step_has_no_material_items input work)
  let carry : Motion (Birth.law claim) current.position.phase position.phase :=
    .inr (.waiting current.position.phase)
  let waiting := Birth.Carry.waiting position.phase
  let balance := recordedDue source attack (past ++ [input]) community key
  finish current input
    ⟨position, current.world, Same.afterShape (shape := current.shape) edge,
      Same.landed current.resident edge carry waiting⟩
    (.sequential (Same.generated current.resident edge carry waiting balance))
    (Same.actual_write_generates_the_next_resident current.resident edge carry waiting balance)
    (heq_of_eq (same_address current.shape edge.sameNetwork))

def registered (work : NativeWork (query (originalAt claim past) input))
    (registered : Admission.Registration (query (originalAt claim past) input).native)
    (selected : registrationAt (query (originalAt claim past) input) = some registered) : Step current input :=
  let visit := current.resident.atQuery (cut := originalAt claim past) input
  let position := current.position.account input (native_step_has_no_material_items input work)
  let original := selected_registration_is_the_original_native_next input work selected
  let landed : Attached claim (past ++ [input]) (Admission.nextNative registered) :=
    ⟨position, _, Admission.nextShape (shape := Resident.queryShape (shape := current.shape) input) registered,
      Admission.landed visit registered⟩
  finish current input (landed.rebase original.symm)
    (.admission (Admission.generated visit registered work))
    ((Admission.actual_admission_generates_the_next_resident visit registered work).trans
      (landed.rebase_erase original.symm).symm)
    ((by
      have same : let queried := Resident.queryShape (cut := originalAt claim past) input current.shape
          current.address = (queried.repairKey, queried.repairClaim) := by cases input <;> rfl
      exact heq_of_eq (congrArg (fun a : Address current.world =>
        ((Sum.inl a.1, Sum.inl a.2) : Address landed.world)) same) :
      HEq ((Emission.admission (Admission.generated visit registered work)).forwardAddress current.address)
        landed.address).trans (landed.rebase_address original.symm).symm)

theorem registered_keeps_phase (work : NativeWork (query (originalAt claim past) input))
    (registered : Admission.Registration (query (originalAt claim past) input).native)
    (selected : registrationAt (query (originalAt claim past) input) = some registered) :
    (Step.registered current input work registered selected).next.position.phase = current.position.phase := by
  simp only [Step.registered, finish, Attached.rebase_position]
  rfl

end Step

/-- Run one actual source input through the original dispatcher. Each
branch returns the kernel action and the authority of its own successor. -/
def step (input : Input) : Step current input :=
  match inspect (query (originalAt claim past) input) with
  | .material ready => Step.material current input ready
  | .accounting work absent => Step.accounting current input work absent
  | .registration work registered selected => Step.registered current input work registered selected

theorem inspect_registration (input : Input) (work : NativeWork (query (originalAt claim past) input))
    {registered : Admission.Registration (query (originalAt claim past) input).native}
    (selected : registrationAt (query (originalAt claim past) input) = some registered) :
    inspect (query (originalAt claim past) input) = .registration work registered selected := by
  unfold inspect
  rw [dif_pos work]
  split
  · rename_i noneFound
    rw [selected] at noneFound
    cases noneFound
  · rename_i found original
    cases Option.some.inj (original.symm.trans selected)
    rfl

theorem step_is_registration (input : Input)
    (work : NativeWork (query (originalAt claim past) input))
    {registered : Admission.Registration (query (originalAt claim past) input).native}
    (selected : registrationAt (query (originalAt claim past) input) = some registered) :
    step current input = Step.registered current input work registered selected := by
  unfold step
  rw [inspect_registration (claim := claim) (past := past) input work selected]

theorem the_original_registration_is_consumed_at_this_visit (input : Input)
    (work : NativeWork (query (originalAt claim past) input))
    {registered : Admission.Registration (query (originalAt claim past) input).native}
    (selected : registrationAt (query (originalAt claim past) input) = some registered) :
    (step current input).emission = .admission
      (Admission.generated (current.resident.atQuery (cut := originalAt claim past) input) registered work) := by
  rw [step_is_registration current input work selected]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
