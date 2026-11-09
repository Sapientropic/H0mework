import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Opening
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Path.Position
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Path.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open Quantities.Execution (endAt next query endAt_append)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Script" => List Input
local notation "Native" => Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

abbrev originalAt (history : Script) := endAt (Birth.attacked claim) history

structure Attached (past : Script) (native : Native) where
  position : Position claim past
  world : WorldRelationNetwork
  shape : Shape (Birth.law claim) native.frame.N world
  resident : Resident (native := native) shape position.phase (Birth.Carry.waiting _)

abbrev State (history : Script) := Attached claim history (originalAt claim history).native

abbrev Address (world : WorldRelationNetwork) := world.Responsibility × world.Claim

namespace Attached

variable {claim} {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {before after : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

def address (state : Attached claim past before) : Address state.world :=
  (state.shape.repairKey, state.shape.repairClaim)

def rebase (same : before = after) (state : Attached claim past before) : Attached claim past after := by
  cases same
  exact state

theorem rebase_erase (same : before = after) (state : Attached claim past before) :
    (state.rebase same).resident.erase = state.resident.erase := by cases same; rfl

theorem rebase_position (same : before = after) (state : Attached claim past before) :
    (state.rebase same).position = state.position := by cases same; rfl

theorem rebase_address (same : before = after) (state : Attached claim past before) :
    HEq (state.rebase same).address state.address := by cases same; rfl

end Attached

def initial : State claim [] where
  position := Position.initial claim
  world := Birth.N claim
  shape := initialShape claim
  resident := openResident claim

abbrev cutAfter (past : Script) (input : Input) : Native := (next (originalAt claim past) input).native

theorem original_snoc (past : Script) (input : Input) :
    cutAfter claim past input = (originalAt claim (past ++ [input])).native :=
  congrArg Evolving.Epoch.Current.native (endAt_append (Birth.attacked claim) past [input]).symm

namespace Resident

variable {R : DebtActivationLaw} {joint : WorldRelationNetwork} {cut : Root.Cut Party Good Port Technology Instrument}
  {shape : Shape R cut.native.frame.N joint} {phase : R.DebtState} {wait : R.TransportAt phase phase}
  (resident : Resident shape phase wait)
  (input : Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev queryShape (shape : Shape R cut.native.frame.N joint) :
    Shape R (query cut input).native.frame.N joint :=
  match input with
  | none => shape
  | some _ => shape

/-- Installing a reader keeps the exact already-authorized ledger visit.
The original source compiler will still own any registration selected there. -/
def atQuery : Resident (native := (query cut input).native)
    (queryShape (cut := cut) (shape := shape) input) phase wait where
  V := resident.V
  root := resident.root
  visit := resident.visit
  unique := resident.unique
  support_eq := by cases input <;> exact resident.support_eq
  entry := resident.entry
  repair_eq := by cases input <;> exact resident.repair_eq
  authority := resident.authority
  structural := by cases input <;> exact resident.structural

end Resident

end

section

variable {law : DebtActivationLaw} {joint : WorldRelationNetwork}
  {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {native : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {shape : Shape law native.frame.N joint} {phase : law.DebtState} {wait : law.TransportAt phase phase}
  (current : Resident shape phase wait)

abbrev exactEvent := current.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt current.visit

/-- The two existing kernel actions consume the same live source occurrence. -/
inductive Emission
  | sequential {program : SourceNativeSequentialActualActionProgramAt current.root current.visit
      current.entry current.authority} (actual : SourceGeneratedSequentialActualActionAt program (exactEvent current))
  | admission {program : SourceNativeDebtAdmissionActualActionProgramAt current.root current.visit
      current.entry current.authority} (actual : SourceGeneratedDebtAdmissionActualActionAt program (exactEvent current))

def Emission.next : Emission current → AnyAuthoritativeRootCurrent
  | .sequential actual => ⟨actual.target.TargetN, actual.target.targetAnswerAndNext.nextCurrent⟩
  | .admission actual => ⟨actual.target.TargetN, actual.target.targetAnswerAndNext.nextCurrent⟩

variable {current} in
def Emission.forwardAddress (action : Emission current) : Address joint → Address action.next.N :=
  match action with
  | .sequential actual => fun address =>
      (actual.target.translation.responsibility.forward address.1, actual.target.translation.claim.forward address.2)
  | .admission _ => fun address => (.inl address.1, .inl address.2)

variable {current} in
theorem Emission.forwardAddress_injective (action : Emission current) :
    Function.Injective action.forwardAddress := by
  cases action with
  | sequential actual =>
    intro left right same
    exact Prod.ext
      (Function.LeftInverse.injective actual.target.translation.responsibility.backward_forward (congrArg Prod.fst same))
      (Function.LeftInverse.injective actual.target.translation.claim.backward_forward (congrArg Prod.snd same))
  | admission =>
    intro left right same
    exact Prod.ext (Sum.inl.inj (congrArg Prod.fst same)) (Sum.inl.inj (congrArg Prod.snd same))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
