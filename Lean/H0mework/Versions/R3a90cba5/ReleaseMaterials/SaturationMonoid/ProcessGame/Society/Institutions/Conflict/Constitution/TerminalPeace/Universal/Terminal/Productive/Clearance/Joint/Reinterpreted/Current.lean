import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Settlement
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Recipe
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Posting
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Reparation.Actual (ReceiptAnswers Script StateAt)
open Quantities.Execution (endAt)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

abbrev anchor (loss : Reparation.Actual.Occurrence seed community)
    (front : Script Party Good Port Technology Instrument) :=
  Occurrence.history loss ++ front

/-- The original stack is indexed by the native landing. Its active
material interpreter and stock advance on the same resident. -/
structure Current (loss : Reparation.Actual.Occurrence seed community)
    (front : Script Party Good Port Technology Instrument) where
  private mk ::
  ledger : StateAt seed community (endAt seed (anchor loss front))
  physical : Runtime.Native Party Good Port Technology Instrument
  programme : ProgrammeSource.Input Party Good Port Technology Instrument
  ordinal : Nat
  afterAnchor : (anchor loss front).length ≤ ordinal
  terms : FixedPoint.KeepsPublicTerms seed.native.input programme
  origins : ledger.stack.balances.map Prod.fst = Reparation.Actual.originalLosses seed community (anchor loss front)
  inherited : FixedPoint.OpenPeace.Network.InheritedCalculus ledger.world

variable (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (front : Script Party Good Port Technology Instrument)

def people : List Party := (ExposureGuard.bearers seed community (anchor loss front)).dedup

inductive EntranceIssue
  | rejected (reason : ProductionInputFailure (community := community) answers (Occurrence.history loss)
      (Occurrence.history loss) front)
  | pending (reason : ¬ ReadyEntry loss front)

local notation "Here" => endAt seed (anchor loss front)

/-- Opening reads the checked native prefix of this loss. The first
non-native action cannot take the place of an old outstanding head. -/
def enter : Except (EntranceIssue loss answers front) (Current loss front) :=
  match inspectInputs (community := community) answers (Occurrence.history loss) (Occurrence.history loss) front with
  | .inl reason => .error (.rejected reason)
  | .inr _ =>
    if ready : Ready Here ∧ ReviewAvailable Here then
      .ok ⟨Occurrence.reached answers loss front, (Here).state, seed.native.input, (anchor loss front).length,
        le_rfl, .refl _, Occurrence.reached_origins answers loss front,
        FixedPoint.OpenPeace.Network.inheritedReached loss answers front⟩
    else .error (.pending ready)

theorem enters_when_the_original_prefix_is_admitted
    (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front) :
    ∃ current, enter loss answers front = .ok current ∧
      current.ledger = Occurrence.reached answers loss front ∧
      current.physical = (Here).state ∧ current.programme = seed.native.input := by
  unfold enter
  split
  · rename_i reason _
    exact ((reason.refutes answers (Occurrence.history loss)) safe).elim
  · change Ready Here ∧ ReviewAvailable Here at ready
    rw [dif_pos ready]
    exact ⟨_, rfl, rfl, rfl, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
