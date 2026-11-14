import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedProgramTrace
import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.OwnerFree.Installation.Inquiry

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedProgramSource

open BurnolPhysicalState SourceOperationEffects SourceOperationExecution RootInquiryCompletion
open SourceOperationScalarInventoryLift

namespace Read
export ActualCofinalRootResidualConsumer (source selected installed generatedCurrent consume)
export ActualCofinalRootResidualConsumer.ST (state)
export ActualCofinalRootResidualConsumer.R (query)
end Read

namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (source_value source_history)
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry (resultFace)
end Calc

namespace Word
export BoundaryCountedProgramTrace (Value Var environment expression expression_eval expression_budget)
end Word

open private countFor meshFor lengthFor from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFiniteFlow
open private packet_whole_at from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit
open private nativeLanguage from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

private abbrev sourcePacket (ordinal : Nat) := Read.source factory initial cfg language (ordinal+1)

private abbrev currentField (ordinal : Nat) := PacketFit.packetWhole
  (sourcePacket observation nontrivial half depth ordinal)

private theorem current_source (ordinal : Nat) :
    currentField observation nontrivial half depth ordinal = raw (ordinal+1) := by
  change PacketFit.packetWhole (Native.packet observation nontrivial half depth ordinal) = _
  exact (packet_whole_at observation nontrivial half depth ordinal).trans
    (Native.calculated_target_raw_successor observation nontrivial half depth ordinal)

private abbrev frame (ordinal : Nat) := Read.selected factory initial cfg language (ordinal+1)
private abbrev configuration (ordinal : Nat) := Read.installed factory initial cfg language (ordinal+1)

private abbrev base (ordinal : Nat) := Read.state
  (frame observation nontrivial half depth ordinal) (configuration observation nontrivial half depth ordinal)

local notation "old" => base observation nontrivial half depth
local notation "packetField" => currentField observation nontrivial half depth

private abbrev count (ordinal : Nat) (tolerance : ℝ) := countFor c (raw ordinal) tolerance
private abbrev mesh (ordinal : Nat) (tolerance : ℝ) := meshFor c (packetField ordinal) tolerance
private abbrev steps (ordinal : Nat) (tolerance : ℝ) :=
  lengthFor c (packetField ordinal) (count observation nontrivial half depth ordinal tolerance) tolerance

/-- The registered source is the original actual packet field and the generated finite word. -/
private def reader (ordinal : Nat) (tolerance : ℝ) {now : _}
    (_ : (old ordinal).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) :
    Calc.Raw (Value := Word.Value) (Var := Word.Var) (sort := .orbit) :=
  ⟨Word.environment (packetField ordinal),
    Word.expression ((c).value/2) (count observation nontrivial half depth ordinal tolerance)
      (mesh observation nontrivial half depth ordinal tolerance)
      (steps observation nontrivial half depth ordinal tolerance)⟩

local notation "readerAt" => reader observation nontrivial half depth

/-- Use the existing inquiry installation on the exact original stock occurrence. -/
def request (ordinal : Nat) (tolerance : ℝ) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.query
    (old ordinal) (readerAt ordinal tolerance)
    (Read.query (frame observation nontrivial half depth ordinal) (configuration observation nontrivial half depth ordinal))

def inquiry (ordinal : Nat) (tolerance : ℝ) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.state
    (old ordinal) (readerAt ordinal tolerance)

def result (ordinal : Nat) (tolerance : ℝ) :=
  (Calc.resultFace (old ordinal) (readerAt ordinal tolerance)).rootRead

/-- The math inquiry and original compiler have the identical ledger root and temporal visit. -/
theorem original_ledger (ordinal : Nat) (tolerance : ℝ) :
    (inquiry observation nontrivial half depth ordinal tolerance).root.toAuthoritativeRoot.toLedgerRoot =
      (old ordinal).root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem original_visit (ordinal : Nat) (tolerance : ℝ) :
    HEq (inquiry observation nontrivial half depth ordinal tolerance).visit (old ordinal).visit := HEq.rfl

def field (ordinal : Nat) (tolerance : ℝ) : BurnolL2 :=
  -((result observation nontrivial half depth ordinal tolerance).2.2.1).2.1

/-- The actual paid stock preserves the original input and clears the same cell accumulator. -/
theorem generated_stock (ordinal : Nat) (tolerance : ℝ) :
    (result observation nontrivial half depth ordinal tolerance).2.2.1 =
      (packetField ordinal, -(BoundaryCountedFiniteFlow.program c (raw ordinal) (packetField ordinal) tolerance), 0) := by
  have actual := Calc.source_value (old ordinal).root.toAuthoritativeRoot (readerAt ordinal tolerance)
    ((old ordinal).root.emitted (old ordinal).visit.current)
  have finite := Word.expression_eval ((c).value/2) (count observation nontrivial half depth ordinal tolerance)
    (mesh observation nontrivial half depth ordinal tolerance) (steps observation nontrivial half depth ordinal tolerance)
    (packetField ordinal)
  have proof := actual.trans finite
  change (result observation nontrivial half depth ordinal tolerance).2.2.1 = _ at proof
  simpa only [BoundaryCountedFiniteFlow.program, neg_neg] using proof

/-- The native trace counts the actual mesh letters and cell closes. -/
theorem generated_budget (ordinal : Nat) (tolerance : ℝ) :
    (result observation nontrivial half depth ordinal tolerance).2.1.2.length =
      steps observation nontrivial half depth ordinal tolerance *
        (mesh observation nontrivial half depth ordinal tolerance+1)+2 := by
  have actual := Calc.source_history (old ordinal).root.toAuthoritativeRoot (readerAt ordinal tolerance)
    ((old ordinal).root.emitted (old ordinal).visit.current)
  exact actual.trans (Word.expression_budget _ _ _ _)

theorem actual_accuracy (ordinal : Nat) (tolerance : ℝ) (positive : 0 < tolerance) :
    ‖field observation nontrivial half depth ordinal tolerance - raw (ordinal+2)‖ < tolerance := by
  have stock := generated_stock observation nontrivial half depth ordinal tolerance
  have read := congrArg (fun state : BoundaryCountedProgramTrace.Stock => -state.2.1) stock
  change field observation nontrivial half depth ordinal tolerance =
    -(-(BoundaryCountedFiniteFlow.program c (raw ordinal) (packetField ordinal) tolerance)) at read
  rw [read, neg_neg, current_source]
  exact BoundaryCountedFiniteFlow.actual_accuracy observation nontrivial half depth ordinal tolerance positive

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedProgramSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
