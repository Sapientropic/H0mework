import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedDivision

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedDivisionTrace

open BurnolPhysicalState Filter SourceOperationEffects SourceOperationScalarInventoryLift
open scoped Topology

namespace Finite
export BoundaryCountedDivision (jointCode jointEnvironment jointWord decode actual_division)
end Finite

namespace NativeCalc
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (source_value)
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry (query state resultFace)
end NativeCalc

open private base currentField current_source frame configuration
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedProgramSource

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "old" => base observation nontrivial half depth
local notation "packetField" => currentField observation nontrivial half depth
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "invisible" => OriginalKCombCofinalPaAction.invisible
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "response" => OriginalKDirectRCofinalDivision.sourceResponse observation nontrivial half depth

private def reader (ordinal n : Nat) {now : _}
    (_ : (old ordinal).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) :
    NativeCalc.Raw (Value := PairValue BoundaryCountedProgramTrace.Value)
      (Var := BoundaryCountedProgramTrace.Var) (sort := .orbit) :=
  ⟨Finite.jointEnvironment (E (packetField ordinal)) (invisible (packetField ordinal)), Finite.jointCode c n⟩

local notation "readerAt" => reader observation nontrivial half depth

def request (ordinal n : Nat) :=
  NativeCalc.query (old ordinal) (readerAt ordinal n)
    (BoundaryCountedProgramSource.Read.query
      (frame observation nontrivial half depth ordinal) (configuration observation nontrivial half depth ordinal))

def inquiry (ordinal n : Nat) := NativeCalc.state (old ordinal) (readerAt ordinal n)

def result (ordinal n : Nat) := (NativeCalc.resultFace (old ordinal) (readerAt ordinal n)).rootRead

def fields (ordinal n : Nat) : BurnolL2 × BurnolL2 :=
  Finite.decode (result observation nontrivial half depth ordinal n).2.2.1

theorem fields_source (ordinal n : Nat) :
    fields observation nontrivial half depth ordinal n =
      Finite.jointWord c n (pa (ordinal+1) : BurnolL2) (invisible (raw (ordinal+1))) := by
  have produced := NativeCalc.source_value (old ordinal).root.toAuthoritativeRoot (readerAt ordinal n)
    ((old ordinal).root.emitted (old ordinal).visit.current)
  have read := congrArg Finite.decode produced
  change fields observation nontrivial half depth ordinal n =
    Finite.jointWord c n (E (packetField ordinal)) (invisible (packetField ordinal)) at read
  rw [current_source observation nontrivial half depth ordinal] at read
  exact read

theorem original_ledger (ordinal n : Nat) :
    (inquiry observation nontrivial half depth ordinal n).root.toAuthoritativeRoot.toLedgerRoot =
      (old ordinal).root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem original_visit (ordinal n : Nat) :
    HEq (inquiry observation nontrivial half depth ordinal n).visit (old ordinal).visit := HEq.rfl

/-- The same occurrence's paired finite trace recovers the original Division limits before recombining. -/
theorem actual_fields (ordinal : Nat) :
    let f := fields observation nontrivial half depth ordinal
    (∀ n : Nat, (f n).1 ∈ locallyConstantFace burnolUnscaledCommonGapRadius) ∧
    Tendsto f atTop (𝓝 ((response (ordinal+1) : BurnolL2), OriginalKCombPhysicalAction.R observation nontrivial half
      (invisible (raw (ordinal+1))))) ∧
    Tendsto (fun n : Nat => (f n).1+(f n).2) atTop (𝓝 (raw (ordinal+2))) := by
  have source : fields observation nontrivial half depth ordinal =
      fun n => Finite.jointWord c n (pa (ordinal+1) : BurnolL2) (invisible (raw (ordinal+1))) :=
    funext (fields_source observation nontrivial half depth ordinal)
  dsimp only
  rw [source]
  exact Finite.actual_division observation nontrivial half depth (ordinal+1)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedDivisionTrace
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
