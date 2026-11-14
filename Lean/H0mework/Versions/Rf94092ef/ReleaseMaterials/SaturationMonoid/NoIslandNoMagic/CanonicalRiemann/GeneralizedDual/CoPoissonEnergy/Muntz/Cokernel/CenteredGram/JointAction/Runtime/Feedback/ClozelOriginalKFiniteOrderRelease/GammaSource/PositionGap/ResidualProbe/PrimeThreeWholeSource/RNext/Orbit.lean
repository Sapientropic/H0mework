import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.RNext.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit

open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Install

namespace Family
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Packet)
end Family

namespace Code
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (code_base_value)
end Code

namespace Writer
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor (write)
end Writer

local notation "Word" => PairValue C.Value
local notation "total" => BoundaryNativeKAction.total
local notation "Packet" k => Family.Packet (W := Word) (X := C.Var) (s := ()) k
local notation "Cfg" k => A.Programme (PhysicalValue := L.Value Word k) (PhysicalVar := C.Var) (sort := ())

local instance groups (k : Nat) : ∀ slot, AddCommGroup (L.Value Word k slot) := L.groups Word k

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ j : Nat, observation.coordinate = -2 * (j+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "factory" => OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half
local notation "code" => Install.sourceCode observation nontrivial half
local notation "R₀" => OriginalKCombPhysicalAction.R observation nontrivial half

private def configurationAt {k : Nat} (p : Packet k) : Cfg k :=
  SF.cfg factory k p.2

private abbrev writeAt {k : Nat} (p : Packet k) :=
  Writer.write k (configurationAt observation nontrivial half p)

private def paidPacket {k : Nat} (p : Packet k) : Packet (k+1) :=
  let cfg := configurationAt observation nontrivial half p
  let write := writeAt observation nontrivial half p
  ⟨WB.born p.1 cfg write, Material.inventorySeed p.1 cfg write⟩

theorem code_total (k : Nat) (active : Env (L.Value Word k) C.Var) :
    total (k+1) ((CF.codeAt code k).eval (pairEnvironment active 0)) =
      R₀ (total k (active () ())) := by
  let computed := (CF.codeAt code k).eval (pairEnvironment active 0)
  have collapse := Code.code_base_value code k (pairEnvironment active 0)
  have input := Material.current_collapse k (active () ())
  calc
    _ = total 1 (CF.collapseValue k computed) := Material.total_collapse _ _
    _ = total 1 ((code).eval (fun target name => CF.collapseValue k (active target name, 0))) :=
      congrArg (total 1) collapse
    _ = R₀ (total 1 (CF.collapseValue k (active () (), 0))) :=
      Material.joint_total observation nontrivial half _
    _ = _ := congrArg R₀ input

variable (depth width start : Nat)
local notation "baseGrade" => Install.grade observation nontrivial half depth start + 1

attribute [local irreducible] Install.frame Install.grade

private def initialPacket : Packet baseGrade :=
  let f := Install.frame observation nontrivial half depth width start
  let cfg := Install.configuration observation nontrivial half depth width start
  let write := Install.write observation nontrivial half depth start
  ⟨Install.born observation nontrivial half depth width start, Material.inventorySeed f cfg write⟩

/-- Each continuation starts from the prior complete born and its actual scalar inventory. -/
def packet : (k : Nat) → Packet (baseGrade + k)
  | 0 => initialPacket observation nontrivial half depth width start
  | k+1 => paidPacket observation nontrivial half (packet k)

abbrev frameAt (k : Nat) := (packet observation nontrivial half depth width start k).1
abbrev cfgAt (k : Nat) : Cfg (baseGrade + k) :=
  configurationAt observation nontrivial half (packet observation nontrivial half depth width start k)
abbrev writerAt (k : Nat) := writeAt observation nontrivial half (packet observation nontrivial half depth width start k)
local notation "F" => frameAt observation nontrivial half depth width start
local notation "Q" => cfgAt observation nontrivial half depth width start
local notation "write" => writerAt observation nontrivial half depth width start

theorem initial_frame : F 0 = Install.born observation nontrivial half depth width start := rfl

theorem generated_frame (k : Nat) : F (k+1) = WB.born (F k) (Q k) (write k) := rfl

theorem seed_from_born (k : Nat) :
    (F k).inventory = some (packet observation nontrivial half depth width start k).2 := by
  cases k with
  | zero =>
    exact Material.inventorySeed_source
      (Install.frame observation nontrivial half depth width start)
      (Install.configuration observation nontrivial half depth width start)
      (Install.write observation nontrivial half depth start)
  | succ k =>
    exact Material.inventorySeed_source (F k) (Q k) (write k)

private theorem next_environment (k : Nat) :
    (S.next (F k) (Q k)).activeEnvironment = (F k).activeEnvironment := by
  cases k with
  | zero =>
    exact Material.born_next_environment
      (Install.frame observation nontrivial half depth width start)
      (Install.configuration observation nontrivial half depth width start)
      (Install.write observation nontrivial half depth start) (Q 0)
  | succ k =>
    exact Material.born_next_environment (F k) (Q k) (write k) (Q (k+1))

attribute [local irreducible] packet

theorem actual_payload (k : Nat) :
    (F (k+1)).activeEnvironment () () =
      (CF.codeAt code (baseGrade+k)).eval (pairEnvironment (F k).activeEnvironment 0) := by
  let result (environment : Env (L.Value Word (baseGrade+k)) C.Var) :=
    (CF.codeAt code (baseGrade+k)).eval (pairEnvironment environment 0)
  have written : (F (k+1)).activeEnvironment () () =
      WB.oldPaid (F k) (Q k) + WB.nativeValue (F k) (Q k) (write k) := by
    rw [generated_frame]
    exact congrArg (fun environment => environment () ())
      (E.active (WB.born_environment (F k) (Q k) (write k)))
  have calculated := AI.updated_total (baseGrade+k) (F k) code (SF.defaultFactory Word C.Var ())
    (packet observation nontrivial half depth width start k).2 (write k)
  exact written.trans
    (calculated.trans (congrArg result (next_environment observation nontrivial half depth width start k)))

def value (k : Nat) : BurnolL2 := total (baseGrade+k) ((F k).activeEnvironment () ())

theorem initial_value :
    value observation nontrivial half depth width start 0 =
      Install.value observation nontrivial half depth width start :=
  congrArg (fun f : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
      (Value := L.Value Word baseGrade) (Var := C.Var) (sort := ()) =>
      total baseGrade (f.activeEnvironment () ()))
    (initial_frame observation nontrivial half depth width start)

/-- The actual paid payload computes the original full R action at every generated birth. -/
theorem actual_R_step (k : Nat) :
    value observation nontrivial half depth width start (k+1) =
      R₀ (value observation nontrivial half depth width start k) :=
  (congrArg (total (baseGrade+k+1)) (actual_payload observation nontrivial half depth width start k)).trans
    (code_total observation nontrivial half (baseGrade+k) (F k).activeEnvironment)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
