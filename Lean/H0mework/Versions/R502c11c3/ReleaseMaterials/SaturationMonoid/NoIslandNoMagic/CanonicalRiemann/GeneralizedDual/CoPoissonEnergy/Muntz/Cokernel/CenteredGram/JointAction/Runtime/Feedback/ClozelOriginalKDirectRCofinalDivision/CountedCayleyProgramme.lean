import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyInverse
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Source

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 190000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyProgramme

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open SourceGeneratedActionObservationHistory.ContractiveRecovery
open RootGeneratedDebtActivationJointSource.OwnerFree

namespace Eval
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
  (value value_source trace target_expression paid_history original_material relation_boundary relation_cochain
    updated_inverse_fibre)
end Eval

local notation "V" => CountedCellHistory.CellValue
local notation "X" => CountedCellHistory.Var
local notation "Cayley" => sourceCayley

/-- Advance the running sum and keep the same decoded successor as its drive. -/
private def accumulate (coord : BurnolCompletedMellinCoordinate) (stage : Nat) : V () →+ V () where
  toFun x := ![Cayley coord (x 0)+(stage : ℂ) • CountedCayleyInverse.drive coord (x 1), x 1]
  map_zero' := by
    funext i
    fin_cases i <;> simp [CountedCayleyInverse.drive]
  map_add' := by
    intro x y
    funext i
    fin_cases i
    · change Cayley coord (x 0+y 0)+(stage : ℂ) • CountedCayleyInverse.drive coord (x 1+y 1) =
        Cayley coord (x 0)+(stage : ℂ) • CountedCayleyInverse.drive coord (x 1)+
          (Cayley coord (y 0)+(stage : ℂ) • CountedCayleyInverse.drive coord (y 1))
      rw [map_add]
      simp only [CountedCayleyInverse.drive, smul_add]
      abel
    · rfl

private def finish (n : Nat) : V () →+ V () where
  toFun x := ![(((n+1 : Nat) : ℂ)⁻¹) • x 0, x 1]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp [smul_add]

private def tally (coord : BurnolCompletedMellinCoordinate) (seed : Expr V X ()) : Nat → Expr V X ()
  | 0 => seed
  | n+1 => .linear (accumulate coord (n+1)) (tally coord seed n)

private theorem tally_value (coord : BurnolCompletedMellinCoordinate) (seed : Expr V X ())
    (environment : Env V X) (value : BurnolL2) (initial : seed.eval environment = ![0,value])
    (n : Nat) :
    ((tally coord seed n).eval environment) 0 =
        birkhoffSum (step (Cayley coord) (CountedCayleyInverse.drive coord value)) id (n+1) 0 ∧
      ((tally coord seed n).eval environment) 1 = value := by
  induction n with
  | zero =>
      change (seed.eval environment) 0 = _ ∧ (seed.eval environment) 1 = _
      rw [initial]
      exact ⟨(birkhoffSum_one (step (Cayley coord) (CountedCayleyInverse.drive coord value)) id 0).symm, rfl⟩
  | succ n previous =>
      constructor
      · change Cayley coord (((tally coord seed n).eval environment) 0) +
            ((n+1 : Nat) : ℂ) • CountedCayleyInverse.drive coord (((tally coord seed n).eval environment) 1) = _
        rw [previous.1, previous.2]
        exact (driven_sum_succ (Cayley coord) _ n).symm
      · exact previous.2

private theorem tally_charge (coord : BurnolCompletedMellinCoordinate) (seed : Expr V X ()) (n : Nat) :
    remaining (tally coord seed n) = remaining seed+n := by
  induction n with
  | zero => rfl
  | succ n previous =>
      rw [tally, remaining, previous, Nat.add_assoc]

private def tallyReceipt (coord : BurnolCompletedMellinCoordinate) (seed : Expr V X ())
    {environment : Env V X} : (n : Nat) → {value : V ()} →
    (actual : Trace environment (tally coord seed n) (.const value)) → Trace.SourceReceipt actual seed
  | 0, _, actual => ⟨_,actual,.refl _⟩
  | n+1, _, actual =>
    let last := actual.splitLinear
    let earlier := tallyReceipt coord seed n last.trace
    ⟨earlier.value, earlier.trace, .linear last earlier.retained⟩

private def decode (N : Nat) (positive : 0 < N) : V () →+ V () where
  toFun x := ![0, CountedCellInverse.recoverOutput N positive (x 0) (x 1)]
  map_zero' := by
    funext i
    fin_cases i
    · rfl
    · change CountedCellInverse.recoverOutput N positive 0 0 = 0
      simp only [CountedCellInverse.recoverOutput, sub_self, map_zero]
  map_add' := by
    intro x y
    funext i
    fin_cases i
    · exact (zero_add (0 : BurnolL2)).symm
    · change CountedCellInverse.recoverOutput N positive (x 0+y 0) (x 1+y 1) =
        CountedCellInverse.recoverOutput N positive (x 0) (x 1) +
          CountedCellInverse.recoverOutput N positive (y 0) (y 1)
      rw [CountedCellInverse.recoverOutput, CountedCellInverse.recoverOutput,
        CountedCellInverse.recoverOutput, add_sub_add_comm, map_add]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "authority" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "origin" => CountedFiniteNative.current observation nontrivial half depth ordinal
local notation "cell" => CountedCellHistory.reader observation nontrivial half depth ordinal
local notation "counts" => CountedCellHistory.count observation nontrivial half depth ordinal

/-- The adjacently counted bank is a child of the finite decoder, keeping its actual operations. -/
def readBank (N : Nat) (positive : 0 < N)
    (actual : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := V) (Var := X) (sort := ()) :=
  let material := cell N actual
  ⟨material.environment, .linear (decode N positive) material.expression⟩

def recoveredBank (N : Nat) (positive : 0 < N) :=
  Eval.value authority origin (readBank observation nontrivial half depth ordinal N positive)

theorem recovered_bank_source (N : Nat) (positive : 0 < N) :
    recoveredBank observation nontrivial half depth ordinal N positive =
      ![0, (cellIncidence observation nontrivial half depth ordinal N positive).2] := by
  change Eval.value authority origin (readBank observation nontrivial half depth ordinal N positive) = _
  rw [Eval.value_source]
  have bank := Eval.value_source authority origin (cell N)
  change (counts N) = (CountedCellHistory.cellCode N).eval
    ((cell N ((authority).emitted origin)).environment) at bank
  change decode N positive ((CountedCellHistory.cellCode N).eval
    ((cell N ((authority).emitted origin)).environment)) = _
  rw [← bank]
  rfl

/-- The root receives the full counted bank; each subsequent step pays one Cayley action and the drive. -/
def reader (N : Nat) (positive : 0 < N) (n : Nat)
    (actual : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := V) (Var := X) (sort := ()) :=
  let material := readBank observation nontrivial half depth ordinal N positive actual
  ⟨material.environment, .linear (finish n) (tally coord material.expression n)⟩

def output (N : Nat) (positive : 0 < N) (n : Nat) : BurnolL2 × BurnolL2 :=
  let result := Eval.value authority origin (reader observation nontrivial half depth ordinal N positive n)
  (result 0, result 1)

theorem output_source (N : Nat) (positive : 0 < N) (n : Nat) :
    let y := (cellIncidence observation nontrivial half depth ordinal N positive).2
    output observation nontrivial half depth ordinal N positive n =
      (CountedCayleyInverse.entrance coord y n,y) := by
  let bank := readBank observation nontrivial half depth ordinal N positive
  let programme := reader observation nontrivial half depth ordinal N positive n
  let y := (cellIncidence observation nontrivial half depth ordinal N positive).2
  have bankSource : (bank ((authority).emitted origin)).expression.eval
      (bank ((authority).emitted origin)).environment = ![0,y] :=
    (Eval.value_source authority origin bank).symm.trans
      (recovered_bank_source observation nontrivial half depth ordinal N positive)
  have summed := tally_value coord _ _ y bankSource n
  have executed : Eval.value authority origin programme = ![CountedCayleyInverse.entrance coord y n,y] := by
    rw [Eval.value_source]
    funext index
    fin_cases index
    · change (((n+1 : Nat) : ℂ)⁻¹) •
          ((tally coord (bank ((authority).emitted origin)).expression n).eval
            (bank ((authority).emitted origin)).environment) 0 =
        CountedCayleyInverse.entrance coord y n
      exact congrArg (fun field : BurnolL2 => (((n+1 : Nat) : ℂ)⁻¹) • field) summed.1
    · exact summed.2
  exact congrArg (fun data : V () => (data 0, data 1)) executed

local notation "sourceReader" => reader observation nontrivial half depth ordinal

/-- Fix the actual parent terminal before descending to its paid count-bank child. -/
def terminalTrace (N : Nat) (positive : 0 < N) (n : Nat) :
    Trace ((sourceReader N positive n) ((authority).emitted origin)).environment
      ((sourceReader N positive n) ((authority).emitted origin)).expression
      (.const (Eval.value authority origin (sourceReader N positive n))) := by
  rw [← Eval.target_expression authority origin (sourceReader N positive n)]
  exact Eval.trace authority origin (sourceReader N positive n)

def countChild (N : Nat) (positive : 0 < N) (n : Nat) :
    Trace.SourceReceipt (terminalTrace observation nontrivial half depth ordinal N positive n)
      (CountedCellHistory.cellCode N) := by
  let seed := readBank observation nontrivial half depth ordinal N positive ((authority).emitted origin)
  let outer := (terminalTrace observation nontrivial half depth ordinal N positive n).splitLinear
  let cut := tallyReceipt coord seed.expression n outer.trace
  let bank := cut.trace.splitLinear
  exact ⟨bank.input, bank.trace, .linear outer (cut.retained.trans (.linear bank (.refl _)))⟩

theorem count_child_source (N : Nat) (positive : 0 < N) (n : Nat) :
    let child := countChild observation nontrivial half depth ordinal N positive n
    child.value = counts N ∧ child.trace.length = 8 := by
  let child := countChild observation nontrivial half depth ordinal N positive n
  have eval := Eval.value_source authority origin (cell N)
  have paid := CountedCellHistory.count_paid_steps observation nontrivial half depth ordinal N
  have sourceCost : remaining (CountedCellHistory.cellCode N) = 8 :=
    (Eval.paid_history authority origin (cell N)).symm.trans paid
  exact ⟨child.trace.sound.symm.trans eval.symm, child.trace.length_to_const.trans sourceCost⟩

theorem paid_steps (N : Nat) (positive : 0 < N) (n : Nat) :
    (Eval.trace authority origin (sourceReader N positive n)).length = 10+n := by
  have countPaid := CountedCellHistory.count_paid_steps observation nontrivial half depth ordinal N
  have sourceCost : remaining (CountedCellHistory.cellCode N) = 8 :=
    (Eval.paid_history authority origin (cell N)).symm.trans countPaid
  rw [Eval.paid_history]
  change remaining (tally coord (.linear (decode N positive) (CountedCellHistory.cellCode N)) n)+1 = _
  rw [tally_charge, remaining, sourceCost]
  omega

end CountedCayleyProgramme
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
