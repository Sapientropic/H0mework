import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyRelations

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 170000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyIncrement

open BurnolPhysicalState Filter RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open RootGeneratedDebtActivationJointSource.OwnerFree
open scoped InnerProductSpace Topology

open private tally finish decode from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyProgramme

open private literal_R from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity

local notation "V" => CountedCellHistory.CellValue
local notation "X" => CountedCellHistory.Var
local notation "Resolvent" => burnolDirectRightResolventCLM

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "authority" "[" j "]" => CountedFiniteNative.root observation nontrivial half depth j
local notation "origin" "[" j "]" => CountedFiniteNative.current observation nontrivial half depth j
local notation "readIn" "[" j "]" => CountedCayleyProgramme.reader observation nontrivial half depth j
local notation "nextRaw" "[" j "]" => D.raw observation nontrivial half depth (j+1+1)
local notation "out" "[" j "]" => CountedCayleyProgramme.output observation nontrivial half depth j

/-- The environment change is read from the next literal Division, using its own original occurrence. -/
def increment (N : Nat) (positive : 0 < N) (n : Nat) : Env V X :=
  (raw authority[ordinal+1] origin[ordinal+1] (readIn[ordinal+1] N positive n)).environment -
    (raw authority[ordinal] origin[ordinal] (readIn[ordinal] N positive n)).environment

private theorem common_expression (N : Nat) (positive : 0 < N) (n : Nat) :
    (raw authority[ordinal+1] origin[ordinal+1] (readIn[ordinal+1] N positive n)).expression =
      (raw authority[ordinal] origin[ordinal] (readIn[ordinal] N positive n)).expression := by
  let code : Expr V X () :=
    .linear (finish n) (tally coord (.linear (decode N positive) (CountedCellHistory.cellCode N)) n)
  have born : (raw authority[ordinal+1] origin[ordinal+1] (readIn[ordinal+1] N positive n)).expression = code := rfl
  have old : (raw authority[ordinal] origin[ordinal] (readIn[ordinal] N positive n)).expression = code := rfl
  exact born.trans old.symm

/-- The old expression is re-evaluated under the actual born source of the adjacent Division. -/
theorem actual_effect (N : Nat) (positive : 0 < N) (n : Nat) :
    let old := raw authority[ordinal] origin[ordinal] (readIn[ordinal] N positive n)
    let effect := old.expression.effect old.environment (increment observation nontrivial half depth ordinal N positive n)
    (effect 0,effect 1) = out[ordinal+1] N positive n-out[ordinal] N positive n := by
  let old := raw authority[ordinal] origin[ordinal] (readIn[ordinal] N positive n)
  let born := raw authority[ordinal+1] origin[ordinal+1] (readIn[ordinal+1] N positive n)
  let changeBy := increment observation nontrivial half depth ordinal N positive n
  have input : old.environment + changeBy = born.environment := add_sub_cancel _ _
  have syntaxSame : born.expression = old.expression :=
    common_expression observation nontrivial half depth ordinal N positive n
  have oldValue : @Eq (V ()) (CountedCayleyProgramme.Eval.value
      authority[ordinal] origin[ordinal] (readIn[ordinal] N positive n))
      (old.expression.eval old.environment) :=
    CountedCayleyProgramme.Eval.value_source authority[ordinal] origin[ordinal] (readIn[ordinal] N positive n)
  have bornValue : @Eq (V ()) (CountedCayleyProgramme.Eval.value
      authority[ordinal+1] origin[ordinal+1] (readIn[ordinal+1] N positive n))
      (born.expression.eval born.environment) :=
    CountedCayleyProgramme.Eval.value_source authority[ordinal+1] origin[ordinal+1] (readIn[ordinal+1] N positive n)
  have arrived : old.expression.eval (old.environment+changeBy) = born.expression.eval born.environment :=
    (congrArg old.expression.eval input).trans
      (congrArg (fun code : Expr V X () => code.eval born.environment) syntaxSame.symm)
  have effectSource : old.expression.effect old.environment changeBy =
      born.expression.eval born.environment-old.expression.eval old.environment := by
    have update := (Expr.eval_update old.expression old.environment changeBy).symm.trans arrived
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans update)
  have changed : @Eq (V ()) (old.expression.effect old.environment changeBy)
      (CountedCayleyProgramme.Eval.value authority[ordinal+1] origin[ordinal+1] (readIn[ordinal+1] N positive n) -
        CountedCayleyProgramme.Eval.value authority[ordinal] origin[ordinal] (readIn[ordinal] N positive n)) :=
    effectSource.trans (congrArg₂ (· - ·) bornValue.symm oldValue.symm)
  exact congrArg (fun values : V () => (values 0, values 1)) changed

/-- The same update is the original R increment on both finite readout slots. -/
theorem actual_resolvent_effect (N : Nat) (positive : 0 < N) (n : Nat) :
    let current := out[ordinal] N positive n
    out[ordinal+1] N positive n-current =
      (Resolvent coord current.1-current.1,Resolvent coord current.2-current.2) := by
  have old := CountedCayleyWriteback.finite_source observation nontrivial half depth ordinal N positive n
  have born := CountedCayleyWriteback.finite_source observation nontrivial half depth (ordinal+1) N positive n
  have sourceNext : @Eq BurnolL2 (nextRaw[ordinal+1]) (Resolvent coord (nextRaw[ordinal])) :=
    literal_R observation nontrivial half depth (ordinal+1+1)
  have commute : CountedCayleyInverse.entrance coord (Resolvent coord (nextRaw[ordinal])) n =
      Resolvent coord (CountedCayleyInverse.entrance coord (nextRaw[ordinal]) n) := by
    let y := nextRaw[ordinal]
    let A := sourceCayley coord
    let r := Resolvent coord
    have actions (x : BurnolL2) : r (A x) = A (r x) := by
      change r (sourceCayley coord x) = sourceCayley coord (r x)
      rw [sourceCayley_apply, sourceCayley_apply]
      change r (x+(sourceDamping coord : ℂ) • r x) = r x+(sourceDamping coord : ℂ) • r (r x)
      rw [map_add,map_smul]
    have drive : r (CountedCayleyInverse.drive coord y) = CountedCayleyInverse.drive coord (r y) := by
      rw [CountedCayleyInverse.drive, CountedCayleyInverse.drive, map_smul]
    have flow : Function.Semiconj r
        (SourceGeneratedActionObservationHistory.ContractiveRecovery.step A (CountedCayleyInverse.drive coord y))
        (SourceGeneratedActionObservationHistory.ContractiveRecovery.step A (CountedCayleyInverse.drive coord (r y))) := by
      intro x
      change r (A x+CountedCayleyInverse.drive coord y) = A (r x)+CountedCayleyInverse.drive coord (r y)
      rw [map_add,actions,drive]
    change CountedCayleyInverse.entrance coord (r y) n = r (CountedCayleyInverse.entrance coord y n)
    symm
    unfold CountedCayleyInverse.entrance SourceGeneratedActionObservationHistory.ContractiveRecovery.approximate
      birkhoffAverage birkhoffSum
    rw [map_smul,map_sum]
    apply congrArg (fun value : BurnolL2 => (((n+1 : Nat) : ℂ)⁻¹) • value)
    apply Finset.sum_congr rfl
    intro j _
    exact (flow.iterate_right j 0).trans (congrArg _ (map_zero r))
  let step := fun pair : BurnolL2 × BurnolL2 => (Resolvent coord pair.1, Resolvent coord pair.2)
  have nextRead : @Eq (BurnolL2 × BurnolL2) (out[ordinal+1] N positive n) (step (out[ordinal] N positive n)) := by
    have acted : @Eq (BurnolL2 × BurnolL2) (out[ordinal+1] N positive n)
        (CountedCayleyInverse.entrance coord (Resolvent coord (nextRaw[ordinal])) n, Resolvent coord (nextRaw[ordinal])) :=
      born.trans (congrArg (fun y : BurnolL2 => (CountedCayleyInverse.entrance coord y n,y)) sourceNext)
    have pair : @Eq (BurnolL2 × BurnolL2)
        (CountedCayleyInverse.entrance coord (Resolvent coord (nextRaw[ordinal])) n, Resolvent coord (nextRaw[ordinal]))
        (step (CountedCayleyInverse.entrance coord (nextRaw[ordinal]) n, nextRaw[ordinal])) :=
      Prod.ext commute rfl
    exact acted.trans (pair.trans (congrArg step old.symm))
  exact congrArg (fun pair : BurnolL2 × BurnolL2 => pair-out[ordinal] N positive n) nextRead

end CountedCayleyIncrement
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
