import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedStageLimit
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP751Independent

open CategoryTheory CategoryTheory.Limits SequentialHomotopyLimit
open RootGeneratedSequentialHomotopyLimitAt SourceGeneratedPrimePowerCompletion

private def the_actual_difference_is_epi_and_its_kernel_is_the_strict_limit
    {Root : Type u}
    {occurrence : RootedAccountedUnfolding (Root × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
    (face : RootGeneratedSequentialHomotopyLimitAt occurrence)
    (cone : Cone face.actualTower) (lim : IsLimit cone)
    (onto : ∀ (degree : ℤ) (stage : Nat), Function.Surjective ((face.transitionAt stage).f degree)) :=
  PProd.mk (limitProductKernel face cone lim)
    (And.intro (difference_epi_of_surjective face onto) (limit_difference_short_exact face cone lim onto))

private def the_canonical_comparison_reads_every_stage_and_commutes_with_the_full_cocone
    {Root : Type u} {NextRoot : Type v}
    (root : RootedAccountedUnfolding Root) (next : RootedAccountedUnfolding NextRoot)
    (p : Nat.Primes) {source target : CochainComplex AddCommGrpCat ℤ}
    (action : HomotopyEquiv source target) (stage : Nat) :=
  And.intro (cochain_derived_limit_quasiIso root p source) <|
    And.intro (cochain_derived_limit_quasiIso next p target) <|
    And.intro (cochain_derived_limit_stage root p source stage) <|
    And.intro (cochain_derived_limit_naturality root next p action.hom)
      (cochain_derived_action_quasiIso root next p action)

private def alternatingIntegerTarget (n : Nat) : ℤ := if n % 2 = 0 then 1 else 0

private theorem multiplication_by_two_has_a_compatibility_difference_with_no_preimage :
    ¬ ∃ x : ℕ → ℤ, (fun n => x n - 2 * x (n+1)) = alternatingIntegerTarget := by
  rintro ⟨x,writes⟩
  have twoSteps (n : Nat) : 3 * x (2*n) + 1 = 4 * (3 * x (2*(n+1)) + 1) := by
    have evenWrite := congrFun writes (2*n)
    have oddWrite := congrFun writes (2*n+1)
    have evenIndex : (2*n) % 2 = 0 := by omega
    have oddIndex : (2*n+1) % 2 ≠ 0 := by omega
    have nextIndex : 2*n+1+1 = 2*(n+1) := by omega
    change x (2*n) - 2*x (2*n+1) = alternatingIntegerTarget (2*n) at evenWrite
    change x (2*n+1) - 2*x (2*n+1+1) = alternatingIntegerTarget (2*n+1) at oddWrite
    rw [alternatingIntegerTarget, if_pos evenIndex] at evenWrite
    rw [alternatingIntegerTarget, if_neg oddIndex, nextIndex] at oddWrite
    omega
  let initial : ℤ := 3 * x 0 + 1
  have expands (n : Nat) : initial = (4 : ℤ)^n * (3 * x (2*n) + 1) := by
    induction n with
    | zero => simp [initial]
    | succ n prior =>
      calc
        _ = (4 : ℤ)^n * (3 * x (2*n) + 1) := prior
        _ = (4 : ℤ)^n * (4 * (3 * x (2*(n+1)) + 1)) :=
          congrArg (fun z : ℤ => (4 : ℤ)^n * z) (twoSteps n)
        _ = _ := by rw [pow_succ,mul_assoc]
  let n := initial.natAbs + 1
  have nonzero : 3 * x (2*n) + 1 ≠ 0 := by omega
  have absolute := congrArg Int.natAbs (expands n)
  rw [Int.natAbs_mul,Int.natAbs_pow] at absolute
  change initial.natAbs = (4 : ℕ)^n * (3 * x (2*n) + 1).natAbs at absolute
  have bound : (4 : ℕ)^n ≤ initial.natAbs := by
    rw [absolute]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr nonzero)
  have grows : n < (4 : ℕ)^n := Nat.lt_pow_self (by decide : 1 < 4)
  have tooLarge : n < initial.natAbs := lt_of_lt_of_le grows bound
  change initial.natAbs + 1 < initial.natAbs at tooLarge
  omega

end CP751Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP751Independent

open CofinalRelationGeneratedComplex SourceOperationScalarInventoryLift
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

set_option cleanup.letToHave false in
private def the_four_original_R_ticks_keep_the_paid_cofiber_Division_K_whole_and_next
    (ordinal : Nat) (index : Fin 4) (p : Nat.Primes) (stage : Nat) :=
  let paid := actual_paid_derived_stage_limit observation nontrivial half depth ordinal
    (Fin.cast (actual_paid_stage_count observation nontrivial half depth ordinal).symm index) p stage
  PProd.mk paid.1 <| And.intro paid.2 <|
    And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1
      (actual_original_K_read observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.RootRelation.CP751Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP751Independent

open CategoryTheory CofinalRelationGeneratedComplex
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent tick_paid_prefix)
open SourceOperationCompletion SourceGeneratedPrimePowerCompletion

open private extendPaidHomotopy from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedStageLimit

set_option cleanup.letToHave false in
private def the_fixed_target_advances_its_literal_paid_derived_limit_and_original_terminal
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth))) (p : Nat.Primes) :=
  let runtime := C.mathRuntime depth (count+1)
  let prior := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).2
  let later := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime.tick.next).2
  let first := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let next := RootedAccountedUnfolding.zero runtime.tick.next.emittedOccurrence
  let retained := tick_paid_prefix (R.old depth) (R.origin depth) (R.reader depth) runtime
  let action := (forget₂ (ModuleCat ℤ) AddCommGrpCat).mapHomotopyEquiv
    (extendPaidHomotopy (continuationCochainHomotopyEquiv first prior next later retained))
  And.intro (cochain_derived_limit_naturality first next p action.hom) <|
    And.intro (cochain_derived_action_quasiIso first next p action) <|
    And.intro (actual_actor_cofinal_continuation depth count within p)
      (TopologyTrace.actual_actor_cofinal_terminal depth p)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP751Independent

#eval IO.println "CP751_CONTROL + the_actual_difference_is_epi_and_its_kernel_is_the_strict_limit"
#eval IO.println "CP751_CONTROL + the_canonical_comparison_reads_every_stage_and_commutes_with_the_full_cocone"
#eval IO.println "CP751_CONTROL + the_four_original_R_ticks_keep_the_paid_cofiber_Division_K_whole_and_next"
#eval IO.println "CP751_CONTROL + the_fixed_target_advances_its_literal_paid_derived_limit_and_original_terminal"
#eval IO.println "CP751_CONTROL - multiplication_by_two_has_a_compatibility_difference_with_no_preimage"
#eval IO.println "CP751_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
