import H0mework.Realization.Integral.CharacterExact
import H0mework.Realization.Operations.RuntimePrefix
import H0mework.Arithmetic.FockDynamics.RootRuntime
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! The original runtime generates a torsion field point retained by the faithful
character image and missed by every integer-valued linear stage observation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCharacter.Controls

open SourceOperationEffects SourceOperationScalarRelations SourceOperationRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

abbrev Value : Unit → Type := fun _ => ZMod 2
abbrev Var : Unit → Type := fun _ => Unit

def readMaterial (state : process.State) : ℤ := state

def environment : ℤ →+ Env Value Var where
  toFun n := fun _ _ => (n : ZMod 2)
  map_zero' := by ext _ _; simp
  map_add' := by intro a b; ext _ _; simp

def word : FormalCarrier ℤ Value Var () := Finsupp.single (.var ()) 1

def field : completion (R := ℤ) (s := ()) readMaterial environment (runtimeAt 0) :=
  (completionMap readMaterial environment (runtimeAt 0)).hom word

theorem seed_completion_read :
    stageRead readMaterial environment (runtimeAt 0) 0 field 0 = (0, 1) := by
  rw [field, completion_source_to_actual_stage]
  change updateInventory (R := ℤ) (environment 0) (environment 1) word = (0, 1)
  norm_num [updateInventory, evaluation, effectEvaluator, environment, word, Expr.eval, Expr.effect]

theorem character_preserves_actual_seed :
    field ≠ 0 ∧
      SourceGeneratedScalarCharacterExact.canonicalMap ℤ _ field ≠ 0 ∧
      let runtime := runtimeAt 0
      let stage := (materialHistory runtime 0).stageAt 0
      stageRead readMaterial environment runtime 0 field 0 = (0, 1) ∧
        stage.activated = runtime.tick ∧
        stage.activated.generated.occurrence =
            runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
              runtime.current.visit.current ∧
          HEq stage.wholeLedgerWriteBack
            (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
              runtime.current.visit.current) ∧
          stage.next.current = stage.activated.nextCurrent := by
  have nonzero : field ≠ 0 := by
    intro killed
    have read := seed_completion_read
    rw [killed, map_zero] at read
    exact zero_ne_one (congrArg Prod.snd read)
  have characterNonzero : SourceGeneratedScalarCharacterExact.canonicalMap ℤ _ field ≠ 0 := by
    intro killed
    apply nonzero
    exact SourceGeneratedScalarCharacterExact.canonicalMap_injective ℤ _
      (killed.trans (map_zero _).symm)
  exact ⟨nonzero, characterNonzero, seed_completion_read, rfl,
    ((materialHistory (runtimeAt 0) 0).stageAt 0).factorizes.2⟩

/-- This observer shape loses all torsion pairs, including the actual `(0, 1)`. -/
theorem integer_scalar_observer_kills_torsion
    (readout : (ZMod 2 × ZMod 2) →ₗ[ℤ] ℤ) (point : ZMod 2 × ZMod 2) :
    readout point = 0 := by
  have killed (value : ZMod 2) : (2 : ℤ) • value = 0 := by
    rw [zsmul_eq_mul, show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul]
  have pointKilled : (2 : ℤ) • point = 0 :=
    Prod.ext (killed point.1) (killed point.2)
  have observed := readout.map_smul (2 : ℤ) point
  rw [pointKilled, map_zero] at observed
  change 0 = 2 * readout point at observed
  omega

end

end SourceOperationCharacter.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
