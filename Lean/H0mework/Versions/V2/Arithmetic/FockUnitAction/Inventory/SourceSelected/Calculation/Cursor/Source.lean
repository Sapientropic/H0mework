import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor
import H0mework.Versions.R2.Realization.Operations.RuntimePrefix

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source

open SourceOperationEffects
open Registered

noncomputable section

namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree
  (process finiteVisit initialRuntime Runtime mathFace raw)
end OF

abbrev Material (depth : Nat) := Option (Point depth) →₀ ℤ
abbrev Value (depth : Nat) (_ : Unit) := Material depth
abbrev ActorWord (depth : Nat) := Point depth →₀ ℤ
abbrev State (depth : Nat) := (OF.process (old depth) (origin depth) (reader depth)).State

abbrev mathSeed (depth : Nat) := OF.initialRuntime (old depth) (origin depth) (reader depth)
abbrev mathTail (depth : Nat) := (mathSeed depth).tick.next

/-- The original process supplies the paid syntax; this read never reconstructs
an actor cursor from its clock or a completed future. -/
def readMaterial (depth : Nat) (state : State depth) : Material depth :=
  Finsupp.single
    (readCursor depth (OF.finiteVisit (old depth) (origin depth) (reader depth) state.down).current.1) 1

def environment (depth : Nat) : Material depth →+ Env (Value depth) Var where
  toFun material := fun _ _ => material
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The original actor word is the `some` summand; the `none` basis remains in
Material and records the genuine unbound syntax coordinate. -/
def someLift (depth : Nat) : ActorWord depth →ₗ[ℤ] Material depth :=
  Finsupp.lmapDomain ℤ ℤ Option.some

def liftEnvironment (depth : Nat) (original : Env (Registered.Value depth) Var) :
    Env (Value depth) Var := fun sort name => someLift depth (original sort name)

theorem material_is_mathFace (depth : Nat)
    (runtime : OF.Runtime (old depth) (origin depth) (reader depth)) :
    readMaterial depth runtime.state = Finsupp.single
      (readCursor depth
        (OF.mathFace (old depth) (origin depth) (reader depth) runtime).rootRead.1) 1 := rfl

private theorem readCursor_pulses (depth count : Nat) :
    readCursor depth (pulses (index depth) (active depth) count) = none := by
  induction count with
  | zero => rfl
  | succ count previous => simpa only [pulses, readCursor] using previous

theorem seed_material (depth : Nat) :
    readMaterial depth (mathSeed depth).state = Finsupp.single none 1 := by
  change Finsupp.single (readCursor depth (pulses (index depth) (active depth)
    (sourceFuel (source depth (emitted depth))))) 1 = _
  rw [readCursor_pulses]

private theorem someLift_single (depth : Nat) (point : Point depth) :
    someLift depth (Finsupp.single point (1 : ℤ)) = Finsupp.single (some point) 1 := by
  simp only [someLift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem material_at (depth count : Nat)
    (within : count ≤ sourceFuel (source depth (emitted depth))) :
    readMaterial depth (mathRuntime depth (count + 1)).state =
      someLift depth (Finsupp.single
        (runPoint (index depth) (active depth) count
          (initialPoint (index depth) (active depth) (emitted depth))) 1) := by
  change Finsupp.single (readCursor depth (mathState depth (count + 1)).1) 1 = _
  rw [current_cursor depth count within, someLift_single]

/-- The full source occurrence and ordered unit prefix enter the native material. -/
theorem material_keeps_prefix (depth count : Nat)
    (within : count ≤ sourceFuel (source depth (emitted depth))) :
    readMaterial depth (mathRuntime depth (count + 1)).state =
      Finsupp.single (some (⟨emitted depth,
        run count (initial (source depth (emitted depth)))⟩ : Point depth)) 1 := by
  change Finsupp.single (readCursor depth (mathState depth (count + 1)).1) 1 = _
  rw [current_cursor_fibre depth count within]

/-- The next material is read at the literal canonical successor and recognized
as the existing action on the old actor word. -/
theorem material_literal_next (depth count : Nat)
    (within : count < sourceFuel (source depth (emitted depth))) :
    readMaterial depth (mathRuntime depth (count + 1)).tick.next.state =
      someLift depth (action (index depth) (active depth) (Finsupp.single
        (runPoint (index depth) (active depth) count
          (initialPoint (index depth) (active depth) (emitted depth))) 1)) := by
  change Finsupp.single
    (readCursor depth
      (Engine.runtimeCurrent (old depth) (origin depth) (reader depth)
        (mathRuntime depth (count + 1)).tick.next).1) 1 = _
  rw [literal_next_cursor depth count within, current_cursor depth count (by omega)]
  simp only [Option.map_some, action, LinearMap.toAddMonoidHom_coe,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, someLift]

/-- The actual generated material difference is the same source action effect,
including every occurrence and receipt coordinate. -/
theorem literal_increment_at (depth count : Nat)
    (within : count < sourceFuel (source depth (emitted depth))) :
    SourceOperationRuntime.incrementEnvironment (readMaterial depth) (environment depth)
      (SourceGeneratedRuntimeMaterialStageAt.generate (mathRuntime depth (count + 1))) =
    fun _ _ => someLift depth
      (action (index depth) (active depth) (Finsupp.single
        (runPoint (index depth) (active depth) count
          (initialPoint (index depth) (active depth) (emitted depth))) 1) -
      Finsupp.single
        (runPoint (index depth) (active depth) count
          (initialPoint (index depth) (active depth) (emitted depth))) 1) := by
  funext sort name
  change readMaterial depth (mathRuntime depth (count + 1)).tick.next.state -
    readMaterial depth (mathRuntime depth (count + 1)).state = _
  rw [material_literal_next depth count within, material_at depth count (by omega), map_sub]

/-- Binding is a prior canonical tick. The first actor pulse consumes its sealed
successor, rather than an arbitrary process state. -/
theorem first_pulse_increment (depth : Nat) :
    SourceOperationRuntime.incrementEnvironment (readMaterial depth) (environment depth)
      (SourceGeneratedRuntimeMaterialStageAt.generate (mathTail depth)) =
        liftEnvironment depth (actualIncrement depth) := by
  have positive : 0 < sourceFuel (source depth (emitted depth)) := by
    unfold sourceFuel
    have floor := CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer.splitRight_atLeastTwo
      (source depth (emitted depth))
    omega
  change SourceOperationRuntime.incrementEnvironment (readMaterial depth) (environment depth)
    (SourceGeneratedRuntimeMaterialStageAt.generate (mathRuntime depth (0 + 1))) = _
  rw [literal_increment_at depth 0 positive]
  rfl

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
