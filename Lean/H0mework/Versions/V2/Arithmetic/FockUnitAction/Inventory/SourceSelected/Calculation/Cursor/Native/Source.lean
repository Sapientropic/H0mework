import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Consumer
import H0mework.Versions.R2.Realization.Operations.FieldInputs
import H0mework.Versions.R2.Realization.Operations.Context.Action
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Relations.Tick
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Source
import H0mework.Realization.Operations.CompleteWordDual
import H0mework.Versions.PR.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceKernel
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source

open SourceOperationEffects

noncomputable section

namespace R
export Registered (old origin reader index active source actualIncrement)
end R
namespace C
export Cursor (mathRuntime mathState)
end C
namespace S
export Cursor.Source (Material Value environment readMaterial)
end S
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (process Runtime mathFace facade)
end OF

abbrev process (depth : Nat) := OF.process (R.old depth) (R.origin depth) (R.reader depth)
abbrev FullCarrier (depth : Nat) := SourceOperationNative.Carrier (process depth)

def readEnv (depth : Nat) : (process depth).State → Env (S.Value depth) Var :=
  fun state => S.environment depth (S.readMaterial depth state)

def physicalExpr (depth : Nat) : Expr (S.Value depth) Var Unit.unit := .var Unit.unit

def fullExpr (depth : Nat) := SourceOperationNative.Context.embed (readEnv depth) (physicalExpr depth)

def cursorRestriction (depth : Nat) : FullCarrier depth →ₗ[ℤ] S.Material depth :=
  SourceOperationNative.observer (process depth) (S.readMaterial depth)

/-- The native packet retains the activated stage, installed mathematical and
relation inventories, and complete source material before any cursor readout. -/
def packet (depth count : Nat) :=
  let runtime := C.mathRuntime depth count
  (SourceGeneratedRuntimeMaterialStageAt.generate runtime,
    (OF.mathFace (R.old depth) (R.origin depth) (R.reader depth) runtime).rootRead,
    (RootGeneratedDebtActivationJointSource.OwnerFree.Relations.sourceFace
      (R.old depth) (R.origin depth) (R.reader depth) runtime).rootRead,
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      runtime.current.root.toAuthoritativeRoot runtime.emittedOccurrence)

abbrev pairing (depth : Nat) : FullCarrier depth →ₗ[ℤ] Module.Dual ℤ (FullCarrier depth) :=
  SourceGeneratedCompleteWordDual.pairing

abbrev nativeEnvironment (depth : Nat) := SourceOperationNative.Field.environment (process depth)
abbrev nativeRead (depth : Nat) := SourceOperationNative.statePoint (process depth)
abbrev NativeField (depth count : Nat) :=
  SourceOperationRuntime.Character.Carrier (R := ℤ) (s := PUnit.unit)
    (nativeRead depth) (nativeEnvironment depth) (C.mathRuntime depth count)

def algebra (depth : Nat) := (pairing depth, SourceOperationNative.sourceAction (process depth))
def combinatorial (depth count : Nat) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Relations.history
    (R.old depth) (R.origin depth) (R.reader depth) (C.mathRuntime depth count)
abbrev topology (depth count : Nat) := CofinalAllPrimeTopology.allStageSourceUniformity (L := NativeField depth count)
def logic (depth : Nat) := SourceOperationLogic.fibreDecomposition (pairing depth)
def relation (depth count : Nat) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Relations.evaluationFace
    (R.old depth) (R.origin depth) (R.reader depth) (C.mathRuntime depth count),
   SourceOperationRuntime.Fibre.actualMorphism (R := ℤ) (s := PUnit.unit)
    (nativeRead depth) (nativeEnvironment depth) (C.mathRuntime depth count))
def cochain (depth count : Nat) :=
  SourceOperationScalarCochain.cochain (R := ℤ) (s := PUnit.unit)
    (SourceOperationRuntime.oldEnvironment (nativeRead depth) (nativeEnvironment depth)
      (SourceGeneratedRuntimeMaterialStageAt.generate (C.mathRuntime depth count)))
    (SourceOperationRuntime.incrementEnvironment (nativeRead depth) (nativeEnvironment depth)
      (SourceGeneratedRuntimeMaterialStageAt.generate (C.mathRuntime depth count)))

abbrev Input (depth count : Nat) := UnifiedFourFace.Input (type_of% (packet depth count))
  ((type_of% (packet depth count)) × type_of% (algebra depth))
  ((type_of% (packet depth count)) × type_of% (combinatorial depth count))
  ((type_of% (packet depth count)) × type_of% (topology depth count))
  ((type_of% (packet depth count)) × type_of% (logic depth))
  ((type_of% (packet depth count)) × type_of% (relation depth count))
  ((type_of% (packet depth count)) × type_of% (cochain depth count))
  (FullCarrier depth) (FullCarrier depth)

def input (depth count : Nat) : Input depth count where
  occurrence := .zero (packet depth count)
  algebraAt := fun original => (original, algebra depth)
  combinatorialAt := fun original => (original, combinatorial depth count)
  topologicalAt := fun original => (original, topology depth count)
  logicalAt := fun original => (original, logic depth)
  relationAt := fun original => (original, relation depth count)
  cochainAt := fun original => (original, cochain depth count)
  dualEvaluationAt := fun _ => pairing depth
  faithfulAt := fun _ => LinearMap.id

def generated (depth count : Nat) := UnifiedFourFace.generate (input depth count)
abbrev Coimage (depth count : Nat) := UnifiedFourFace.Perfectification (input depth count)
abbrev canonical (depth count : Nat) := (generated depth count).canonical

def recover (depth count : Nat) : Coimage depth count →ₗ[ℤ] FullCarrier depth :=
  SourceGeneratedCompleteWordDual.coimageRecovery

theorem complete_inverse (depth count : Nat) (word : FullCarrier depth) :
    recover depth count (canonical depth count word) = word :=
  SourceGeneratedCompleteWordDual.recovery_source word

theorem cursor_restriction (depth count : Nat) :
    cursorRestriction depth (SourceOperationNative.point (C.mathRuntime depth count)) =
      S.readMaterial depth (C.mathRuntime depth count).state :=
  SourceOperationNative.observer_point _ _

theorem full_eval (depth count : Nat) :
    (fullExpr depth).eval (SourceOperationNative.Context.environment
      (PhysicalValue := S.Value depth) (SourceOperationNative.point (C.mathRuntime depth count))) =
      S.readMaterial depth (C.mathRuntime depth count).state :=
  SourceOperationNative.Context.embed_eval (readEnv depth) (physicalExpr depth) (C.mathRuntime depth count)

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
