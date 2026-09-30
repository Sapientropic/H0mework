import H0mework.NavierStokes.WindowPhysics.RootControl
import H0mework.NavierStokes.Butterfly.StackedSourceCurrent
import H0mework.Foundation.Runtime.Activation

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewRuntime

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

abbrev initial := stackedShortCurrent

def visit (index : ℕ) : SourceNativeTemporalVisitAt (nativeTemporalRoot initial) :=
  .finite ((nativeTemporalProductiveHistory initial).visitAt index)

def currentAt (index : ℕ) : SourceNativeLivingRootCurrentAt (N initial) :=
  ⟨V initial, living initial, visit index⟩

def depth (current : SourceNativeLivingRootCurrentAt (N initial)) : ℕ :=
  match current.visit.history with
  | .finite history => ProductiveFiniteRootHistoryAt.causalDepth history
  | .postCofinal _ => 0

theorem currentAt_depth (index : ℕ) : depth (currentAt index) = index :=
  (nativeTemporalProductiveHistory initial).visitAt_depth index

def process : SourceNativeLivingRootProcess (N initial) where
  State := ℕ
  stateAt := currentAt
  stateAt_injective := by
    intro first last same
    simpa only [currentAt_depth] using congrArg depth same
  initial := 0
  successorAt index := by
    refine ⟨index + 1, ?_, ?_⟩
    · cases index <;> rfl
    · generalize (currentAt index).root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (currentAt index).visit.current = generated
      cases generated <;> trivial

/-- One source-fixed instrument: the heat evolution for one physical time unit. -/
def resolution : HeatQuery := ⟨1, by norm_num⟩

def facade : SourceNativeLivingRuntimeFacade (N initial) where
  process := process
  FaceAt := fun _ => PUnit
  componentAt := fun _ _ => component initial
  installationAt := fun _ _ => installation initial
  projectionAt := fun _ _ => resolution

def seed : LivingRuntimeState process := facade.seed

def carrier (runtime : LivingRuntimeState process) :
    CarrierAt initial runtime.emittedOccurrence :=
  match facade.readoutAt runtime PUnit.unit with
  | .inl ⟨_, payload⟩ => payload
  | .inr impossible => nomatch impossible

theorem carrier_generated (runtime : LivingRuntimeState process) :
    carrier runtime = generatedCarrier initial runtime.emittedOccurrence := rfl

theorem activated_readout (runtime : LivingRuntimeState process) :
    HEq (facade.readoutAt runtime PUnit.unit)
      (runtime.tick.generated.projectionOutcome ((installation initial).embed resolution)) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        ((nativeTemporalRoot initial).generatedLedgerAt (visit runtime.state).current) ∧
      runtime.tick.nextCurrent = process.stateAt (process.successor runtime.state) := by
  have covered := facade.readoutAt_factorizes runtime PUnit.unit
  exact ⟨covered.2.2.2.1, covered.2.2.1, covered.2.2.2.2⟩

theorem actual_successor (runtime : LivingRuntimeState process) :
    runtime.tick.next.state = Nat.succ runtime.state := rfl

end
end SaturationMonoid.NavierStokes.NativeViewRuntime
