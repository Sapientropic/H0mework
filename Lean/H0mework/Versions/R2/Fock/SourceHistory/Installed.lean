import H0mework.Versions.R2.Arithmetic.FockDynamics.RootRuntime
import H0mework.Versions.R2.Probability.Source.Hilbert
import H0mework.Versions.R2.Fock.SourceHistory.Window
import H0mework.Versions.R2.Probability.FullSource.Read

/-! The installed native write acts on its whole past window, with the complete source residual retained. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.Installed

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

abbrev Current := CanonicalUnitArithmeticRoot.Current
abbrev nativeStep := CanonicalUnitArithmeticRoot.next
abbrev fullRead : Current → Carrier Current := sourcePoint

abbrev SourceSpace (current : Current) :=
  Space nativeStep fullRead CanonicalUnitArithmeticRoot.initialCurrent (NativeWindow.bound current)

abbrev ImageSpace (current : Current) :=
  Space nativeStep fullRead (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) (NativeWindow.bound current)

abbrev LostSpace (current : Current) :=
  ResidualSpace nativeStep fullRead CanonicalUnitArithmeticRoot.initialCurrent (NativeWindow.bound current)

/-- Pure mathematical substrate; authority is consumed by the runtime theorem below. -/
def oneStep (current : Current) : SourceSpace current ≃ₗ[ℂ] ImageSpace current × LostSpace current :=
  retainedUpdate nativeStep fullRead CanonicalUnitArithmeticRoot.initialCurrent (NativeWindow.bound current)

theorem oneStep_reconstruct (current : Current) (value : SourceSpace current) :
    (oneStep current).symm (oneStep current value) = value :=
  (oneStep current).symm_apply_apply value

theorem oneStep_energy (current : Current) (value : SourceSpace current) :
    ‖value‖ ^ 2 = ‖(oneStep current value).1‖ ^ 2 + ‖(oneStep current value).2‖ ^ 2 :=
  retainedUpdate_energy nativeStep fullRead CanonicalUnitArithmeticRoot.initialCurrent
    (NativeWindow.bound current) value

variable {current : Current}
variable {occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
variable {active : 1 ≤ scanIndex current}
variable (payload : RootGeneratedParticleWaveCurrentAt current occurrence active)

theorem native_point :
    sourceAction nativeStep (sourcePoint current) = sourcePoint payload.nativeWrite.target := by
  rw [payload.nativeWrite_eq]
  exact sourceAction_point nativeStep current

theorem native_field_point :
    fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current) =
      fieldPoint nativeStep fullRead payload.nativeWrite.target := by
  rw [payload.nativeWrite_eq]
  exact fieldPoint_action nativeStep fullRead current

theorem native_field_point_changed :
    fieldPoint nativeStep fullRead payload.nativeWrite.target ≠
      fieldPoint nativeStep fullRead current := by
  intro same
  exact payload.nativeWrite.target_ne_source
    (full_fieldPoint_injective nativeStep same)

theorem window_endpoints :
    nativeStep^[NativeWindow.bound current] CanonicalUnitArithmeticRoot.initialCurrent = current ∧
      nativeStep^[NativeWindow.bound current] (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) =
        payload.nativeWrite.target :=
  ⟨NativeWindow.last_source current active, NativeWindow.native_last_image active payload.nativeWrite⟩

theorem window_prefixes (index : Fin (NativeWindow.bound current + 1)) :
    nativeStep^[NativeWindow.bound current - index.val] (NativeWindow.point current index) = current ∧
      nativeStep^[NativeWindow.bound current - index.val] (NativeWindow.imagePoint current index) =
        payload.nativeWrite.target :=
  ⟨NativeWindow.point_prefix current active index,
    NativeWindow.native_image_prefix active payload.nativeWrite index⟩

def runtimeOneStep (depth : Nat) := oneStep (runtimeAt depth).current.visit.current

theorem runtime_current_next (depth : Nat) :
    (runtimeAt depth).tick.next.current.visit.current = (runtimePayload depth).nativeWrite.target := by
  rw [(runtimePayload depth).nativeWrite_eq]
  rfl

theorem runtime_bound (depth : Nat) :
    NativeWindow.bound (runtimeAt depth).current.visit.current = depth := by
  change scanIndex (runtimeAt depth).current.visit.current - 1 = depth
  rw [runtimeAt_scanIndex, Nat.add_sub_cancel]

theorem runtime_current_iterate (depth : Nat) :
    (runtimeAt depth).current.visit.current =
      nativeStep^[depth] CanonicalUnitArithmeticRoot.initialCurrent := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
      change nativeStep (runtimeAt depth).current.visit.current = _
      exact (congrArg nativeStep previous).trans
        (Function.iterate_succ_apply' nativeStep depth CanonicalUnitArithmeticRoot.initialCurrent).symm

def materialHistory (depth : Nat) : SourceGeneratedRuntimeMaterialHistoryAt runtimeSeed
    (NativeWindow.bound (runtimeAt depth).current.visit.current + 1) :=
  .generate runtimeSeed _

theorem window_actor_factorizes (depth : Nat)
    (index : Fin (NativeWindow.bound (runtimeAt depth).current.visit.current + 1)) :
    let current := (runtimeAt depth).current.visit.current
    let runtime := runtimeAt index.val
    let stage := (materialHistory depth).stageAt index
    NativeWindow.point current index = runtime.current.visit.current ∧
      NativeWindow.imagePoint current index = stage.next.current.visit.current ∧
      fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead (NativeWindow.point current index)) =
        fieldPoint nativeStep fullRead stage.next.current.visit.current ∧
      (runtimeFacade.process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) := by
  have source : NativeWindow.point (runtimeAt depth).current.visit.current index =
      (runtimeAt index.val).current.visit.current := (runtime_current_iterate index.val).symm
  have image : NativeWindow.imagePoint (runtimeAt depth).current.visit.current index =
      ((materialHistory depth).stageAt index).next.current.visit.current := congrArg nativeStep source
  exact ⟨source, image,
    (fieldPoint_action nativeStep fullRead _).trans (congrArg (fieldPoint nativeStep fullRead) image),
    ((materialHistory depth).stageAt index).factorizes⟩

theorem runtime_oneStep_factorizes (depth : Nat)
    (value : SourceSpace (runtimeAt depth).current.visit.current) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    (runtimeOneStep depth).symm (runtimeOneStep depth value) = value ∧
      NativeWindow.bound runtime.current.visit.current = depth ∧
      (nativeStep^[NativeWindow.bound runtime.current.visit.current] CanonicalUnitArithmeticRoot.initialCurrent =
          runtime.current.visit.current ∧
        nativeStep^[NativeWindow.bound runtime.current.visit.current]
            (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) = (runtimePayload depth).nativeWrite.target) ∧
      (∀ index : Fin (NativeWindow.bound runtime.current.visit.current + 1),
        NativeWindow.point runtime.current.visit.current index = (runtimeAt index.val).current.visit.current ∧
        NativeWindow.imagePoint runtime.current.visit.current index =
          ((materialHistory depth).stageAt index).next.current.visit.current) ∧
      sourceAction nativeStep (sourcePoint runtime.current.visit.current) =
        sourcePoint (runtimePayload depth).nativeWrite.target ∧
      (runtimePayload depth).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave =
        .inl ⟨runtimeActive depth, runtimePayload depth⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      (runtimeFacade.process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) ∧
      stage.next.current.visit.current = (runtimePayload depth).nativeWrite.target := by
  have installed := coversAt_factorizes (runtimeAt depth) .particleWave
  exact ⟨oneStep_reconstruct _ value, runtime_bound depth, window_endpoints (runtimePayload depth),
    (fun index => ⟨(window_actor_factorizes depth index).1, (window_actor_factorizes depth index).2.1⟩),
    native_point (runtimePayload depth),
    (runtimePayload depth).sourceOccurrence_eq, runtimeReadout_is_particleWave depth,
    installed.2.2.2.1, (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)).factorizes,
    runtime_current_next depth⟩

end
end SourceOwnedObservationHistory.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
