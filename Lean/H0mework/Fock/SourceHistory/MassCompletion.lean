import H0mework.Probability.MassCompletion.Native
import H0mework.Probability.MassCompletion.Density
import H0mework.Probability.MassCompletion.Boundary
import H0mework.Fock.SourceHistory.Installed

/-! The original runtime consumes both coordinates and the source-generated nonzero invariant limit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMassCompletion

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift Filter
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Topology

noncomputable section

theorem runtime_point_next (depth : Nat) :
    action (nativeRead (sourcePoint (runtimeAt depth).state)) =
      nativeRead (sourcePoint (runtimeAt depth).tick.next.state) :=
  (action_native (sourcePoint (runtimeAt depth).state)).symm.trans
    (congrArg nativeRead (sourceAction_point Nat.succ (runtimeAt depth).state))

theorem runtime_point_mass (depth : Nat) : massRead (nativeRead (sourcePoint (runtimeAt depth).state)) = 1 := by
  rw [massRead_native]
  change (mass ℤ (Finsupp.single (runtimeAt depth).state 1) : ℂ) = 1
  rw [mass_single, Int.cast_one]

theorem generated_limit_mass : massRead (WithLp.toLp 2 ((0 : H), (1 : ℂ))) = 1 := by
  have generated : Tendsto (fun bound => massRead (jointRead (meanWord bound))) atTop
      (𝓝 (massRead (WithLp.toLp 2 ((0 : H), (1 : ℂ))))) := by
    simpa only [Function.comp_def] using massRead.continuous.continuousAt.tendsto.comp source_mean_tendsto
  have conserved : Tendsto (fun bound => massRead (jointRead (meanWord bound))) atTop (𝓝 (1 : ℂ)) := by
    simpa only [massRead_source, mass_meanWord] using (tendsto_const_nhds (x := (1 : ℂ)))
  exact tendsto_nhds_unique generated conserved

theorem generated_limit_ne_zero : WithLp.toLp 2 ((0 : H), (1 : ℂ)) ≠ (0 : Joint) := by
  intro vanished
  have preserved := generated_limit_mass
  rw [vanished, map_zero] at preserved
  exact zero_ne_one preserved

theorem firstRead_generated_limit : firstRead (WithLp.toLp 2 ((0 : H), (1 : ℂ))) = 0 := rfl

theorem runtime_joint_completion_factorizes (depth : Nat) (word : Carrier Nat) (left right : Joint) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    jointRead.range.topologicalClosure = ⊤ ∧
      nativeRead (sourceAction runtimeFacade.process.successor word) = action (nativeRead word) ∧
      firstRead (nativeRead word) = SourceShift.wordRead word ∧
      massRead (nativeRead word) = (mass ℤ word : ℂ) ∧
      action (nativeRead (sourcePoint runtime.state)) = nativeRead (sourcePoint stage.next.state) ∧
      massRead (nativeRead (sourcePoint stage.next.state)) = 1 ∧
      (massRead left = massRead right ↔
        left - right ∈ (jointRead.comp (SourceSuccessorBoundary.boundary ℂ)).range.topologicalClosure) ∧
      Tendsto (fun bound => jointRead (meanWord bound)) atTop (𝓝 (WithLp.toLp 2 ((0 : H), (1 : ℂ)))) ∧
      massRead (WithLp.toLp 2 ((0 : H), (1 : ℂ))) = 1 ∧
      WithLp.toLp 2 ((0 : H), (1 : ℂ)) ≠ (0 : Joint) ∧
      firstRead (WithLp.toLp 2 ((0 : H), (1 : ℂ))) = 0 ∧
      action (WithLp.toLp 2 ((0 : H), (1 : ℂ))) = WithLp.toLp 2 (0, 1) ∧
      WithLp.toLp 2 ((0 : H), (1 : ℂ)) ∉
        (jointRead.comp (SourceSuccessorBoundary.boundary ℂ)).range.topologicalClosure ∧
      (∀ index : Fin (NativeWindow.bound runtime.current.visit.current + 1),
        NativeWindow.point runtime.current.visit.current index = (runtimeAt index.val).current.visit.current ∧
          NativeWindow.imagePoint runtime.current.visit.current index =
            ((materialHistory depth).stageAt index).next.current.visit.current ∧
          action (nativeRead (sourcePoint (runtimeAt index.val).state)) =
            nativeRead (sourcePoint ((materialHistory depth).stageAt index).next.state)) ∧
      (runtimePayload depth).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, runtimePayload depth⟩ ∧
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
  exact ⟨range_jointRead_closure_eq_top, action_native word, firstRead_native word, massRead_native word,
    runtime_point_next depth, runtime_point_mass (depth + 1), massRead_fibre_iff left right,
    source_mean_tendsto, generated_limit_mass, generated_limit_ne_zero, firstRead_generated_limit,
    generated_limit_fixed, mass_axis_not_mem_boundary_closure,
    (fun index => ⟨(window_actor_factorizes depth index).1, (window_actor_factorizes depth index).2.1,
      runtime_point_next index.val⟩),
    (runtimePayload depth).sourceOccurrence_eq, runtimeReadout_is_particleWave depth, installed.2.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)).factorizes, runtime_current_next depth⟩

end
end SourceMassCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
