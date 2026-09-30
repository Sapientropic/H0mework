import H0mework.Fock.HistoryModel.CompletionSource
import H0mework.Fock.PrimeField.RecoveryModel

/-! Actual native words recover the prime history through the original Fock theta face. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState ParticleWaveFock ParticleWaveFockRuntime
open ArithmeticGeneration SourcePrimeHistoryRecovery

noncomputable section

theorem unit_reader_sourceState (depth : Nat) (current : Current) :
    FamilyModel.Fock.reader depth 0 current = sourceStateAt current := by
  have material := (NativeCopy.Fock.material_is_unit_iff depth 0).mpr rfl
  have copyUnit : NativeCopy.copy CanonicalUnitArithmeticRoot.unitHistory current = current := by
    apply UnitHistory.eq_of_cardinalShadow_eq
    change (current.joint CanonicalUnitArithmeticRoot.unitHistory).cardinalShadow = current.cardinalShadow
    simp only [UnitHistory.cardinalShadow_joint, CanonicalUnitArithmeticRoot.unitHistory,
      UnitHistory.cardinalShadow, Nat.mul_one]
  change sourceStateAt (NativeCopy.copy (NativeCopy.Fock.material depth 0) current) = _
  rw [material, copyUnit]

theorem unit_complete_read (depth : Nat) (current : Current) :
    completeRead (Fock.actions depth) (Fock.observer depth) (.inl ()) []
      (Complete.point depth current) 0 = sourceStateAt current := by
  rw [Complete.point, complete_read_source]
  change SourceOwnedObservationHistory.observation
    (FamilyModel.familyRead (FamilyModel.Fock.reader depth)) (sourcePoint current) 0 = _
  rw [observation_point]
  exact unit_reader_sourceState depth current

private theorem native_word_source (depth steps state : Nat) :
    run (Fock.actions depth) (List.replicate steps (.inl ()))
      (sourcePoint ((runtimeAt state).current.visit.current : Current)) =
        sourcePoint ((runtimeAt (state + steps)).current.visit.current : Current) := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps previous =>
      rw [List.replicate_succ]
      change run (Fock.actions depth) (List.replicate steps (.inl ()))
        (SourceOwnedObservationHistory.sourceAction nativeStep
          (sourcePoint ((runtimeAt state).current.visit.current : Current))) = _
      have next : SourceOwnedObservationHistory.sourceAction nativeStep
          (sourcePoint ((runtimeAt state).current.visit.current : Current)) =
          sourcePoint ((runtimeAt (state + 1)).current.visit.current : Current) :=
        SourceOwnedObservationHistory.sourceAction_point nativeStep _
      exact (congrArg (run (Fock.actions depth) (List.replicate steps (.inl ()))) next).trans
        ((previous (state + 1)).trans (congrArg (fun position : Nat =>
          sourcePoint ((runtimeAt position).current.visit.current : Current)) (by omega)))

theorem native_word_theta (depth steps state : Nat) :
    thetaProjection (completeRead (Fock.actions depth) (Fock.observer depth) (.inl ())
      (List.replicate steps (.inl ()))
      (Complete.point depth ((runtimeAt state).current.visit.current : Current)) 0) =
        rawField (state + steps) := by
  have wordRead := complete_read_source (Fock.actions depth) (Fock.observer depth) (.inl ())
    (List.replicate steps (.inl ())) (sourcePoint ((runtimeAt state).current.visit.current : Current))
  have wordSource := native_word_source depth steps state
  have material := observation_point (FamilyModel.familyRead (FamilyModel.Fock.reader depth))
    ((runtimeAt (state + steps)).current.visit.current : Current)
  have theta : thetaProjection (sourceStateAt ((runtimeAt (state + steps)).current.visit.current : Current)) =
      rawField (state + steps) := by
    change thetaProjection (secondQuantizedState (rawField (state + steps))) = _
    simp only [secondQuantizedState, map_add, thetaProjection_diagonalInclusion]
    change rawField (state + steps) + 0 = rawField (state + steps)
    exact add_zero _
  exact (congrArg (fun values : FamilyModel.Fock.Index depth → ParentCarrier => thetaProjection (values 0))
      wordRead).trans
    ((congrArg (fun source => thetaProjection (Fock.observer depth source 0)) wordSource).trans
      ((congrArg (fun values : FamilyModel.Fock.Index depth → ParentCarrier => thetaProjection (values 0)) material).trans
        ((congrArg thetaProjection (unit_reader_sourceState depth _)).trans theta)))

theorem point_runtime_injective (depth : Nat) :
    Function.Injective (fun state : Nat =>
      Complete.point depth ((runtimeAt state).current.visit.current : Current)) := by
  intro left right same
  apply SourceOperationNative.statePoint_injective process
  apply history_separates (liveGlobalOwner (runtimeAt 0).current.visit.current)
  intro steps
  rw [SourcePrimeHistoryRecovery.source_iterate, SourcePrimeHistoryRecovery.source_iterate]
  change SourceOperationNative.observer process rawField (SourceOperationNative.statePoint process (left + steps)) =
    SourceOperationNative.observer process rawField (SourceOperationNative.statePoint process (right + steps))
  rw [SourceOperationNative.observer_statePoint, SourceOperationNative.observer_statePoint]
  exact (native_word_theta depth steps left).symm.trans
    ((congrArg (fun value => thetaProjection (completeRead (Fock.actions depth) (Fock.observer depth) (.inl ())
      (List.replicate steps (.inl ())) value 0)) same).trans (native_word_theta depth steps right))

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
