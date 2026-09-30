import H0mework.Versions.X.Fock.HistoryPolynomial.CopySource
import H0mework.Versions.X.Fock.HistoryModel.SourceWords

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyProgram

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory
noncomputable section

def whole : SourceOperationNative.Carrier process →ₗ[ℤ] Carrier Current :=
  (FullWord.word nativeStep).comp FullProjection.Fock.bridge

theorem whole_point (state : Nat) :
    whole (SourceOperationNative.statePoint process state) = sourcePoint (finiteVisit state).current := by
  change FullWord.word nativeStep (FullProjection.Fock.bridge (SourceOperationNative.statePoint process state)) = _
  rw [FullProjection.Fock.bridge_statePoint]
  exact FullWord.word_source nativeStep _

theorem whole_is_source : whole = Finsupp.lmapDomain ℤ ℤ (fun state => (finiteVisit state).current) := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  change whole (SourceOperationNative.statePoint process state) =
    Finsupp.mapDomain (fun state => (finiteVisit state).current) (Finsupp.single state 1)
  rw [Finsupp.mapDomain_single]
  exact whole_point state

theorem whole_copy (depth : Nat) (index : Index depth) (word : SourceOperationNative.Carrier process) :
    whole (action depth index word) =
      SourceGeneratedActionWords.Fock.actions depth (.inr index) (whole word) := by
  rw [whole_is_source]
  have same := congrArg (Finsupp.lmapDomain ℤ ℤ) (funext (actual_copy_state depth index))
  have source : (Finsupp.lmapDomain ℤ ℤ (fun state => (finiteVisit state).current)).comp
      (Finsupp.lmapDomain ℤ ℤ (indexAfter depth index)) =
      (Finsupp.lmapDomain ℤ ℤ (NativeCopy.copy (NativeCopy.Fock.material depth index))).comp
        (Finsupp.lmapDomain ℤ ℤ (fun state => (finiteVisit state).current)) := by
    exact (Finsupp.lmapDomain_comp ℤ ℤ (indexAfter depth index)
      (fun state => (finiteVisit state).current)).symm.trans (same.trans
        (Finsupp.lmapDomain_comp ℤ ℤ (fun state => (finiteVisit state).current)
          (NativeCopy.copy (NativeCopy.Fock.material depth index))))
  exact LinearMap.congr_fun source word

theorem whole_native (word : SourceOperationNative.Carrier process) :
    whole (SourcePrimeHistoryRecovery.nativeAction word) = sourceAction nativeStep (whole word) := by
  have field := LinearMap.congr_fun FullProjection.Fock.bridge_action word
  exact (congrArg (FullWord.word nativeStep) field).symm.trans (FullWord.word_action nativeStep _)

theorem original_field_action (depth : Nat) (index : Index depth)
    (word : SourceOperationNative.Carrier process) :
    FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index))
        (NativeCopy.copy (NativeCopy.Fock.material depth index)) (FullProjection.Fock.bridge word) =
      FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index)) id
        (FullProjection.Fock.bridge (action depth index word)) := by
  apply FullWord.word_injective
  rw [FullMap.map_word, FullMap.map_word, Finsupp.lmapDomain_id, LinearMap.id_apply]
  exact (whole_copy depth index word).symm

end
end SourceCopyProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
