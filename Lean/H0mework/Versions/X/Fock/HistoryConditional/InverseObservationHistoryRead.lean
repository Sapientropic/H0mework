import H0mework.Versions.X.Fock.HistoryConditional.InverseObservationHistoryWindow
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationHistory

open SourceCopyTimeModel SourceOwnedObservationHistory.SourceShift
noncomputable section

private theorem read_mem (program : Nat × Nat) (positive : 0 < program.1)
    (samples : SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier (horizon program)) :
    Memℓp (fun index : Nat => hilbert (samples (sampleIndex program index)) (index / program.1)) 2 := by
  let : NeZero program.1 := ⟨positive.ne'⟩
  have rows : Summable (fun pair : Fin program.1 × Nat =>
      ‖hilbert (samples ⟨horizon program - pair.1.val,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) pair.2‖ ^ (2 : ENNReal).toReal) := by
    apply (summable_prod_of_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)).mpr
    exact ⟨fun phase => (memℓp_gen_iff (by norm_num)).mp (hilbert (samples
      ⟨horizon program - phase.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).property,
      (hasSum_fintype _).summable⟩
  apply memℓp_gen
  have paid := (Nat.divModEquiv program.1).summable_iff.mpr rows.prod_symm
  exact paid

def readHilbert (program : Nat × Nat) (positive : 0 < program.1) :
    SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier (horizon program) →ₗ[ℂ] H where
  toFun samples := ⟨fun index => hilbert (samples (sampleIndex program index)) (index / program.1),
    read_mem program positive samples⟩
  map_add' left right := by
    apply lp.ext
    funext index
    exact map_add (SourceMassCompletion.firstRead.comp SourceJointClockGraph.joint) _ _ |> congrArg (fun value : H => value (index / program.1))
  map_smul' scalar samples := by
    apply lp.ext
    funext index
    exact map_smul (SourceMassCompletion.firstRead.comp SourceJointClockGraph.joint) scalar _ |> congrArg (fun value : H => value (index / program.1))

def readWindow (program : Nat × Nat) (positive : 0 < program.1) :
    SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier (horizon program) →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  let first : SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier (horizon program) →ₗ[ℂ] SourceJointClockGraph.Carrier := LinearMap.proj 0
  let massRead := (SourceMassCompletion.massRead.comp SourceJointClockGraph.joint).toLinearMap.comp first
  let clockRead := SourceJointClockGraph.clock.toLinearMap.comp first
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceMassCompletion.Joint ℂ).symm.toLinearMap.comp
    (((WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toLinearMap.comp
      ((readHilbert program positive).prod massRead)).prod
      ((program.1 : ℂ) • clockRead + (program.2 : ℂ) • massRead))

theorem read_window (depth : Nat) (word : List (SourceGeneratedActionWords.Fock.Letter depth))
    (value : SourceJointClockGraph.Carrier) :
    readWindow (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
      (SourceCompiledWordOperator.slope_positive _) (window depth word value) = value := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply lp.ext
      funext index
      exact coordinate depth word value index
    · exact SourceGWordInverse.mass_recover depth word value
  · exact SourceGWordInverse.clock_balance depth word value

theorem window_injective (depth : Nat) (word : List (SourceGeneratedActionWords.Fock.Letter depth)) :
    Function.Injective (window depth word) :=
  Function.LeftInverse.injective (read_window depth word)

end
end SourceInverseObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
