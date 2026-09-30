import H0mework.Fock.HistoryModel.RecordedAtomicQuery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAtomicObservation.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
open SourcePrimeHistoryRecovery SourcePrimeCalculation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance witnessUniform (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) :=
  fieldUniform nativeStep (rawWords depth)
local instance witnessMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)
local instance witnessBorel (depth : Nat) : BorelSpace (Field nativeStep (rawWords depth)) := ⟨rfl⟩
local instance witnessT2 (depth : Nat) : T2Space (Field nativeStep (rawWords depth)) := Actor.conditionalFieldT2 depth

def witness (depth bound : Nat) (actor : Fin (bound + 1)) :
    SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound :=
  SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound
    (cotest (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound)
      (whole depth bound (recordedQuery bound actor)))

theorem query_witness (depth bound : Nat) (actor : Fin (bound + 1)) :
    query depth bound actor (witness depth bound actor) = 1 := by
  let atom : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
      (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound :=
    cotest (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound)
      (whole depth bound (recordedQuery bound actor))
  have returned := IsometricRetainedTransfer.transfer_pullback
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) atom
  have read := congrArg (fun value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
    (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound =>
      value (whole depth bound (recordedQuery bound actor))) returned
  exact read.trans (cotest_at _ _ (recorded_supported depth bound actor))

theorem witness_norm (depth bound : Nat) (actor : Fin (bound + 1)) :
    ‖witness depth bound actor‖ = 1 / Real.sqrt ((bound + 1 : Nat) : ℝ) := by
  let atom : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
      (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound :=
    cotest (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound)
      (whole depth bound (recordedQuery bound actor))
  have conserved := (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth)
    CanonicalUnitArithmeticRoot.initialCurrent bound).norm_map atom
  have mass := cotest_norm
    (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound)
    (whole depth bound (recordedQuery bound actor))
  rw [recorded_mass, ENNReal.toReal_inv, ENNReal.toReal_natCast, Real.sqrt_inv] at mass
  calc
    ‖witness depth bound actor‖ = ‖atom‖ := conserved
    _ = (Real.sqrt ((bound + 1 : Nat) : ℝ))⁻¹ := mass
    _ = _ := (one_div _).symm

theorem recorded_error_bound (depth bound : Nat) (actor : Fin (bound + 1))
    (left right : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    ‖decoder sourceOwner bound (fun index => left (Actor.originalRead depth bound index)) (recordedQuery bound actor) -
        decoder sourceOwner bound (fun index => right (Actor.originalRead depth bound index)) (recordedQuery bound actor)‖ ≤
      Real.sqrt ((bound + 1 : Nat) : ℝ) * ‖left - right‖ := by
  have estimate := (query depth bound actor).le_opNorm (left - right)
  rw [map_sub, query_norm, query_read, query_read] at estimate
  exact estimate

theorem query_not_contractive (depth bound : Nat) (positive : 0 < bound) (actor : Fin (bound + 1)) :
    ‖witness depth bound actor‖ < ‖query depth bound actor (witness depth bound actor)‖ := by
  rw [witness_norm, query_witness, norm_one]
  have root : 1 < Real.sqrt ((bound + 1 : Nat) : ℝ) := by
    have greater : (1 : ℝ) < ((bound + 1 : Nat) : ℝ) := by exact_mod_cast (by omega : 1 < bound + 1)
    nlinarith [Real.sq_sqrt (le_trans (by norm_num : (0 : ℝ) ≤ 1) greater.le),
      Real.sqrt_nonneg ((bound + 1 : Nat) : ℝ)]
  exact (div_lt_one (lt_trans (by norm_num : (0 : ℝ) < 1) root)).mpr root

end
end SourceGeneratedAtomicObservation.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
