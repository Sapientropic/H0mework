import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationNumericCompleteArrays

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNumericSource
open PreparationVacuumTailSupport PreparationVacuumWeyl PreparationVacuumEngineSource
open PreparationVacuumCanonicalMoyal PreparationVacuumCentralBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators

theorem source_five_energy_read (k : ℕ) : sourceFiveArrays k 4=sourceEnergyArray k := rfl

theorem source_five_clock_read (k : ℕ) (a : Fin 4) :
    sourceFiveArrays k a.castSucc=sourceClockCoefficientArray (k-1) a := by
  simp only [sourceFiveArrays,Fin.lastCases_castSucc]

theorem actual_stage_clock_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) (positive : 1 ≤ k) (a : Fin 4) :
    FiniteBound (sourceEngine k a (Fin.last k)) M (sourceFiveArrays k a.castSucc)
      (z,WithLp.toLp 2 u) := by
  cases k with
  | zero=>omega
  | succ k=>
    simpa only [source_five_clock_read,Nat.add_sub_cancel_right] using
      actual_source_clock_budget z u zbox ubox unit k M a

theorem generated_unit_energy_inputs (N : ℕ) : UnitEnergyInputs sourceFiveArrays N where
  coefficients:=by
    intro z hz u hu unit k _
    exact actual_source_energy_budget z u hz hu unit k N

-- The original serialized fold is responsible for this numerical admission.
-- This transports the proved jets; it never changes B or its original radii.
theorem original_stream_unit_inputs (B : ℕ → Fin 5 → ArrayBound) (N : ℕ)
    (admission : ∀ k,2 ≤ k → ∀ m,m ≤ N → sourceEnergyArray k m ≤ B k 4 m) :
    UnitEnergyInputs B N where
  coefficients:=by
    intro z hz u hu unit k hk m hm w
    exact (actual_source_energy_budget z u hz hu unit k N m hm w).trans (admission k hk m hm)

theorem original_stream_unit_102 (B : ℕ → Fin 5 → ArrayBound)
    (admission : ∀ k,2 ≤ k → ∀ m,m ≤ 102 → sourceEnergyArray k m ≤ B k 4 m) :
    UnitEnergyInputs B 102 := original_stream_unit_inputs B 102 admission

end LowEnergy.PreparationVacuumNumericSource
