import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumNoetherPrice

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedQuantumFieldWindowPrice
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumActionFieldLift PreparationVacuumStaticPoleResponse PreparationVacuumMixedPrincipal
open PreparationVacuumFullOriginResponse PreparationPhysicalStaticSpatialCouplingReturn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedNoetherCoulombUnit
open ActualSourcePreparedEMEnclosure ActualSourcePreparedN3MovingResponse ActualSourcePreparedN3EMChargeRead
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedQuantumDriverCofactor ActualSourcePreparedQuantumNoetherPrice
open LowEnergy.ActualSourceQuantumCoefficientErrorOwn LowEnergy.ActualMixedNoetherTimePriceOwn
open scoped Matrix BigOperators Matrix.Norms.Operator
attribute [local irreducible] sourcePreparedFullGreenRead sourceFullGreenBinaryRead

private theorem component_price (A B : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 289 → ℂ)
    (t : ℝ) (close : ∀ i j, ‖A i j-B i j‖ ≤ t) (i : Fin 289) :
    ‖(A*ᵥv) i‖ ≤ ∑ j, (‖B i j‖+t)*‖v j‖ := by
  have entry (j : Fin 289) : ‖A i j‖ ≤ ‖B i j‖+t := by
    calc
      _ = ‖A i j-B i j+B i j‖ := by rw [sub_add_cancel]
      _ ≤ ‖A i j-B i j‖+‖B i j‖ := norm_add_le _ _
      _ ≤ t+‖B i j‖ := add_le_add (close i j) le_rfl
      _ = _ := by ring
  change ‖∑ j, A i j*v j‖ ≤ _
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (entry j) (norm_nonneg _)))

variable (event : DressedEvent) (e : scaleDomain) (sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 1)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance)

/-- The same generated full cofactor window prices the actual external field;
its tolerance is multiplied by the original temporal forcing, not a unit norm. -/
def sourceQuantumFieldWindowPrice (j : Fin 289) : ℝ :=
  let bits := sourcePreparedBinaryBits event e.val sigma n positive
    (small.trans (by norm_num)) regular tolerance accurate
  ∑ k, (‖sourceFullGreenBinaryRead event e.val sigma n bits j k‖+tolerance)*‖sourceTemporalEMForce k‖

theorem source_quantum_actual_field_window_price (j : Fin 289) :
    ‖sourceTemporalCorrectedField event e.val sigma n j‖ ≤
      sourceQuantumFieldWindowPrice event e sigma n positive small regular tolerance accurate j := by
  have close := (source_prepared_generated_enclosure event e.val sigma n positive
    (small.trans (by norm_num)) regular tolerance accurate).1
  exact component_price _ _ sourceTemporalEMForce tolerance (fun i k => (close i k).le) j

def sourceQuantumNoetherWindowMass : ℝ :=
  ∑ i, ∑ j, sourceCompleteCubicNoetherPrice event (e.val^2 • n) (fieldUnit i) (fieldUnit j)*
    sourceQuantumFieldWindowPrice event e sigma n positive small regular tolerance accurate j

theorem source_quantum_noether_window_mass_bound :
    sourceQuantumNoetherMass event e sigma n ≤
      sourceQuantumNoetherWindowMass event e sigma n positive small regular tolerance accurate := by
  unfold sourceQuantumNoetherMass sourceQuantumNoetherWindowMass
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (source_quantum_actual_field_window_price event e sigma n positive small regular tolerance accurate j)
    (sourceCompleteCubicNoetherPrice_nonnegative event _ (fieldUnit i) (fieldUnit j))

theorem source_quantum_noether_window_driver_price :
    sigma^3*‖sourceTemporalActualQuantumDriver event e sigma n‖ ≤
      56*sourceQuantumNoetherWindowMass event e sigma n positive small regular tolerance accurate :=
  (source_quantum_noether_driver_price event e sigma n positive small).trans
    (mul_le_mul_of_nonneg_left
      (source_quantum_noether_window_mass_bound event e sigma n positive small regular tolerance accurate)
      (by norm_num))

/-- The source-generated full Green window replaces the actual external-field
norm in the original full quantum IR price, on its unchanged regular chart. -/
theorem source_quantum_noether_window_ir_price (unit : spatialSquare n=1)
    (spatial_small : e.val^2 ≤ staticRadius) :
    let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, spatial_small⟩
    let driver := sourceTemporalActualQuantumDriver event e sigma n
    sigma^3*‖-(e.val:ℂ)^4*(sourceN3TemporalEMCoefficient event e.val sigma n -
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceNativeStaticMatrix e.val n*ᵥsourceTemporalEMForce)-
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceSpatialStaticRegularField n unit kappa driver))-
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceSpatialStaticPoleCoefficient n unit kappa driver)‖ ≤
      ‖noetherPairScale^2‖*((∑ i, ‖sourceTemporalEMForce i‖)*
        ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa)‖*
        (2*staticInverseBudget^2*effectiveErrorBudget*kappa.val)*
        ‖sourceQuantumNativeReader e n unit spatial_small‖*
        (56*sourceQuantumNoetherWindowMass event e sigma n positive small regular tolerance accurate)) := by
  have original := source_quantum_noether_ir_price event e sigma n unit spatial_small positive small regular
  have error_nonnegative := effectiveErrorBudget_nonneg
  apply original.trans
  have paid := mul_le_mul_of_nonneg_left
    (source_quantum_noether_window_mass_bound event e sigma n positive small regular tolerance accurate)
    (show 0 ≤ ‖noetherPairScale^2‖*((∑ i, ‖sourceTemporalEMForce i‖)*
      ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit ⟨e.val^2, pow_pos e.property.1 2, spatial_small⟩)‖*
      (2*staticInverseBudget^2*effectiveErrorBudget*e.val^2)*
      ‖sourceQuantumNativeReader e n unit spatial_small‖)*56 by positivity)
  convert paid using 1 <;> ring

end LowEnergy.GaussComposite.ActualSourcePreparedQuantumFieldWindowPrice
