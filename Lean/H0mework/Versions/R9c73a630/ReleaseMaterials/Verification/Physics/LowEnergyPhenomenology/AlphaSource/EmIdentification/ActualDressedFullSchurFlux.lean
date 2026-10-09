import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintClockColumns

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSchurClock
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedClockMoment ActualDressedPhysicalClock
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open ActualDressedNullNative ActualEMDressedClockGerm ActualEMDressedClockSchur
open Filter
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalChange originalReadback sourceNullLift sourceCokernel
  clockResolvent dressedWindowPolarization clockFeedbackJet dressedCoincidentClockJet
  dressedSynchronizedPencil dressedNativeClockFlux clockGreen clockGreenJet clockNullJet

private abbrev matrixNorm (m n : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin n) ℂ) := by
  unfold Matrix
  infer_instance

attribute [local instance] matrixNorm

private abbrev matrixSpace (m n : ℕ) : NormedSpace ℂ (Matrix (Fin m) (Fin n) ℂ) := by
  unfold Matrix
  infer_instance

attribute [local instance] matrixSpace

/-- This is the previously generated original Schur matrix, with both actual clock-dependent column maps. -/
theorem clock_schur_original_product (event : DressedEvent) (T : ℝ) (z : ℂ) :
    clockSchur event T z=clockNativeCokernel z*
      dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock z) z T*
        clockResolvent event T z*clockNativeNull z := by
  ext n m
  change sourceCokernel (sourceInputClock z)
    (dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock z) z T*ᵥ
      (clockResolvent event T z*ᵥsourceNullLift (sourceInputClock z) (Pi.single m 1))) n=_
  rw [←(clock_native_columns_actual z (Pi.single m 1) 0).1,
    ←(clock_native_columns_actual z 0 _).2]
  simp only [Matrix.mulVec_mulVec,Matrix.mulVec_single_one,←Matrix.mul_assoc]
  rfl

private theorem rectangular_product_derivative {m n r : ℕ}
    (A : ℂ→Matrix (Fin m) (Fin n) ℂ) (B : ℂ→Matrix (Fin n) (Fin r) ℂ)
    (DA : Matrix (Fin m) (Fin n) ℂ) (DB : Matrix (Fin n) (Fin r) ℂ) (z : ℂ)
    (ha : HasDerivAt A DA z) (hb : HasDerivAt B DB z) :
    HasDerivAt (fun w=>A w*B w) (DA*B z+A z*DB) z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro k
  change HasDerivAt (fun w=>∑j : Fin n,A w i j*B w j k)
    ((∑j : Fin n,DA i j*B z j k)+(∑j : Fin n,A z i j*DB j k)) z
  rw [←Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum
  intro j _
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp ha i) j).mul
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hb j) k)

private def originalInverseFlux (event : DressedEvent) (T : ℝ) (z : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  -(clockResolvent event T z*
    ((T:ℂ)⁻¹ • (clockGreenJet z*dressedSynchronizedPencil (anchorEvent event) 0 z T+
      clockGreen z*dressedNativeClockFlux (anchorEvent event) 0 z T)+clockNullJet z)*clockResolvent event T z)

/-- Every original clock-dependent factor contributes to the same nine-constraint flux. -/
def clockSourceSchurFlux (event : DressedEvent) (T : ℝ) (z : ℂ) : Matrix (Fin 9) (Fin 9) ℂ :=
  (-clockNativeNullJet.transpose)*dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock z) z T*
      clockResolvent event T z*clockNativeNull z+
    clockNativeCokernel z*dressedCoincidentClockJet (anchorEvent event) 0 z T*
      clockResolvent event T z*clockNativeNull z+
    clockNativeCokernel z*dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock z) z T*
      originalInverseFlux event T z*clockNativeNull z+
    clockNativeCokernel z*dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock z) z T*
      clockResolvent event T z*clockNativeNullJet

/-- The full source Schur derivative retains both moving constraint maps, the quantum memory jet and full inverse flux. -/
theorem clock_source_schur_flux_generated (event : DressedEvent) (T : ℝ) (positive : 0<T) (small : T≤1) :
    ∀ᶠz in 𝓝 (3:ℂ),HasDerivAt (clockSchur event T) (clockSourceSchurFlux event T z) z := by
  filter_upwards [clock_resolvent_derivative event T positive small,
    clock_feedback_full_flux event T positive small] with z inverse full
  rw [full] at inverse
  change HasDerivAt (clockResolvent event T) (originalInverseFlux event T z) z at inverse
  have columns:=clock_native_columns_derivative z
  have quantum:=dressed_coincident_clock_jet_generated (anchorEvent event) 0 z T
  have first:=rectangular_product_derivative clockNativeCokernel
    (fun w=>dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock w) w T)
    _ _ z columns.2 quantum
  have second:=rectangular_product_derivative
    (fun w=>clockNativeCokernel w*dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock w) w T)
    (clockResolvent event T) _ _ z first inverse
  have third:=rectangular_product_derivative
    (fun w=>clockNativeCokernel w*dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock w) w T*
      clockResolvent event T w) clockNativeNull _ _ z second columns.1
  have actual:=third.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (clock_schur_original_product event T))
  apply actual.congr_deriv
  simp only [clockSourceSchurFlux,Matrix.add_mul]

end LowEnergy.GaussComposite.ActualDressedSchurClock
