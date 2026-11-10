import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedPhotonFieldResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparedPhotonPoleRead
open SaturationMonoid.PhysicsCore
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumNativePoleTensor PreparationVacuumOriginalGreenFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open SourcePropagationNoetherTime
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonFluxReturn
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedSylvester
open ActualDressedFiniteStaticRead ActualSourcePreparedNoetherPi ActualSourceExplicitEvolutionPolynomial
open Set MeasureTheory
open scoped Topology BigOperators Matrix

private theorem forcing_add (epsilon s : ℝ) (n : PhysicalMomentum)
    (v w : Fin 289 → ℂ) :
    nativeModeForcing epsilon s n (v+w) =
      nativeModeForcing epsilon s n v + nativeModeForcing epsilon s n w := by
  ext i
  simp only [nativeModeForcing, activeForcing, Matrix.mulVec_add, Pi.add_apply]

private theorem forcing_smul (epsilon s : ℝ) (n : PhysicalMomentum)
    (c : ℂ) (v : Fin 289 → ℂ) :
    nativeModeForcing epsilon s n (c • v) = c • nativeModeForcing epsilon s n v := by
  ext i
  simp only [nativeModeForcing, activeForcing, Matrix.mulVec_smul, Pi.smul_apply]

/-- The original independent cofactor reader, with no supplied row or normalizer. -/
def sourcePhotonLeftReaderLinear (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    (Fin 289 → ℂ) →ₗ[ℂ] ℂ where
  toFun := sourcePhotonLeftReader branch epsilon s n
  map_add' := by
    intro v w
    unfold sourcePhotonLeftReader
    rw [forcing_add epsilon s n v w]
    simp only [sourceNativePoleCoefficient, Matrix.mulVec_add, Pi.add_apply, add_div]
  map_smul' := by
    intro c v
    unfold sourcePhotonLeftReader
    rw [forcing_smul epsilon s n c v]
    simp only [sourceNativePoleCoefficient, Matrix.mulVec_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, mul_div_assoc]

def sourcePhotonLeftReaderCLM (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    (Fin 289 → ℂ) →L[ℂ] ℂ :=
  (sourcePhotonLeftReaderLinear branch epsilon s n).toContinuousLinearMap

theorem source_photon_left_reader_original (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (v : Fin 289 → ℂ) :
    sourcePhotonLeftReaderCLM branch epsilon s n v =
      sourcePhotonLeftReader branch epsilon s n v := rfl

def sourcePreparedComplexFieldRead (event : DressedEvent) (transfer : PhysicalMomentum)
    (a : Fin 289 → ℂ) (age r : ℝ) (i : Fin 289) : ℂ :=
  sourcePreparedFiniteRead event transfer (fieldUnit i) age (r • fun j => (a j).re) +
    Complex.I * sourcePreparedFiniteRead event transfer (fieldUnit i) age (r • fun j => (a j).im)

attribute [local irreducible] sourcePreparedFiniteRead dressedSignalMatrix dressedSignalQuadrature
  dressedSignalComplexOperator dressedEulerObserver noetherHistoryOperatorJet
  dressedKinematicPoint dressedNoetherJet finiteConstantFieldSlope

/-- The two actual real field curves generate Pi acting on the mode, with no transpose. -/
theorem source_prepared_complex_field_derivative (event : DressedEvent)
    (transfer : PhysicalMomentum) (a : Fin 289 → ℂ) (age : ℝ) (i : Fin 289) :
    HasDerivAt (fun r => sourcePreparedComplexFieldRead event transfer a age r i)
      ((dressedSignalMatrix event transfer 0 age *ᵥ a) i) 0 := by
  have re := source_prepared_finite_field_derivative event transfer (fun j => (a j).re) age i
  have im := source_prepared_finite_field_derivative event transfer (fun j => (a j).im) age i
  have generated := re.add (im.const_mul Complex.I)
  have original := dressed_static_current event transfer 0 rfl a age i
  have matrix := congrFun (dressed_signal_matrix_actual event transfer 0 age a) i
  have slope :
      (dressedNoetherJet event transfer (fun _ => ⟨fun j => (a j).re,0,0⟩) age i).value +
        Complex.I * (dressedNoetherJet event transfer (fun _ => ⟨fun j => (a j).im,0,0⟩) age i).value =
      (dressedSignalMatrix event transfer 0 age *ᵥ a) i := by
    simp only [dressed_noether_jet_original]
    exact original.symm.trans matrix
  exact generated.congr_deriv slope

private theorem zero_slope (event : DressedEvent) (transfer : PhysicalMomentum)
    (age : ℝ) (i : Fin 289) :
    (dressedNoetherJet event transfer (fun _ => ⟨0,0,0⟩) age i).value = 0 := by
  have generated := source_prepared_finite_field_derivative event transfer 0 age i
  have constant : HasDerivAt (fun r : ℝ => sourcePreparedFiniteRead event transfer
      (fieldUnit i) age (r • (0 : Field289))) 0 0 := by
    simpa only [smul_zero] using hasDerivAt_const (0 : ℝ)
      (sourcePreparedFiniteRead event transfer (fieldUnit i) age 0)
  exact generated.unique constant

private theorem source_matrix_slope (event : DressedEvent) (transfer : PhysicalMomentum)
    (age : ℝ) (i j : Fin 289) :
    dressedSignalMatrix event transfer 0 age i j =
      finiteConstantFieldSlope event transfer (fieldUnit j) age i := by
  have realpart : (fun k => ((Pi.single j 1 : Fin 289 → ℂ) k).re) = fieldUnit j := by
    ext k
    by_cases same : k=j <;> simp [fieldUnit,same]
  have imagpart : (fun k => ((Pi.single j 1 : Fin 289 → ℂ) k).im) = 0 := by
    ext k
    by_cases same : k=j <;> simp [same]
  let read (force : Field289) : ℂ := dressedEulerObserver event
    (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i)
      (fun _ => ⟨force,0,0⟩) age).value
  have zeroRead : read 0 = 0 :=
    (dressed_noether_jet_original event transfer (fun _ => ⟨0,0,0⟩) age i).symm.trans
      (zero_slope event transfer age i)
  have realRead := congrArg read realpart
  have imagRead := (congrArg read imagpart).trans zeroRead
  have actual := dressed_static_current event transfer 0 rfl (Pi.single j 1) age i
  have basis : dressedSignalQuadrature event transfer 0 age (Pi.single j 1) i = read (fieldUnit j) :=
    actual.trans ((congrArg₂ (fun x y : ℂ => x + Complex.I*y) realRead imagRead).trans
      (by simp only [mul_zero, add_zero]))
  have matrix : dressedSignalMatrix event transfer 0 age i j =
      dressedSignalQuadrature event transfer 0 age (Pi.single j 1) i := by
    unfold dressedSignalMatrix
    exact congrFun (dressed_signal_complex_original event transfer 0 age (Pi.single j 1)) i
  exact matrix.trans (basis.trans
    ((finite_constant_field_slope_actual event transfer (fieldUnit j) age i).trans
      (dressed_noether_jet_original event transfer (fun _ => ⟨fieldUnit j,0,0⟩) age i)).symm)

def sourcePreparedModeResponse (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (a : Fin 289 → ℂ) : Fin 289 → ℂ := fun i =>
  ∫t in Ioi (0:ℝ), laplaceWeight lambda t *
    deriv (fun r => sourcePreparedComplexFieldRead event transfer a t r i) 0

theorem source_prepared_mode_response_actual (event : DressedEvent)
    (transfer : PhysicalMomentum) (lambda : ℂ) (positive : 0 < lambda.re)
    (a : Fin 289 → ℂ) :
    sourcePreparedModeResponse event transfer lambda a =
      (fun i j => sourcePreparedPiEntry event transfer lambda i j) *ᵥ a := by
  ext i
  unfold sourcePreparedModeResponse
  simp_rw [(source_prepared_complex_field_derivative event transfer a _ i).deriv]
  change (∫t in Ioi (0:ℝ), laplaceWeight lambda t *
    (∑j, dressedSignalMatrix event transfer 0 t i j * a j)) = _
  calc
    _ = ∫t in Ioi (0:ℝ), ∑j, (laplaceWeight lambda t *
        finiteConstantFieldSlope event transfer (fieldUnit j) t i) * a j := by
      simp_rw [Finset.mul_sum, source_matrix_slope, mul_assoc]
    _ = ∑j, ∫t in Ioi (0:ℝ), (laplaceWeight lambda t *
        finiteConstantFieldSlope event transfer (fieldUnit j) t i) * a j :=
      integral_finsetSum Finset.univ (fun j _ =>
        (finite_static_integrand_integrable event transfer (fieldUnit j) lambda positive i).mul_const (a j))
    _ = ∑j, sourcePreparedPiEntry event transfer lambda i j * a j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, source_prepared_pi_actual event transfer lambda positive i j,
        dressed_static_polarization_finite event transfer lambda positive i j]
    _ = _ := rfl

def sourcePreparedPhotonPoleResponse (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (lambda : ℂ) : ℂ :=
  sourcePhotonLeftReaderCLM branch epsilon s n
    (sourcePreparedModeResponse event transfer lambda
      (sourceNativeFrequencyPolarization branch epsilon s n))

theorem source_prepared_photon_pole_response (event : DressedEvent)
    (transfer : PhysicalMomentum) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) :
    sourcePreparedPhotonPoleResponse event transfer branch epsilon s n lambda =
      sourcePhotonLeftReader branch epsilon s n
        ((fun i j => explicitFullNoetherEntry event transfer lambda i j) *ᵥ
          sourceNativeFrequencyPolarization branch epsilon s n) := by
  unfold sourcePreparedPhotonPoleResponse
  rw [source_prepared_mode_response_actual event transfer lambda positive,
    source_photon_left_reader_original]
  simp_rw [source_prepared_pi_explicit event transfer lambda positive]

/-- Rescaling the source mode and its dual reader together leaves the full response unchanged. -/
theorem source_prepared_pole_mode_scale (event : DressedEvent)
    (transfer : PhysicalMomentum) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (lambda c : ℂ) (positive : 0 < lambda.re) (nonzero : c ≠ 0) :
    c⁻¹ * sourcePhotonLeftReaderCLM branch epsilon s n
        (sourcePreparedModeResponse event transfer lambda
          (c • sourceNativeFrequencyPolarization branch epsilon s n)) =
      sourcePreparedPhotonPoleResponse event transfer branch epsilon s n lambda := by
  unfold sourcePreparedPhotonPoleResponse
  rw [source_prepared_mode_response_actual event transfer lambda positive,
    source_prepared_mode_response_actual event transfer lambda positive,
    Matrix.mulVec_smul, map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]

end LowEnergy.GaussComposite.ActualSourcePreparedPhotonPoleRead
