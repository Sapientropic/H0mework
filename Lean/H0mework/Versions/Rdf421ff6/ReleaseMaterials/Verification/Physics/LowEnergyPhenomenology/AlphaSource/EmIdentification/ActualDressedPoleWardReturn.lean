import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPoleSourceMode
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeConstraint
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPoleWardMode
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumGaugeSourceInjection SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedFrequencyHalf ActualDressedCorrectedGreen ActualDressedCorrectedElectronRead
open ActualDressedUniformMaterialCoefficients LowEnergy.GaussComposite.ActualDressedVisiblePole ActualEMDressedConstraint ActualEMDressedSchur
open LowEnergy.ActualDressedVisiblePole ActualEMCurrentSplit ActualEMCarrierOwn PhysicalEMGaugeRealization
open ActualDressedNativeConstraint ActualDressedPhaseWard ActualDressedPencil ActualEMAction
open Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact PreparationVacuumCurrentSignalOperator
open Filter MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] frequencyHalfPolarization frequencyResponsePencil commonClearedPencil
  commonDenominator emInsertion sourceCokernel phaseSignalRead emGaugeField

def modeEMCurrent (v : Fin 289 → ℂ) : Fin 4 → ℂ := emCurrent v

/-- This classifies the generated EM gauge read; a nonzero read alone is not a propagation identity. -/
inductive ModeEMDisposition (v : Fin 289 → ℂ) : Type
  | noEM (vanishes : modeEMCurrent v=0)
  | coupled (visible : modeEMCurrent v≠0)

def sourceModeEMDisposition (v : Fin 289 → ℂ) : ModeEMDisposition v := by
  classical
  exact if zero : modeEMCurrent v=0 then .noEM zero else .coupled zero

/-- Original real and imaginary quadratures of this same full mode, with the coordinate Gram paid once. -/
def modeEMWeight (v : Fin 289 → ℂ) (imaginary : Bool) (mu : Fin 4) : ℝ :=
  if imaginary then (emCoordinateCurrent v mu).im else (emCoordinateCurrent v mu).re

def modeEMGauge (v : Fin 289 → ℂ) (imaginary : Bool) (nu : Fin 4) :=
  ∑mu : Fin 4, modeEMWeight v imaginary mu •
    (PreparationVacuumMixedFieldReturn.sourceField (emGaugeField mu)).gauge nu

def modeEMConnection (v : Fin 289 → ℂ) (imaginary : Bool) (nu : Fin 4) :=
  ∑mu : Fin 4, (modeEMWeight v imaginary mu : ℂ) •
    Electromagnetic.CanonicalCoframe.connectionDirection
      (PreparationVacuumMixedFieldReturn.sourceField (emGaugeField mu)) nu

theorem source_mode_em_gauge (v : Fin 289 → ℂ) (imaginary : Bool) (nu : Fin 4) :
    modeEMGauge v imaginary nu=modeEMWeight v imaginary nu • emDirection := by
  unfold modeEMGauge
  simp_rw [em_field_gauge]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem source_mode_em_connection (v : Fin 289 → ℂ) (imaginary : Bool) (nu : Fin 4) :
    modeEMConnection v imaginary nu=(modeEMWeight v imaginary nu : ℂ) •
      Quantum.operatorMatrix emGaugeAction := by
  unfold modeEMConnection
  simp_rw [em_field_connection]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem source_mode_full_decomposition (v : Fin 289 → ℂ) :
    v=emInsertion*ᵥemCoordinateCurrent v+emCurrentResidual v ∧
      emInsertion.transpose*ᵥemCurrentResidual v=0 := by
  exact ⟨(em_current_complete v).trans (congrArg (fun x => x+emCurrentResidual v)
    (em_current_force_insertion v)), em_current_residual_zero v⟩

private theorem sheet_pencil_real (event : DressedEvent) (eps sigma s : ℝ) (n : PhysicalMomentum) :
    (sourceSheetPencil event eps sigma n).map (Polynomial.eval (s : ℂ))=
      (commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma s)) := by
  ext i j
  exact sheet_slice_eval eps sigma s _

/-- At a real source sheet point, generated positive damping removes the clearing factor before the full physical equation is read. -/
theorem actual_real_pole_physical_kernel (event : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : ActualCompositeFieldCurrent.CompositeLeg)
    (positive : 0<sigma)
    (root : (s : ℂ) ∈ visibleRoots (sheetReadFraction event eps sigma n pd ps dL dR sL sR)) :
    frequencyResponsePencil event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
      (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥ
        actualVisibleMode event eps sigma n ps sL sR (s : ℂ)=0 := by
  have kernel := (actual_visible_full_mode event eps sigma n pd ps dL dR sL sR (s : ℂ) root).2
  rw [sheet_pencil_real, ← actual_common_ir_pencil_clear event n eps sigma s positive,
    Matrix.smul_mulVec] at kernel
  exact (smul_eq_zero.mp kernel).resolve_left
    (ActualDressedUniformClockNonzero.actual_common_ir_denominator_nonzero event n eps sigma s positive)

private theorem physical_kernel_balance (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (v : Fin 289 → ℂ) (positive : 0<sigma)
    (kernel : frequencyResponsePencil event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
      (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv=0) :
    emOriginalJacobi (frequencyRay eps s n)*ᵥv=(sigma : ℂ) •
      (frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv) := by
  rw [damped_source_sheet_response event eps s sigma n positive, Matrix.sub_mulVec, Matrix.smul_mulVec] at kernel
  exact sub_eq_zero.mp kernel

private theorem physical_kernel_nine (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (v : Fin 289 → ℂ) (positive : 0<sigma)
    (kernel : frequencyResponsePencil event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
      (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv=0) :
    sourceCokernel (frequencyRay eps s n)
      (frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv)=0 := by
  have balance := congrArg (sourceCokernel (frequencyRay eps s n))
    (physical_kernel_balance event eps sigma s n v positive kernel)
  have original : sourceCokernel (frequencyRay eps s n) (emOriginalJacobi (frequencyRay eps s n)*ᵥv)=0 := by
    rw [em_jacobi_source]
    exact (source_compatibility_nine _ _).mp (source_compatibility_euler _ _)
  rw [original, map_smul] at balance
  exact (smul_eq_zero.mp balance.symm).resolve_left (Complex.ofReal_ne_zero.mpr positive.ne')

private theorem real_clock_domain (eps sigma s : ℝ) (n : PhysicalMomentum) (positive : 0<sigma) :
    sourceClockGrowth (frequencyRay eps s n)<(dampedFourierClock (sourceFrequency eps s) sigma).re := by
  have same : sourceFrequency eps s=s*eps^2 := by unfold sourceFrequency; ring
  simpa only [frequencyRay, same] using
    damped_fourier_source_domain (sourceFrequency eps s) sigma ((eps^2 : ℝ) • n) positive

/-- The generated mode enters all original nine quantum Ward histories, including their reference deviation and both real quadratures. -/
theorem actual_real_pole_nine_ward (event : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : ActualCompositeFieldCurrent.CompositeLeg)
    (positive : 0<sigma)
    (root : (s : ℂ) ∈ visibleRoots (sheetReadFraction event eps sigma n pd ps dL dR sL sR)) (j : Fin 9) :
    let v := actualVisibleMode event eps sigma n ps sL sR (s : ℂ)
    Tendsto (fun T : ℝ => ∫t in (0 : ℝ)..T, laplaceWeight (dampedFourierClock (sourceFrequency eps s) sigma) t*
      (nativeConstraintHistory event ((eps^2 : ℝ) • n) (frequencyRay eps s n) j v t-
        nativeConstraintDeviation event ((eps^2 : ℝ) • n) (frequencyRay eps s n) j v t))
      atTop (𝓝 0) := by
  dsimp only
  let v := actualVisibleMode event eps sigma n ps sL sR (s : ℂ)
  have domain := real_clock_domain eps sigma s n positive
  have window := frequency_polarization_window_limit event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
    (dampedFourierClock (sourceFrequency eps s) sigma) domain
  have continuity : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ =>
      sourceCokernel (frequencyRay eps s n) (M*ᵥv) j) := by
    exact (continuous_apply j).comp ((sourceCokernel (frequencyRay eps s n)).toContinuousLinearMap.continuous.comp
      (by unfold Matrix.mulVec dotProduct; fun_prop))
  have limit := (continuity.tendsto _).comp window
  have kernel := actual_real_pole_physical_kernel event eps sigma s n pd ps dL dR sL sR positive root
  rw [physical_kernel_nine event eps sigma s n v positive kernel, Pi.zero_apply] at limit
  simpa only [Function.comp_def, source_constraint_native_history, v] using limit

/-- The complete held phase Ward reaches the original halfline quantum response without separately discarding scalar or deviation terms. -/
theorem actual_phase_half_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4 → ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re)
    (v : Fin 289 → ℂ) :
    Tendsto (fun T : ℝ => ∫t in (0 : ℝ)..T, laplaceWeight lambda t*
      (phaseSignalRead .ward event transfer p v t-phaseSignalRead .scalar event transfer p v t-
        phaseSignalRead .deviation event transfer p v t)) atTop
      (𝓝 (((gaugeScale/2 : ℝ) : ℂ)*dotProduct (fun j => (sourceModeField j : ℂ))
        (frequencyHalfPolarization event transfer p lambda*ᵥv))) := by
  have window := frequency_polarization_window_limit event transfer p lambda off
  have continuity : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ =>
      ((gaugeScale/2 : ℝ) : ℂ)*dotProduct (fun j => (sourceModeField j : ℂ)) (M*ᵥv)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have limit := (continuity.tendsto _).comp window
  simpa only [Function.comp_def, dotProduct, phase_window_polarization_return] using limit

/-- The same full corrected response drives the original phase Ward; its source term is the actual charged-input current. -/
theorem actual_corrected_probe_phase_balance (event : DressedEvent) (eps sigma s : ℝ)
    (n ps : PhysicalMomentum) (sL sR : ActualCompositeFieldCurrent.CompositeLeg)
    (positive : 0<sigma) (regular : correctedDet event eps s sigma n≠0) :
    let v := correctedProbeResponse event eps s sigma n ps sL sR
    Tendsto (fun T : ℝ => (sigma : ℂ)*(∫t in (0 : ℝ)..T,
      laplaceWeight (dampedFourierClock (sourceFrequency eps s) sigma) t*
      (phaseSignalRead .ward event ((eps^2 : ℝ) • n) (frequencyRay eps s n) v t-
        phaseSignalRead .scalar event ((eps^2 : ℝ) • n) (frequencyRay eps s n) v t-
        phaseSignalRead .deviation event ((eps^2 : ℝ) • n) (frequencyRay eps s n) v t))) atTop
      (𝓝 (((gaugeScale/2 : ℝ) : ℂ)*
        (dotProduct (fun j => (sourceModeField j : ℂ)) (emOriginalJacobi (frequencyRay eps s n)*ᵥv)-
          dotProduct (fun j => (sourceModeField j : ℂ)) (ActualCompositeFieldCurrent.compositeCurrent ps sL sR)))) := by
  dsimp only
  let v := correctedProbeResponse event eps s sigma n ps sL sR
  have domain := real_clock_domain eps sigma s n positive
  have limit := (actual_phase_half_return event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
    (dampedFourierClock (sourceFrequency eps s) sigma) domain v).const_mul (sigma : ℂ)
  have equation := actual_corrected_probe_equation event eps s sigma n ps sL sR positive regular
  rw [damped_source_sheet_response event eps s sigma n positive, Matrix.sub_mulVec, Matrix.smul_mulVec] at equation
  have balance := sub_eq_iff_eq_add.mp equation
  have observed := congrArg (fun a : Fin 289 → ℂ => dotProduct (fun j => (sourceModeField j : ℂ)) a) balance
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at observed
  have value : ((gaugeScale/2 : ℝ) : ℂ)*
      (dotProduct (fun j => (sourceModeField j : ℂ)) (emOriginalJacobi (frequencyRay eps s n)*ᵥv)-
        dotProduct (fun j => (sourceModeField j : ℂ)) (ActualCompositeFieldCurrent.compositeCurrent ps sL sR))=
      (sigma : ℂ)*(((gaugeScale/2 : ℝ) : ℂ)*dotProduct (fun j => (sourceModeField j : ℂ))
        (frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
          (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv)) := by
    rw [observed]
    ring
  rw [value]
  exact limit

inductive PoleClearingDisposition (d : ℂ[X]) (a : ℂ) : Type
  | singular (clearing_zero : d.eval a=0)
  | regular (clearing_nonzero : d.eval a≠0)

def sourcePoleClearingDisposition (d : ℂ[X]) (a : ℂ) : PoleClearingDisposition d a := by
  classical
  exact if zero : d.eval a=0 then .singular zero else .regular zero

/-- A source pole carries a generated full homogeneous mode and the original EM/clearing branches, rather than a photon label. -/
structure FullPoleWardMode (event : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : ActualCompositeFieldCurrent.CompositeLeg) (a : ℂ) where
  mode : Fin 289 → ℂ
  generated : mode=actualVisibleMode event eps sigma n ps sL sR a
  nonzero : mode≠0
  homogeneous : (sourceSheetPencil event eps sigma n).map (Polynomial.eval a)*ᵥmode=0
  electromagnetic : ModeEMDisposition mode
  clearing : PoleClearingDisposition (sheetSlice eps sigma (commonDenominator event n)) a
  preparations : PreparedProbe dL ∧ PreparedProbe dR ∧ PreparedProbe sL ∧ PreparedProbe sR
  complete : mode=emInsertion*ᵥemCoordinateCurrent mode+emCurrentResidual mode
  residual : emInsertion.transpose*ᵥemCurrentResidual mode=0
  real_physical : ∀s : ℝ, 0<sigma → a=(s : ℂ) →
    frequencyResponsePencil event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
      (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥmode=0

def actualPoleWardMode (event : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : ActualCompositeFieldCurrent.CompositeLeg) (a : ℂ)
    (root : a ∈ visibleRoots (sheetReadFraction event eps sigma n pd ps dL dR sL sR)) :
    FullPoleWardMode event eps sigma n pd ps dL dR sL sR a := by
  let v := actualVisibleMode event eps sigma n ps sL sR a
  have paid := actual_visible_full_mode event eps sigma n pd ps dL dR sL sR a root
  refine ⟨v,rfl,paid.1,paid.2,sourceModeEMDisposition v,
    sourcePoleClearingDisposition _ a,
    ⟨actual_prepared_probe dL,actual_prepared_probe dR,actual_prepared_probe sL,actual_prepared_probe sR⟩,
    (source_mode_full_decomposition v).1,(source_mode_full_decomposition v).2,?_⟩
  intro s positive same
  subst a
  exact actual_real_pole_physical_kernel event eps sigma s n pd ps dL dR sL sR positive root

/-- Every canonical root is consumed with its own membership proof; no caller chooses a root or a simple-pole certificate. -/
def sourcePoleWardModes (event : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : ActualCompositeFieldCurrent.CompositeLeg) :
    Option (Multiset (Σa : ℂ, FullPoleWardMode event eps sigma n pd ps dL dR sL sR a)) := by
  classical
  exact if sheetDeterminant event eps sigma n=0 then none else some
    ((visibleRoots (sheetReadFraction event eps sigma n pd ps dL dR sL sR)).attach.map
      (fun a => ⟨a.val, actualPoleWardMode event eps sigma n pd ps dL dR sL sR a.val a.property⟩))

end LowEnergy.GaussComposite.ActualDressedPoleWardMode
