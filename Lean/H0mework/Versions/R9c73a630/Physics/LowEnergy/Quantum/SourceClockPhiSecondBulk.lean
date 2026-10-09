import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarVirialBulk
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockRadiusAffineCutoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiSecondBulk
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeEnergy GaussNativeForm GaussNativeMatter GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceDilationRemainder
open SourceScalarFlatJoint SourceScalarRadialContact SourceScalarVirialCurrent SourceScalarVirialBulk
open SourceGaugeRadialCurrent SourceGaugeRadialPair SourceScalarGaugeScale
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarPairedTransport SourceMixedNativeReturn SourceClockYukawaCubicCurrent SourceClockRadiusAffineCutoff
open SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariationDensity
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

/-- Two genuine source derivations retain the positive magnetic sector. -/
def secondJet : End →ₗ[ℂ] End :=
  (LinearMap.id-SourceScalarGaugeScale.deltaGauge).comp
    (SourceScalarVirialBulk.deltaPhi-SourceScalarGaugeScale.deltaGauge)

def secondBulk : End := secondJet diagonalAction+(1/2 : ℂ) • vacuumConstantAction

private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 1) (hz : γ 1=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) :
    fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 1 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem euler_multiplier (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (flow : ℝ → SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z))
    (hg : ∀ z,HasDerivAt (fun r => flow r z) (e z) 1) (h1 : ∀ z,flow 1 z=z)
    (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (law : ∀ f z,A f z=B z (f z)) (hinv : ∀ r z,B (flow r z)=B z) : E*A-A*E=0 := by
  apply sub_eq_zero.mpr
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change E (A f) z=A (E f) z
  rw [hE,law,hE]
  have h := invariant_derivative (E := SourceCoordinateSlice) (V := FockFiber)
    ((B z).restrictScalars ℝ) f (A f) (fun r => flow r z) z (e z)
    (hg z) (h1 z) ((f.contDiff.differentiable (by simp)) z) (((A f).contDiff.differentiable (by simp)) z)
    (fun r => by rw [law,hinv]; rfl)
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using! h

private theorem gauge_multiplier (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (law : ∀ f z,A f z=B z (f z)) (hinv : ∀ r z,B (gaugeScale r z)=B z) : deltaGauge A=0 :=
  euler_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply
    (fun z => gauge_scale_derivative z 1) gauge_scale_one A B law hinv

private theorem gauge_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv : ∀ r z,c (gaugeScale r z)=c z) : deltaGauge (multiply c hc)=0 :=
  gauge_multiplier _ (fun z => (c z : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _ => rfl) (fun r z => congrArg (fun x : ℝ => (x : ℂ) • ContinuousLinearMap.id ℂ FockFiber) (hinv r z))

private theorem centered_gauge : deltaGauge centeredAction=0 := by
  unfold centeredAction
  exact gauge_real _ _ (fun _ _ => rfl)
private theorem vacuum_linear_gauge : deltaGauge vacuumLinearAction=0 := by
  unfold vacuumLinearAction
  exact gauge_real _ _ (fun _ _ => rfl)

private theorem vacuum_completion :
    (2 : ℂ) • centeredAction-(2 : ℂ) • vacuumLinearAction+(1/2 : ℂ) • vacuumConstantAction=
      (2 : ℂ) • shiftedAction := by
  have h := original_positive_bulk
  rw [positiveBulk,original_filtered_bulk] at h
  linear_combination (norm := module) (1/4 : ℂ) • h

/-- The full spatial and matter terms cancel at their actual source weights. -/
theorem original_second_bulk_source :
    secondBulk=(-2 : ℂ) • scalarKinetic+(6 : ℂ) • gaugeKinetic+
      (2 : ℂ) • shiftedAction+(12 : ℂ) • magneticAction := by
  change (deltaPhi diagonalAction-deltaGauge diagonalAction)-
    deltaGauge (deltaPhi diagonalAction-deltaGauge diagonalAction)+
      (1/2 : ℂ) • vacuumConstantAction=_
  rw [original_scalar_gauge_current]
  simp only [map_add,map_sub,map_smul,original_scalar_kinetic_gauge,
    original_gauge_kinetic_gauge,centered_gauge,vacuum_linear_gauge,
    original_magnetic_gauge,original_matter_gauge]
  linear_combination (norm := module) vacuum_completion

private theorem metric_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → E) :
    (∑ i : Fin 3,∑ j : Fin 3,(A*A.transpose) i j*inner ℝ (b i) (b j))=
      ∑ k : Fin 3,‖∑ i : Fin 3,A i k • b i‖^2 := by
  simp only [←real_inner_self_eq_norm_sq,Matrix.mul_apply,Matrix.transpose_apply]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  simp only [Fin.sum_univ_three]
  ring

private theorem magnetic_nonnegative (z : physicalChart) : 0 ≤ magneticPotential z.val := by
  rw [magneticPotential,inverseSpatial,metric_square]
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hs : 0<sourceSigma :=
    SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource.legacy.sigma_pos
  exact mul_nonneg (div_nonneg (volume_pos z).le (by positivity))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem scalar_multiplier_sign (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sign : ℝ)
    (hs : ∀ z : physicalChart,0 ≤ sign*c z.val) (f : QuantumTest) :
    0 ≤ sign*(sourcePair f (multiply c hc f)).re := by
  rw [sourcePair_integral]
  have hr : (∫ z, densityPair f (multiply c hc f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫ z, (densityPair f (multiply c hc f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only using! (integral_re (densityPair_integrable f (multiply c hc f))).symm
  rw [hr,←MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_nonneg
  intro z
  change 0 ≤ sign*(densityPair f (multiply c hc f) z).re
  have he : densityPair f (multiply c hc f) z=(c z : ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  by_cases hz : z∈physicalChart
  · have hp : 0 ≤ (densityPair f f z).re := by
      change 0 ≤ (inner ℂ (GaussFockWeights.weight (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z)).re
      have hw := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
        (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
      have hp := (sq_nonneg ‖GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z) (f z)‖).trans_eq hw.symm
      simpa only using! hp
    simpa only [mul_assoc] using mul_nonneg (hs ⟨z,hz⟩) hp
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,mul_zero]
    exact le_refl _

/-- Positivity includes the actual inverse spatial metric and every Number density. -/
theorem original_magnetic_nonnegative (f : QuantumTest) :
    0 ≤ (sourcePair f (magneticAction f)).re := by
  have h : 0 ≤ (1 : ℝ)*(sourcePair f (magneticAction f)).re := by
    unfold magneticAction
    exact scalar_multiplier_sign _ _ 1 (fun z => by simpa only [one_mul] using magnetic_nonnegative z) f
  simpa only [one_mul] using h

private theorem second_pair (f : QuantumTest) :
    (sourcePair f (secondBulk f)).re=
      -2*(sourcePair f (scalarKinetic f)).re+6*(sourcePair f (gaugeKinetic f)).re+
      2*(sourcePair f (shiftedAction f)).re+12*(sourcePair f (magneticAction f)).re := by
  rw [original_second_bulk_source]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right]
  norm_num only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,sub_zero]

/-- Each native positive form is paid by one complete second source current. -/
theorem original_second_bulk_payment (f : QuantumTest) :
    0 ≤ (sourcePair f (secondBulk f)).re ∧
    -2*(sourcePair f (scalarKinetic f)).re ≤ (sourcePair f (secondBulk f)).re ∧
    6*(sourcePair f (gaugeKinetic f)).re ≤ (sourcePair f (secondBulk f)).re ∧
    2*(sourcePair f (shiftedAction f)).re ≤ (sourcePair f (secondBulk f)).re ∧
    12*(sourcePair f (magneticAction f)).re ≤ (sourcePair f (secondBulk f)).re := by
  rw [second_pair]
  have hK := original_scalar_kinetic_nonpositive f
  have hG := original_gauge_kinetic_nonnegative f
  have hV := original_shifted_nonnegative f
  have hB := original_magnetic_nonnegative f
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The complete second compression defect stays in the same source current. -/
theorem actual_second_compression_source (F : Index) :
    secondJet (compressionCore F)+secondJet (defectAction F)+
      (1/2 : ℂ) • vacuumConstantAction=secondBulk := by
  rw [←map_add]
  have h : compressionCore F+defectAction F=diagonalAction := by
    unfold defectAction
    abel
  rw [h]
  rfl

def responsePrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  let v := phiResponseCore m ell F z hz g
  (sourcePair v ((secondJet (compressionCore F)+secondJet (defectAction F)+
    (1/2 : ℂ) • vacuumConstantAction) v)).re

/-- All four positive slots apply to the literal homogeneous-radius response at the same F. -/
theorem actual_phi_second_bulk_payment (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    let v := phiResponseCore m ell F z hz g
    0 ≤ responsePrice m ell F z hz g ∧
    -2*(sourcePair v (scalarKinetic v)).re ≤ responsePrice m ell F z hz g ∧
    6*(sourcePair v (gaugeKinetic v)).re ≤ responsePrice m ell F z hz g ∧
    2*(sourcePair v (shiftedAction v)).re ≤ responsePrice m ell F z hz g ∧
    12*(sourcePair v (magneticAction v)).re ≤ responsePrice m ell F z hz g := by
  dsimp only [responsePrice]
  rw [actual_second_compression_source]
  exact original_second_bulk_payment _

end LowEnergy.SourceClockPhiSecondBulk
