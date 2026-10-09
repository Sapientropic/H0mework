import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSecondPressurePositiveStorage
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSecondPressureMagneticPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualNonmagneticPressureStorage
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy GaussNativeForm GaussNativePotential SourceCoframeVolume SourceQuantumScalarChart
open SourceScalarPairedTransport SourceScalarVirialBulk SourceScalarGaugeScale
open SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy SourceClockPhiSecondPressure
open SourceScalarInverseBulk SourceClockReflectedForm SourcePhysicalHamiltonianSquare
open SourceClockPhiSecondBulk ActualPhaseBulkSquare ActualScalarPhaseJet
open ActualSecondPressurePositiveStorage ActualSecondPressureMagneticPayment
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair inverseVolumeAction magneticSecondField nonmagneticSecondField
  secondStorage phaseForce phaseCoefficient sourceTime

private theorem lapse_positive:0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem pair_real_left(a:ℝ)(f h:QuantumTest):
    sourcePair ((a:ℂ) • f) h=(a:ℂ)*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_left]
  have hs:starRingEnd ℂ (a:ℂ)=(a:ℂ) := by
    rw [starRingEnd_apply,Complex.star_def,Complex.conj_ofReal]
  rw [hs]

/-- The surviving department generates its own positive storage from the
actual native, gauge, shifted and phase-force slots. -/
def nonmagneticStorage(f:QuantumTest):ℝ :=
  sourceTime 0*scalarForm (inverseVolumeAction f)+
    6*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re+
    2*sourceTime 0*shiftedMoment f+(2/phaseCoefficient)*‖embed (phaseForce f)‖^2

theorem actual_nonmagnetic_storage_nonnegative(f:QuantumTest):0 ≤ nonmagneticStorage f := by
  have hn:=lapse_positive
  have hc:=actual_phase_coefficient_positive
  have hs:0 ≤ scalarForm (inverseVolumeAction f):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have ht:0 ≤ shiftedMoment f:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hg:=original_gauge_kinetic_nonnegative (inverseRootAction f)
  unfold nonmagneticStorage
  positivity

/-- The magnetic price is removed by the exact source decomposition. -/
theorem actual_full_storage_nonmagnetic_split(f:QuantumTest):
    secondStorage f=nonmagneticStorage f+
      12*(sourcePair (inverseRootAction f) (magneticAction (inverseRootAction f))).re := by
  unfold secondStorage nonmagneticStorage
  rw [original_second_pressure_energy]
  ring

private theorem magnetic_inverse_pair(f h:QuantumTest):
    sourcePair f (inverseVolumeAction (magneticAction h))=
      sourcePair (inverseRootAction f) (magneticAction (inverseRootAction h)) := by
  have hc:Commute inverseRootAction magneticAction := by
    unfold magneticAction
    exact inverse_root_real _ _
  rw [←inverse_root_square]
  have hp:sourcePair f (inverseRootAction (inverseRootAction (magneticAction h)))=
      sourcePair (inverseRootAction f) (inverseRootAction (magneticAction h)) := by
    unfold inverseRootAction
    exact multiply_pair _ _ _ _
  rw [hp]
  exact congrArg (sourcePair (inverseRootAction f)) (LinearMap.congr_fun hc.eq h)

private theorem magnetic_inverse_commute:
    Commute magneticAction inverseVolumeAction := by
  unfold magneticAction inverseVolumeAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (magneticPotential z:ℂ) (reciprocalVolume z:ℂ) (f z)

theorem actual_magnetic_second_energy(f:QuantumTest):
    (sourcePair f (magneticSecondField f)).re=
      -24*phaseCoefficient*(sourcePair (inverseRootAction f)
        (magneticAction (inverseRootAction f))).re := by
  have he:magneticSecondField=(-24*(phaseCoefficient:ℂ)) •
      (inverseVolumeAction*magneticAction) := by
    unfold magneticSecondField
    rw [magnetic_inverse_commute.eq]
    module
  rw [he]
  simp only [LinearMap.smul_apply,Module.End.mul_apply,sourcePair,map_smul,inner_smul_right]
  have hp:=magnetic_inverse_pair f f
  simp only [sourcePair] at hp
  rw [hp]
  norm_num [Complex.mul_re,Complex.mul_im]

/-- The vacuum compensation of the surviving field has the same source
coefficient; positivity is generated after exact magnetic removal. -/
theorem actual_nonmagnetic_storage_source(f:QuantumTest):
    nonmagneticStorage f=-(1/(2*phaseCoefficient))*(sourcePair f (nonmagneticSecondField f)).re+
      (sourceTime 0*‖vacuum‖^2/2)*‖embed f‖^2 := by
  have h:=actual_second_storage_source f
  rw [actual_native_phase_second_pressure_split] at h
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Complex.add_re] at h
  have hm:=actual_magnetic_second_energy f
  simp only [sourcePair] at hm
  rw [hm,actual_full_storage_nonmagnetic_split] at h
  have hc:phaseCoefficient≠0:=actual_phase_coefficient_positive.ne'
  simp only [sourcePair] at h ⊢
  field_simp [hc] at h ⊢
  linear_combination (norm:=ring_nf) h

theorem actual_nonmagnetic_storage_native_price(f:QuantumTest):
    sourceTime 0*scalarForm (inverseVolumeAction f)+2*sourceTime 0*shiftedMoment f ≤
      nonmagneticStorage f := by
  have hc:=actual_phase_coefficient_positive
  have hg:=original_gauge_kinetic_nonnegative (inverseRootAction f)
  have hf:0 ≤ (2/phaseCoefficient)*‖embed (phaseForce f)‖^2:=by positivity
  unfold nonmagneticStorage
  linarith only [hg,hf]

private theorem magnetic_second_pair(f h:QuantumTest):
    sourcePair f (magneticSecondField h)=sourcePair (magneticSecondField f) h := by
  have he:magneticSecondField=(-24*(phaseCoefficient:ℂ)) •
      (inverseVolumeAction*magneticAction) := by
    unfold magneticSecondField
    rw [magnetic_inverse_commute.eq]
    module
  have hm(a b:QuantumTest):sourcePair a (magneticAction b)=sourcePair (magneticAction a) b := by
    unfold magneticAction
    exact multiply_pair _ _ _ _
  have hu(a b:QuantumTest):sourcePair a (inverseVolumeAction b)=sourcePair (inverseVolumeAction a) b := by
    unfold inverseVolumeAction
    exact multiply_pair _ _ _ _
  rw [he]
  have hc:(-24*(phaseCoefficient:ℂ))=((-24*phaseCoefficient:ℝ):ℂ):=by push_cast;rfl
  rw [hc]
  simp only [LinearMap.smul_apply,Module.End.mul_apply,pair_real_left,sourcePair,map_smul,inner_smul_right]
  simp only [sourcePair] at hm hu
  rw [hu,hm]
  exact congrArg (fun v:QuantumTest=>((-24*phaseCoefficient:ℝ):ℂ)*inner ℂ (embed v) (embed h))
    (LinearMap.congr_fun magnetic_inverse_commute.eq f)

theorem actual_nonmagnetic_source_pair(f h:QuantumTest):
    sourcePair f (nonmagneticSecondField h)=sourcePair (nonmagneticSecondField f) h := by
  have hp:=actual_second_source_pair f h
  rw [actual_native_phase_second_pressure_split] at hp
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_left,inner_add_right] at hp
  have hm:=magnetic_second_pair f h
  simp only [sourcePair] at hm
  rw [hm] at hp
  simpa only [sourcePair] using add_left_cancel hp

def nonmagneticStorageAction:End :=
  ((-(1/(2*phaseCoefficient)):ℝ):ℂ) • nonmagneticSecondField+
    ((sourceTime 0*‖vacuum‖^2/2:ℝ):ℂ) • (1:End)

theorem actual_nonmagnetic_storage_action(f:QuantumTest):
    (sourcePair f (nonmagneticStorageAction f)).re=nonmagneticStorage f := by
  rw [actual_nonmagnetic_storage_source]
  unfold nonmagneticStorageAction
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hn:(inner ℂ (embed f) (embed f)).re=‖embed f‖^2:=by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  rw [hn]

private theorem storage_pair(f h:QuantumTest):
    sourcePair f (nonmagneticStorageAction h)=sourcePair (nonmagneticStorageAction f) h := by
  unfold nonmagneticStorageAction
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,sourcePair,map_add,map_smul,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right]
  have hr(a:ℝ):starRingEnd ℂ (a:ℂ)=(a:ℂ) := by
    rw [starRingEnd_apply,Complex.star_def,Complex.conj_ofReal]
  rw [hr,hr]
  have hs:=actual_nonmagnetic_source_pair f h
  simp only [sourcePair] at hs
  rw [hs]

private theorem storage_real_young(f h:QuantumTest):
    |(sourcePair f (nonmagneticStorageAction h)).re| ≤
      (nonmagneticStorage f+nonmagneticStorage h)/2 := by
  have hp:=actual_nonmagnetic_storage_nonnegative (f+h)
  have hm:=actual_nonmagnetic_storage_nonnegative (f-h)
  rw [←actual_nonmagnetic_storage_action] at hp hm
  have hc:=congrArg Complex.re (pair_conjugate f (nonmagneticStorageAction h))
  rw [←storage_pair h f] at hc
  simp only [Complex.conj_re] at hc
  simp only [sourcePair,map_add,map_sub,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    Complex.add_re,Complex.sub_re] at hp hm
  have hf:=actual_nonmagnetic_storage_action f
  have hh:=actual_nonmagnetic_storage_action h
  simp only [sourcePair] at hf hh hc
  rw [hf,hh,←hc] at hp hm
  simp only [sourcePair]
  rw [abs_le]
  constructor <;> linarith only [hp,hm]

/-- Both real and imaginary pressure interference receive the surviving
department's own source price, after the magnetic sector is removed. -/
theorem actual_nonmagnetic_storage_complex_price(f h:QuantumTest):
    ‖sourcePair f (nonmagneticStorageAction h)‖ ≤ nonmagneticStorage f+nonmagneticStorage h := by
  have hr:=storage_real_young f h
  have hi:=storage_real_young f (Complex.I • h)
  have hscale:nonmagneticStorage (Complex.I • h)=nonmagneticStorage h := by
    rw [←actual_nonmagnetic_storage_action,←actual_nonmagnetic_storage_action]
    simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have he:sourcePair f (nonmagneticStorageAction (Complex.I • h))=
      Complex.I*sourcePair f (nonmagneticStorageAction h) := by
    simp only [map_smul,sourcePair,inner_smul_right]
  rw [hscale,he] at hi
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,abs_neg] at hi
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith only [hr,hi])

end LowEnergy.ActualNonmagneticPressureStorage
