import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarBalancedForce
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceMatterForceAbsorption
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy GaussMatterCore
open GaussHistoryHilbert GaussLiveMomentum SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy SourceScalarVirialBulk
open SourceScalarBalancedForce SourceElectricColumns SourceElectricCompletedSquare
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] scalarKinetic gaugeKinetic matterAction inverseVolumeAction inverseRootAction

private theorem matter_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute matterAction (multiply c hc) := by
  unfold matterAction
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (GaussQuantumMultiplier.quantized (localMatrix i b z)) (c z : ℂ) (f z)

private theorem pair_right_sub (X Y Z : LieIndex → Fin 3 → QuantumTest) (c : ℂ) :
    gaugePair X (fun a i => Y a i-c • Z a i)=gaugePair X Y-c*gaugePair X Z := by
  simp only [gaugePair,sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right,
    Finset.sum_sub_distrib,Finset.mul_sum]

private theorem matter_pair_real (X : LieIndex → Fin 3 → QuantumTest) :
    (gaugePair X (fun a i => matterAction (X a i))).im=0 := by
  have h := gauge_pair_conjugate X (fun a i => matterAction (X a i))
  have he : gaugePair (fun a i => matterAction (X a i)) X=
      gaugePair X (fun a i => matterAction (X a i)) := by
    unfold gaugePair
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [←GaussMatterCore.matter_pair]
    exact congrArg (sourcePair (X a i))
      (LinearMap.congr_fun (matter_real _ _).eq (X a j))
  rw [he] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

private theorem matter_commutator_form (f : QuantumTest) :
    (sourcePair f ((gaugeKinetic*matterAction-matterAction*gaugeKinetic) f)).im=
      -(gaugePair (fun a i => column i a f)
        (fun a i => matterContact (gaugeDirection i a) f)).re := by
  have he : (fun a i => column i a (matterAction f))=
      (fun a i => matterAction (column i a f)-Complex.I • matterContact (gaugeDirection i a) f) := by
    funext a i
    simpa only [column,neg_smul,sub_eq_add_neg] using original_matter_momentum (gaugeDirection i a) f
  have h := gauge_kinetic_columns f (matterAction f)
  rw [he,pair_right_sub] at h
  have hi := congrArg Complex.im h
  have hz := matter_pair_real (fun a i => column i a f)
  have hp : sourcePair f (matterAction (gaugeKinetic f))=
      star (sourcePair f (gaugeKinetic (matterAction f))) := by
    rw [GaussMatterCore.matter_pair,←pair_conjugate,gaugeKinetic_pair]
    rfl
  simp only [Complex.sub_im,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,
    Complex.re_ofNat,Complex.im_ofNat,add_zero] at hi
  simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
  change (sourcePair f (gaugeKinetic (matterAction f))-sourcePair f (matterAction (gaugeKinetic f))).im=_
  rw [hp,Complex.sub_im,Complex.star_def,Complex.conj_im]
  linarith

private theorem inverse_root_matter : Commute inverseRootAction matterAction := by
  unfold inverseRootAction
  exact (matter_real _ _).symm

private theorem inverse_root_commutator :
    Commute inverseRootAction (gaugeKinetic*matterAction-matterAction*gaugeKinetic) :=
  (inverse_root_electric.mul_right inverse_root_matter).sub_right
    (inverse_root_matter.mul_right inverse_root_electric)

/-- The actual matter part of the complete original bulk current. -/
def matterBulkCurrent : End := (-36 : ℂ) •
  (inverseVolumeAction*(gaugeKinetic*matterAction-matterAction*gaugeKinetic))

/-- This positive quantity has only the source's zeroth-order coframe/CAR contacts. -/
def contactEnergy (f : QuantumTest) : ℝ :=
  (gaugePair (fun a i => matterContact (gaugeDirection i a) (inverseRootAction f))
    (fun a i => matterContact (gaugeDirection i a) (inverseRootAction f))).re

theorem contact_energy_nonnegative (f : QuantumTest) : 0 ≤ contactEnergy f :=
  gauge_pair_nonneg _

/-- True weighted adjoints turn the entire matter current into the original electric/contact cross form. -/
theorem original_matter_current_form (f : QuantumTest) :
    (sourcePair f (matterBulkCurrent f)).im/2=
      18*(gaugePair (fun a i => column i a (inverseRootAction f))
        (fun a i => matterContact (gaugeDirection i a) (inverseRootAction f))).re := by
  have hs : sourcePair f (inverseVolumeAction ((gaugeKinetic*matterAction-matterAction*gaugeKinetic) f))=
      sourcePair (inverseRootAction f) ((gaugeKinetic*matterAction-matterAction*gaugeKinetic) (inverseRootAction f)) := by
    rw [←inverse_root_square]
    have hp (p q : QuantumTest) : sourcePair p (inverseRootAction q)=sourcePair (inverseRootAction p) q := by
      unfold inverseRootAction
      exact multiply_pair _ _ _ _
    rw [hp]
    exact congrArg (sourcePair (inverseRootAction f)) (LinearMap.congr_fun inverse_root_commutator.eq f)
  have h := matter_commutator_form (inverseRootAction f)
  simp only [matterBulkCurrent,LinearMap.smul_apply,Module.End.mul_apply,sourcePair,map_smul,inner_smul_right]
  change ((-36 : ℂ)*sourcePair f (inverseVolumeAction ((gaugeKinetic*matterAction-matterAction*gaugeKinetic) f))).im/2=_
  rw [hs,Complex.mul_im,h]
  norm_num
  ring

private theorem pair_real_expansion (X Y : LieIndex → Fin 3 → QuantumTest) (r : ℝ) :
    (gaugePair (fun a i => (r : ℂ) • X a i+Y a i)
      (fun a i => (r : ℂ) • X a i+Y a i)).re=
      r^2*(gaugePair X X).re+2*r*(gaugePair X Y).re+(gaugePair Y Y).re := by
  have hc := congrArg Complex.re (gauge_pair_conjugate X Y)
  simp only [Complex.conj_re] at hc
  have he : gaugePair (fun a i => (r : ℂ) • X a i+Y a i)
      (fun a i => (r : ℂ) • X a i+Y a i)=
      ((r : ℂ)^2)*gaugePair X X+(r : ℂ)*gaugePair X Y+(r : ℂ)*gaugePair Y X+gaugePair Y Y := by
    simp only [gaugePair,sourcePair,map_add,map_smul,inner_add_left,inner_add_right,
      inner_smul_left,inner_smul_right,Complex.conj_ofReal,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    ring
  rw [he]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    ←Complex.ofReal_pow,sub_zero,zero_mul]
  rw [←hc]
  ring

private theorem cross_young (X Y : LieIndex → Fin 3 → QuantumTest) (r : ℝ) (hr : 0<r) :
    |(gaugePair X Y).re| ≤ (r/2)*(gaugePair X X).re+(gaugePair Y Y).re/(2*r) := by
  have hp := gauge_pair_nonneg (fun a i => (r : ℂ) • X a i+Y a i)
  have hm := gauge_pair_nonneg (fun a i => ((-r : ℝ) : ℂ) • X a i+Y a i)
  rw [pair_real_expansion] at hp hm
  apply (abs_le).mpr
  constructor
  · have he : (-(r^2*(gaugePair X X).re+(gaugePair Y Y).re))/(2*r)=
        -((r/2)*(gaugePair X X).re+(gaugePair Y Y).re/(2*r)) := by field_simp
    rw [←he]
    exact (div_le_iff₀ (by positivity : 0<2*r)).mpr (by nlinarith only [hp])
  · have he : (r^2*(gaugePair X X).re+(gaugePair Y Y).re)/(2*r)=
        (r/2)*(gaugePair X X).re+(gaugePair Y Y).re/(2*r) := by field_simp
    rw [←he]
    exact (le_div_iff₀ (by positivity : 0<2*r)).mpr (by nlinarith only [hm])

/-- One additional source lapse of positive bulk absorbs the full matter derivative; the exact coframe contact moment remains. -/
theorem original_matter_force_absorption (f : QuantumTest) :
    |(sourcePair f (matterBulkCurrent f)).im/2| ≤
      sourceTime 0*inverseForm f+(9/(2*sourceTime 0))*contactEnergy f := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hy := cross_young (fun a i => column i a (inverseRootAction f))
    (fun a i => matterContact (gaugeDirection i a) (inverseRootAction f)) (2*sourceTime 0) (by positivity)
  rw [gauge_kinetic_columns] at hy
  have hscaled := mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 18)
  have hE := original_inverse_energy f
  have hN : 0 ≤ inverseNativeEnergy f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : 0 ≤ shiftedMoment f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hG := original_gauge_kinetic_nonnegative (inverseRootAction f)
  rw [original_matter_current_form,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<18)]
  change _ ≤ sourceTime 0*inverseForm f+(9/(2*sourceTime 0))*contactEnergy f
  simp only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] at hscaled
  change 18*|_| ≤ 18*((2*sourceTime 0/2)*(2*(_ : ℝ))+contactEnergy f/(2*(2*sourceTime 0))) at hscaled
  have hc : 18*(contactEnergy f/(2*(2*sourceTime 0)))=(9/(2*sourceTime 0))*contactEnergy f := by field_simp;ring
  rw [mul_add,hc] at hscaled
  have hbulk : 36*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re ≤ inverseForm f := by
    nlinarith only [hE,mul_nonneg hn.le hN,mul_nonneg hn.le hS]
  have hb := mul_le_mul_of_nonneg_left hbulk hn.le
  nlinarith only [hscaled,hb]

end LowEnergy.SourceMatterForceAbsorption
