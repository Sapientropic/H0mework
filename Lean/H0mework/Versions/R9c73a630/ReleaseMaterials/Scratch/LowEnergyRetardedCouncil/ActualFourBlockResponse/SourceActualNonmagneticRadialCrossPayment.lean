import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualWholeGammaPressureReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualUnweightedSquareCurrentPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualNonmagneticPressureStorage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualNonmagneticRadialCrossPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy SourceQuantumScalarChart
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume
open SourceScalarVirialBulk SourceScalarInverseBulk SourceScalarInverseNativeEnergy SourceScalarInverseEnergyExchange
open SourceInverseContactHardy SourceInverseVolumeContact SourceInverseNoetherEnergy
open SourceNativeCutoffContact SourceClockYukawaCubicCurrent
open ActualScalarPhaseJet ActualPhaseBulkSquare ActualSecondPressureMagneticPayment
open ActualUnweightedSquareCurrentPayment ActualWholeGammaPressureReturn ActualNonmagneticPressureStorage
open SourceClockReflectedForm SourceScalarNativeComparison
open Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair thetaAction phaseForce phaseCoefficient nonmagneticSecondField
  scalarKinetic gaugeKinetic shiftedAction vacuumConstantAction positiveBulk bulkAction shiftedSquare

elab "paid_radial_square%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualUnweightedSquareCurrentPayment 0) "LowEnergy") "ActualUnweightedSquareCurrentPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_radial_ims%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarBulkResidualBudget 0) "LowEnergy") "SourceScalarBulkResidualBudget"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_radial_inverse%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeEnergy 0) "LowEnergy") "SourceScalarInverseNativeEnergy"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem theta_pair(m ell:ℕ)(f h:QuantumTest):
    sourcePair f (thetaAction m ell h)=sourcePair (thetaAction m ell f) h := by
  unfold thetaAction
  exact multiply_pair _ _ _ _
private theorem product_commute(A B T:End)(hA:A*T=T*A)(hB:B*T=T*B):
    (A*B)*T=T*(A*B) := by
  calc
    _=A*(B*T):=by noncomm_ring
    _=A*(T*B):=by rw [hB]
    _=(A*T)*B:=by noncomm_ring
    _=(T*A)*B:=by rw [hA]
    _=T*(A*B):=by noncomm_ring

/-- The actual mixed radial insertion is the whole double commutator. -/
def radialDouble(m ell:ℕ)(A:End):End :=
  let T:=thetaAction m ell
  T*(T*A-A*T)-(T*A-A*T)*T

private theorem double_add(m ell:ℕ)(A B:End):
    radialDouble m ell (A+B)=radialDouble m ell A+radialDouble m ell B := by
  unfold radialDouble
  noncomm_ring
private theorem double_smul(m ell:ℕ)(c:ℂ)(A:End):
    radialDouble m ell (c • A)=c • radialDouble m ell A := by
  unfold radialDouble
  simp only [mul_smul_comm,smul_mul_assoc,←smul_sub]
private theorem double_zero_of_commute(m ell:ℕ)(A:End)(h:Commute A (thetaAction m ell)):
    radialDouble m ell A=0 := by
  unfold radialDouble
  dsimp only
  rw [h.eq]
  simp only [sub_self,mul_zero,zero_mul]

private theorem nonmag_bulk_split:
    nonmagneticBulk=(1/4:ℂ) • positiveBulk-(3:ℂ) • gaugeKinetic-(1/2:ℂ) • vacuumConstantAction := by
  unfold nonmagneticBulk
  rw [original_positive_bulk]
  module

def radialCommutingRemainder:End :=
  (3*(phaseCoefficient:ℂ)) • (gaugeKinetic*inverseVolumeAction+inverseVolumeAction*gaugeKinetic)+
    ((phaseCoefficient:ℂ)/2) •
      (vacuumConstantAction*inverseVolumeAction+inverseVolumeAction*vacuumConstantAction)

/-- The nonmagnetic second field and the already-paid B share the same
radial occurrence. Their genuine gauge/vacuum remainder is retained. -/
theorem actual_nonmagnetic_radial_source:
    nonmagneticSecondField=(1/4:ℂ) • shiftedSquare+radialCommutingRemainder := by
  have hc:positiveBulk*inverseVolumeAction=inverseVolumeAction*positiveBulk :=
    ((paid_radial_inverse% inverse_commute) positiveBulk (paid_radial_inverse% bulk_volume)).eq
  unfold nonmagneticSecondField
  rw [nonmag_bulk_split,(paid_radial_square% shifted_square_negative)]
  unfold radialCommutingRemainder bulkAction
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_add,smul_sub,smul_smul,hc]
  module

/-- Source gauge directions have zero scalar radius contact, while both
volume and vacuum weights are true multiplier actions. -/
theorem actual_radial_remainder_commute(m ell:ℕ):
    Commute radialCommutingRemainder (thetaAction m ell) := by
  have hg:Commute gaugeKinetic (thetaAction m ell):=(paid_radial_ims% gauge_theta) m ell
  have hu:Commute inverseVolumeAction (thetaAction m ell) := by
    apply LinearMap.ext
    intro f
    simp only [Module.End.mul_apply]
    exact (paid_radial_square% theta_inverse) m ell f
  have hv:Commute vacuumConstantAction (thetaAction m ell) := by
    unfold vacuumConstantAction
    exact ((paid_radial_ims% theta_real_commute) m ell _ _).symm
  change radialCommutingRemainder*thetaAction m ell=thetaAction m ell*radialCommutingRemainder
  unfold radialCommutingRemainder
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
  rw [product_commute gaugeKinetic inverseVolumeAction (thetaAction m ell) hg.eq hu.eq,
    product_commute inverseVolumeAction gaugeKinetic (thetaAction m ell) hu.eq hg.eq,
    product_commute vacuumConstantAction inverseVolumeAction (thetaAction m ell) hv.eq hu.eq,
    product_commute inverseVolumeAction vacuumConstantAction (thetaAction m ell) hu.eq hv.eq]


/-- The complete double commutator inherits one quarter of B's real
native70/phase-force contact operator; no diagonal-only replacement is used. -/
theorem actual_nonmagnetic_radial_double(m ell:ℕ):
    radialDouble m ell nonmagneticSecondField=(1/4:ℂ) • radialDouble m ell shiftedSquare := by
  rw [actual_nonmagnetic_radial_source,double_add,double_smul,
    double_zero_of_commute m ell _ (actual_radial_remainder_commute m ell),add_zero]

private theorem pair_add_right(f h k:QuantumTest):sourcePair f (h+k)=sourcePair f h+sourcePair f k := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_right(f h k:QuantumTest):sourcePair f (h-k)=sourcePair f h-sourcePair f k := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_right(c:ℂ)(f h:QuantumTest):sourcePair f (c • h)=c*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem double_pair(m ell:ℕ)(A:End)(f h:QuantumTest):
    sourcePair f (radialDouble m ell A h)=
      sourcePair (thetaAction m ell (thetaAction m ell f)) (A h)-
      (2:ℂ)*sourcePair (thetaAction m ell f) (A (thetaAction m ell h))+
      sourcePair f (A (thetaAction m ell (thetaAction m ell h))) := by
  unfold radialDouble
  have ha:thetaAction m ell*(thetaAction m ell*A-A*thetaAction m ell)-
      (thetaAction m ell*A-A*thetaAction m ell)*thetaAction m ell=
      thetaAction m ell*thetaAction m ell*A-
      (2:ℂ) • (thetaAction m ell*A*thetaAction m ell)+A*thetaAction m ell*thetaAction m ell := by
    simp only [two_smul]
    noncomm_ring
  rw [ha]
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    pair_add_right,pair_sub_right,pair_smul_right]
  rw [theta_pair,theta_pair,theta_pair]

private theorem force_bilinear_ims(m ell:ℕ)(f h:QuantumTest):
    sourcePair (thetaAction m ell f) ((phaseForce*phaseForce) (thetaAction m ell h))=
      (1/2:ℂ)*(sourcePair (thetaAction m ell (thetaAction m ell f)) ((phaseForce*phaseForce) h)+
        sourcePair f ((phaseForce*phaseForce) (thetaAction m ell (thetaAction m ell h))))+
      sourcePair (phaseCutoffContact m ell f) (phaseCutoffContact m ell h) := by
  have hp(q:QuantumTest):phaseForce (thetaAction m ell q)=
      thetaAction m ell (phaseForce q)+phaseCutoffContact m ell q := by
    unfold phaseCutoffContact
    simp only [Module.End.mul_apply,LinearMap.sub_apply]
    abel
  have hc:Commute (phaseCutoffContact m ell) (thetaAction m ell) := by
    apply LinearMap.ext
    exact (paid_radial_square% phase_contact_theta) m ell
  have hrow:=(paid_radial_ims% row_ims) phaseForce (thetaAction m ell) (phaseCutoffContact m ell)
    (theta_pair m ell) hp hc f h
  rw [←actual_phase_force_pair,←actual_phase_force_pair,←actual_phase_force_pair] at hrow
  exact hrow

private theorem bulk_bilinear_ims(m ell:ℕ)(f h:QuantumTest):
    sourcePair (thetaAction m ell f) (bulkAction (thetaAction m ell h))=
      (1/2:ℂ)*(sourcePair (thetaAction m ell (thetaAction m ell f)) (bulkAction h)+
        sourcePair f (bulkAction (thetaAction m ell (thetaAction m ell h))))+inverseContact m ell f h := by
  have he:=original_inverse_bilinear_ims m ell f h
  rw [original_inverse_bulk_symmetric_jet] at he
  simp only [SourceScalarInverseRetardedBudget.theta,SourceScalarInverseRetardedBudget.square,
    InverseVolumeLocalizationAlgebra.jordan,Module.End.mul_apply,LinearMap.smul_apply,
    LinearMap.add_apply,pair_add_right,pair_smul_right,theta_pair] at he
  simp only [bulkAction,Module.End.mul_apply]
  linear_combination he


/-- Native70 and the actual H1 contact retain independent complex source
legs, including the phase interference absent from a real diagonal IMS. -/
theorem actual_nonmagnetic_radial_gram(m ell:ℕ)(f h:QuantumTest):
    sourcePair f (radialDouble m ell nonmagneticSecondField h)=
      (phaseCoefficient:ℂ)*inverseContact m ell f h+
      (8:ℂ)*sourcePair (phaseCutoffContact m ell f) (phaseCutoffContact m ell h) := by
  rw [actual_nonmagnetic_radial_double]
  simp only [LinearMap.smul_apply,pair_smul_right]
  rw [(paid_radial_square% shifted_square_negative),double_add,double_smul,double_smul]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_right,pair_smul_right]
  rw [double_pair,double_pair]
  have hb:=bulk_bilinear_ims m ell f h
  have hf:=force_bilinear_ims m ell f h
  linear_combination (norm := ring) (phaseCoefficient:ℂ)*hb+8*hf


private theorem lapse_positive:0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_square_price(f h:QuantumTest):
    ‖sourcePair f h‖ ≤ (‖embed f‖^2+‖embed h‖^2)/2 := by
  have hp:‖sourcePair f h‖ ≤ ‖embed f‖*‖embed h‖ := by
    simpa only [sourcePair] using norm_inner_le_norm (𝕜:=ℂ) (embed f) (embed h)
  nlinarith only [hp,sq_nonneg (‖embed f‖-‖embed h‖)]

private theorem inverse_contact_pair_price(m ell:ℕ)(f h:QuantumTest):
    ‖inverseContact m ell f h‖ ≤
      ((inverseContact m ell f f).re+(inverseContact m ell h h).re)/2 := by
  have hn:=lapse_positive
  rw [inverse_contact_real,inverse_contact_real]
  unfold inverseContact
  rw [norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
  have hs:‖∑i:ScalarIndex,sourcePair
      (inverseVolumeAction (contactAction (scalarDirection i) m ell f))
      (inverseVolumeAction (contactAction (scalarDirection i) m ell h))‖ ≤
      ∑i:ScalarIndex,(‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell f))‖^2+
        ‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell h))‖^2)/2 :=
    (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun i _=>pair_square_price _ _))
  apply (mul_le_mul_of_nonneg_left hs (by positivity:0 ≤ 4*sourceTime 0)).trans_eq
  rw [←Finset.sum_div,Finset.sum_add_distrib]
  ring

/-- This is the actual positive contact energy, not a caller price. -/
def radialContactEnergy(m ell:ℕ)(f:QuantumTest):ℝ :=
  phaseCoefficient*(inverseContact m ell f f).re+8*‖embed (phaseCutoffContact m ell f)‖^2

private theorem contact_nonnegative(m ell:ℕ)(f:QuantumTest):
    0 ≤ (inverseContact m ell f f).re := by
  rw [inverse_contact_real]
  have hn:=lapse_positive
  positivity
private theorem energy_nonnegative(m ell:ℕ)(f:QuantumTest):0 ≤ radialContactEnergy m ell f := by
  unfold radialContactEnergy
  have hc:=actual_phase_coefficient_positive
  have hi:=contact_nonnegative m ell f
  positivity

/-- Cauchy on the real source contact Gram pays its full complex cross. -/
theorem actual_nonmagnetic_radial_energy_price(m ell:ℕ)(f h:QuantumTest):
    ‖sourcePair f (radialDouble m ell nonmagneticSecondField h)‖ ≤
      (radialContactEnergy m ell f+radialContactEnergy m ell h)/2 := by
  rw [actual_nonmagnetic_radial_gram]
  have hc:=actual_phase_coefficient_positive
  have hn:‖(phaseCoefficient:ℂ)‖=phaseCoefficient := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,hn,Complex.norm_ofNat]
  apply (add_le_add
    (mul_le_mul_of_nonneg_left (inverse_contact_pair_price m ell f h) hc.le)
    (mul_le_mul_of_nonneg_left (pair_square_price _ _) (by norm_num: (0:ℝ) ≤ 8))).trans_eq
  unfold radialContactEnergy
  ring

private theorem energy_radial_slot(m ell:ℕ)(f:QuantumTest):
    |radialSlot m ell f|=2*radialContactEnergy m ell f := by
  rw [actual_radial_slot_source]
  have hc:=actual_phase_coefficient_positive
  have hi:=contact_nonnegative m ell f
  rw [abs_of_nonpos (by nlinarith only [hc,hi,sq_nonneg ‖embed (phaseCutoffContact m ell f)‖])]
  unfold radialContactEnergy
  ring

private theorem energy_self_price(m ell:ℕ)(f:QuantumTest):
    radialContactEnergy m ell f ≤ (12*phaseCoefficient/3481)*inverseForm f := by
  have hp:=actual_radial_slot_self_price m ell f
  rw [energy_radial_slot] at hp
  have hc:=actual_phase_coefficient_positive
  have he:0 < 2*phaseCoefficient:=by positivity
  have h:=(div_le_iff₀ he).mp hp
  nlinarith only [h]

/-- Both independent source inventories receive a strict small gain; the
imaginary interference is covered by the same actual native/H1 Gram. -/
theorem actual_nonmagnetic_radial_form_price(m ell:ℕ)(f h:QuantumTest):
    ‖sourcePair f (radialDouble m ell nonmagneticSecondField h)‖/(2*phaseCoefficient) ≤
      (3/3481:ℝ)*(inverseForm f+inverseForm h) := by
  have hp:=actual_nonmagnetic_radial_energy_price m ell f h
  have hf:=energy_self_price m ell f
  have hh:=energy_self_price m ell h
  have hc:=actual_phase_coefficient_positive
  apply (div_le_iff₀ (by positivity:0 < 2*phaseCoefficient)).mpr
  nlinarith only [hp,hf,hh]

private theorem inverse_form_nonmagnetic_price(f:QuantumTest):inverseForm f ≤ 6*nonmagneticStorage f := by
  have he:=original_inverse_energy f
  have hs:scalarForm (inverseVolumeAction f)=inverseNativeEnergy f := original_inverse_native_return f
  unfold nonmagneticStorage
  rw [hs]
  rw [he]
  have hn:=lapse_positive
  have hc:=actual_phase_coefficient_positive
  have hN:0 ≤ inverseNativeEnergy f:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hV:0 ≤ shiftedMoment f:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hF:0 ≤ (2/phaseCoefficient)*‖embed (phaseForce f)‖^2:=by positivity
  nlinarith only [hn,hN,hV,hF]

/-- The mixed radial cross is paid directly by two actual source storage
slots, with 18/3481 below 1/128; no Gamma norm or contact budget is assumed. -/
theorem actual_nonmagnetic_radial_storage_price(m ell:ℕ)(f h:QuantumTest):
    ‖sourcePair f (radialDouble m ell nonmagneticSecondField h)‖/(2*phaseCoefficient) ≤
      (18/3481:ℝ)*(nonmagneticStorage f+nonmagneticStorage h) := by
  apply (actual_nonmagnetic_radial_form_price m ell f h).trans
  have hf:=inverse_form_nonmagnetic_price f
  have hh:=inverse_form_nonmagnetic_price h
  nlinarith only [hf,hh]

/-- The original retarded Gamma input and RF input keep the same F and z. -/
theorem actual_retarded_radial_storage_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    ‖sourcePair (gaugeRetardedCore F z hz g)
      (radialDouble m ell nonmagneticSecondField (resolventCore F z hz g))‖/(2*phaseCoefficient) ≤
      (18/3481:ℝ)*(nonmagneticStorage (gaugeRetardedCore F z hz g)+
        nonmagneticStorage (resolventCore F z hz g)) :=
  actual_nonmagnetic_radial_storage_price m ell _ _


private theorem energy_window_price(m ell:ℕ)(hm:1 ≤ m)(hell:m ≤ ell)(f:QuantumTest):
    radialContactEnergy m ell f ≤ (216*phaseCoefficient/3481)*
      (inverseForm (thetaAction (m/2) m f)+inverseForm (thetaAction (ell/2) ell f)) := by
  have hp:=actual_radial_slot_window_price m ell hm hell f
  rw [energy_radial_slot] at hp
  have hc:=actual_phase_coefficient_positive
  have h:=(div_le_iff₀ (by positivity:0 < 2*phaseCoefficient)).mp hp
  nlinarith only [h]

/-- The complete mixed contact is paid by the four original half-window
inventories. Its coefficient 54/3481 is strictly below 1/64. -/
theorem actual_nonmagnetic_radial_window_price(m ell:ℕ)(hm:1 ≤ m)(hell:m ≤ ell)(f h:QuantumTest):
    ‖sourcePair f (radialDouble m ell nonmagneticSecondField h)‖/(2*phaseCoefficient) ≤
      (54/3481:ℝ)*(inverseForm (thetaAction (m/2) m f)+inverseForm (thetaAction (ell/2) ell f)+
        inverseForm (thetaAction (m/2) m h)+inverseForm (thetaAction (ell/2) ell h)) := by
  have hp:=actual_nonmagnetic_radial_energy_price m ell f h
  have hf:=energy_window_price m ell hm hell f
  have hh:=energy_window_price m ell hm hell h
  have hc:=actual_phase_coefficient_positive
  apply (div_le_iff₀ (by positivity:0 < 2*phaseCoefficient)).mpr
  nlinarith only [hp,hf,hh]

/-- The source magnetic multiplier contributes zero to this radial
insertion, so the original full-S consumer shares the same contact Gram. -/
theorem actual_full_source_radial_double(m ell:ℕ):
    radialDouble m ell (SourceClockPhiSecondBulk.secondJet phaseHamiltonianSquare)=
      radialDouble m ell nonmagneticSecondField := by
  have hu:Commute inverseVolumeAction (thetaAction m ell) := by
    apply LinearMap.ext
    intro f
    simp only [Module.End.mul_apply]
    exact (paid_radial_square% theta_inverse) m ell f
  have hm:Commute magneticAction (thetaAction m ell) := by
    unfold magneticAction
    exact ((paid_radial_ims% theta_real_commute) m ell _ _).symm
  have hM:Commute magneticSecondField (thetaAction m ell) := by
    change magneticSecondField*thetaAction m ell=thetaAction m ell*magneticSecondField
    unfold magneticSecondField
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
    rw [product_commute magneticAction inverseVolumeAction (thetaAction m ell) hm.eq hu.eq,
      product_commute inverseVolumeAction magneticAction (thetaAction m ell) hu.eq hm.eq]
  rw [actual_native_phase_second_pressure_split,double_add,
    double_zero_of_commute m ell _ hM,zero_add]

/-- Both causal signs use the same full source S and raw-CF Gamma input;
the two source inventories retain every original Own contribution. -/
theorem actual_full_retarded_radial_storage_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    ‖sourcePair (gaugeRetardedCore F z hz g)
      (radialDouble m ell (SourceClockPhiSecondBulk.secondJet phaseHamiltonianSquare)
        (resolventCore F z hz g))‖/(2*phaseCoefficient) ≤
      (18/3481:ℝ)*(nonmagneticStorage (gaugeRetardedCore F z hz g)+
        nonmagneticStorage (resolventCore F z hz g)) := by
  rw [actual_full_source_radial_double]
  exact actual_retarded_radial_storage_price m ell F z hz g

end LowEnergy.ActualNonmagneticRadialCrossPayment
