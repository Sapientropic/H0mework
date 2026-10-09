import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedLocalizationContactReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualLocalizedNativeWorkReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualLocalizedJointFrequencyPayment
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceDilationMultiplier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualBalancedPressureWardPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussHistoryHilbert
open SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet SourceScalarPositiveBulkWard
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourcePhysicalHamiltonianSquare
open SourceScalarInverseBulk SourceScalarInverseNativeEnergy SourceScalarShiftedBulk SourceClockPhiSecondBulk
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceDilationMultiplier SourceKineticScale
open ActualBalancedLocalizationContactReturn ActualNonmagneticPressureStorage ActualSecondPressureMagneticPayment
open ActualScalarPhaseJet ActualPhaseBulkSquare ActualPhaseWardIntertwiner
open SourceClockYukawaCubicCurrent ActualBalancedForceRetardedPayment SourceScalarPairedTransport
open Lean Meta Elab Term
open scoped ContDiff InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair nonmagneticSecondField phaseForce inverseVolumeAction sourceTime phaseCoefficient

elab "paid_pressure_virial%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarVirialBulk 0) "LowEnergy") "SourceScalarVirialBulk"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_pressure_storage%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSecondPressurePositiveStorage 0) "LowEnergy") "ActualSecondPressurePositiveStorage"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

/-- This is the original BF generator acting on the actual pressure source. -/
def balancedPressureJet (X:End):End:=balancedGenerator*X-X*balancedGenerator
private theorem jet_source(X:End):balancedPressureJet X=
    (3:ℂ) • deltaPhi X-(12:ℂ) • deltaGauge X-(6:ℂ) • scaleDerivative X := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator,←SourceGaugeScaleTransport.generator_commutator,
    ←SourceGaugeCoframeJets.K_commutator]
  unfold balancedPressureJet balancedGenerator
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
  module
private theorem jet_product(X Y:End):balancedPressureJet (X*Y)=balancedPressureJet X*Y+X*balancedPressureJet Y := by
  unfold balancedPressureJet
  noncomm_ring
private theorem jet_add(X Y:End):balancedPressureJet (X+Y)=balancedPressureJet X+balancedPressureJet Y := by
  unfold balancedPressureJet
  noncomm_ring
private theorem jet_sub(X Y:End):balancedPressureJet (X-Y)=balancedPressureJet X-balancedPressureJet Y := by
  unfold balancedPressureJet
  noncomm_ring
private theorem jet_smul(a:ℂ)(X:End):balancedPressureJet (a • X)=a • balancedPressureJet X := by
  unfold balancedPressureJet
  simp only [mul_smul_comm,smul_mul_assoc,smul_sub]

private theorem multiplier_coframe(a:SourceCoordinateSlice → ℝ)
    (ha:∀ z:physicalChart,ContDiffAt ℝ ∞ a z.val)
    (hs:∀ r:ℝ,∀ z:SourceCoordinateSlice,a (scale r z)=r^3*a z):
    scaleDerivative (multiply a ha)=(3:ℂ) • multiply a ha := by
  have hm:=homogeneous_multiplier a ha 3 (fun z=>
    euler_of_scale a 3 z (ha z) (fun r _=>by simpa only [zpow_ofNat] using hs r z.val))
  change (3*Complex.I/2) • (dilation*multiply a ha-multiply a ha*dilation)=_
  norm_num only [Complex.ofReal_ofNat] at hm
  rw [hm,smul_smul]
  have hc:(3*Complex.I/2)*((-2*Complex.I/3)*(3:ℂ))=(3:ℂ) := by
    calc _ = -3*(Complex.I*Complex.I) := by ring
         _ = 3 := by rw [Complex.I_mul_I];ring
  rw [hc]
private theorem centered_coframe:scaleDerivative centeredAction=(3:ℂ) • centeredAction := by
  unfold centeredAction
  apply multiplier_coframe
  intro r z
  change sourceTime 0*volume (scale r z)*‖scalarField (scale r z)‖^2=
    r^3*(sourceTime 0*volume z*‖scalarField z‖^2)
  rw [volume_scale]
  change sourceTime 0*(r^3*volume z)*‖scalarField z‖^2=_
  ring
private theorem linear_coframe:scaleDerivative vacuumLinearAction=(3:ℂ) • vacuumLinearAction := by
  unfold vacuumLinearAction
  apply multiplier_coframe
  intro r z
  change sourceTime 0*volume (scale r z)*inner ℝ vacuum (scalarField (scale r z))=
    r^3*(sourceTime 0*volume z*inner ℝ vacuum (scalarField z))
  rw [volume_scale]
  change sourceTime 0*(r^3*volume z)*inner ℝ vacuum (scalarField z)=_
  ring
private theorem constant_coframe:scaleDerivative vacuumConstantAction=(3:ℂ) • vacuumConstantAction := by
  unfold vacuumConstantAction
  apply multiplier_coframe
  intro r z
  change sourceTime 0*volume (scale r z)*‖vacuum‖^2=r^3*(sourceTime 0*volume z*‖vacuum‖^2)
  rw [volume_scale]
  ring
private theorem scalar_coframe:scaleDerivative scalarKinetic=(-3:ℂ) • scalarKinetic := by
  change (3*Complex.I/2) • (dilation*scalarKinetic-scalarKinetic*dilation)=_
  rw [SourceDilationKinetic.scalar_kinetic_current,smul_smul]
  have hc:(3*Complex.I/2)*(2*Complex.I)=(-3:ℂ) := by
    calc _ = 3*(Complex.I*Complex.I) := by ring
         _ = -3 := by rw [Complex.I_mul_I];ring
  rw [hc]

private theorem shifted_source:shiftedAction=centeredAction-vacuumLinearAction+(1/4:ℂ) • vacuumConstantAction := by
  have h:=original_positive_bulk
  rw [positiveBulk,original_filtered_bulk] at h
  linear_combination (norm:=module) (-1/8:ℂ) • h

/-- Actual source weights, including the full vacuum-affine Phi return. -/
theorem actual_balanced_pressure_weights:
    balancedPressureJet inverseVolumeAction=(18:ℂ) • inverseVolumeAction ∧
    balancedPressureJet scalarKinetic=(12:ℂ) • scalarKinetic ∧
    balancedPressureJet gaugeKinetic=(18:ℂ) • gaugeKinetic ∧
    balancedPressureJet shiftedAction=(-12:ℂ) • shiftedAction+(3:ℂ) • vacuumLinearAction-
      (3/2:ℂ) • vacuumConstantAction ∧
    balancedPressureJet vacuumConstantAction=(-18:ℂ) • vacuumConstantAction ∧
    balancedPressureJet phaseForce=(15:ℂ) • phaseForce := by
  have hu:balancedPressureJet inverseVolumeAction=(18:ℂ) • inverseVolumeAction := by
    rw [jet_source,inverse_phi,inverse_gauge,inverse_coframe]
    module
  have hs:balancedPressureJet scalarKinetic=(12:ℂ) • scalarKinetic := by
    rw [jet_source,original_scalar_kinetic_phi,original_scalar_kinetic_gauge,scalar_coframe]
    module
  have hg:balancedPressureJet gaugeKinetic=(18:ℂ) • gaugeKinetic := by
    rw [jet_source,original_gauge_kinetic_phi,original_gauge_kinetic_gauge,scale_electric]
    module
  have hcenter:balancedPressureJet centeredAction=(-12:ℂ) • centeredAction := by
    rw [jet_source,(paid_pressure_virial% centered_phi),(paid_pressure_virial% centered_gauge),centered_coframe]
    module
  have hlinear:balancedPressureJet vacuumLinearAction=(-15:ℂ) • vacuumLinearAction := by
    rw [jet_source,(paid_pressure_virial% vacuum_linear_phi),(paid_pressure_virial% vacuum_linear_gauge),linear_coframe]
    module
  have hconstant:balancedPressureJet vacuumConstantAction=(-18:ℂ) • vacuumConstantAction := by
    rw [jet_source,(paid_pressure_virial% vacuum_constant_phi),(paid_pressure_virial% vacuum_constant_gauge),constant_coframe]
    module
  have ht:balancedPressureJet shiftedAction=(-12:ℂ) • shiftedAction+(3:ℂ) • vacuumLinearAction-
      (3/2:ℂ) • vacuumConstantAction := by
    rw [shifted_source,jet_add,jet_sub,jet_smul,hcenter,hlinear,hconstant]
    module
  have hf:balancedPressureJet phaseForce=(15:ℂ) • phaseForce := by
    obtain ⟨hp,hg,hc⟩:=actual_source_phase_force_weights
    rw [jet_source,hp,hg,hc]
    module
  exact ⟨hu,hs,hg,ht,hconstant,hf⟩

/-- All four source departments have a coercive signed return. The genuine
vacuum-affine terms combine into the centered square before taking a price. -/
theorem actual_balanced_pressure_source:
    balancedPressureJet nonmagneticSecondField-(3:ℂ) • nonmagneticSecondField=
      (54*(phaseCoefficient:ℂ)) • (scalarKinetic*inverseVolumeAction+inverseVolumeAction*scalarKinetic)-
      (198*(phaseCoefficient:ℂ)) • (gaugeKinetic*inverseVolumeAction+inverseVolumeAction*gaugeKinetic)-
      (6*(phaseCoefficient:ℂ)) • (centeredAction*inverseVolumeAction+inverseVolumeAction*centeredAction)-
      (108:ℂ) • (phaseForce*phaseForce) := by
  obtain ⟨hu,hs,hg,ht,hv,hf⟩:=actual_balanced_pressure_weights
  unfold nonmagneticSecondField nonmagneticBulk
  simp only [jet_sub,jet_add,jet_smul,jet_product,hu,hs,hg,ht,hv,hf,
    add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_add,smul_sub,smul_smul]
  rw [shifted_source]
  simp only [add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_add,smul_sub,smul_smul]
  module

private theorem weighted_pair(X:End)(hr:Commute inverseRootAction X)(f:QuantumTest):
    sourcePair f ((X*inverseVolumeAction+inverseVolumeAction*X) f)=
      (2:ℂ)*sourcePair (inverseRootAction f) (X (inverseRootAction f)) := by
  have hx:X (inverseVolumeAction f)=inverseRootAction (X (inverseRootAction f)) := by
    rw [←inverse_root_square f]
    exact (LinearMap.congr_fun hr.eq (inverseRootAction f)).symm
  have hy:inverseVolumeAction (X f)=inverseRootAction (X (inverseRootAction f)) := by
    rw [←inverse_root_square (X f)]
    exact congrArg inverseRootAction (LinearMap.congr_fun hr.eq f)
  have hp:sourcePair f (inverseRootAction (X (inverseRootAction f)))=
      sourcePair (inverseRootAction f) (X (inverseRootAction f)) := by
    unfold inverseRootAction
    exact multiply_pair _ _ _ _
  simp only [LinearMap.add_apply,Module.End.mul_apply,sourcePair,map_add,inner_add_right]
  simp only [sourcePair] at hp
  rw [hx,hy,hp]
  ring

private theorem centered_nonnegative(f:QuantumTest):0 ≤ (sourcePair f (centeredAction f)).re := by
  unfold centeredAction
  have hn:0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  simpa only [one_mul] using
    (paid_pressure_virial% scalar_multiplier_sign) _ _ 1
      (fun z=>by
        change 0 ≤ 1*(sourceTime 0*volume z.val*‖scalarField z.val‖^2)
        have hv:=volume_pos z
        positivity) f

/-- Actual source sign: no symmetry or global CF positivity is supplied. -/
theorem actual_balanced_pressure_coercivity(f:QuantumTest):
    (sourcePair f (balancedPressureJet nonmagneticSecondField f)).re ≤
      3*(sourcePair f (nonmagneticSecondField f)).re := by
  have hr:Commute inverseRootAction centeredAction := by
    unfold centeredAction
    exact inverse_root_real _ _
  have hscalar:=original_scalar_kinetic_nonpositive (inverseRootAction f)
  have hgauge:=original_gauge_kinetic_nonnegative (inverseRootAction f)
  have hcenter:=centered_nonnegative (inverseRootAction f)
  have hforce:=actual_phase_force_square_energy f
  have he:=congrArg (fun X:End=>(sourcePair f (X f)).re) actual_balanced_pressure_source
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_right,inner_smul_right,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im] at he
  have hs:=weighted_pair scalarKinetic (paid_pressure_storage% root_scalar) f
  have hg:=weighted_pair gaugeKinetic inverse_root_electric f
  have hc:=weighted_pair centeredAction hr f
  have hsre:=congrArg Complex.re hs
  have hgre:=congrArg Complex.re hg
  have hcre:=congrArg Complex.re hc
  norm_num [sourcePair,Complex.mul_re] at hsre hgre hcre
  simp only [sourcePair] at hscalar hgauge hcenter hforce
  norm_num [Complex.mul_re,Complex.mul_im] at he
  simp only [inner_add_right,Complex.add_re] at he
  simp only [Module.End.mul_apply] at hforce
  rw [hsre,hgre,hcre,hforce] at he
  simp only [sourcePair]
  have hp:=actual_phase_coefficient_positive
  nlinarith only [he,hscalar,hgauge,hcenter,sq_nonneg ‖embed (phaseForce f)‖,hp]

/-- A source pressure inventory generated by the original BF generator. -/
def balancedPressurePrice(f:QuantumTest):ℝ :=
  -(1/(2*phaseCoefficient))*(sourcePair f (balancedPressureJet nonmagneticSecondField f)).re+
    (3*sourceTime 0*‖vacuum‖^2/2)*‖embed f‖^2

/-- The A pressure supplies three complete native/gauge/shift/force inventories;
the coefficient is generated from the actual vacuum-affine source. -/
theorem actual_balanced_pressure_storage_price(f:QuantumTest):
    3*nonmagneticStorage f ≤ balancedPressurePrice f := by
  have hs:=actual_nonmagnetic_storage_source f
  have hp:=actual_balanced_pressure_coercivity f
  have hc:=actual_phase_coefficient_positive
  unfold balancedPressurePrice
  have hi:0 < 1/(2*phaseCoefficient) := by positivity
  nlinarith only [hs,hp,hi]

theorem actual_balanced_pressure_nonnegative(f:QuantumTest):0 ≤ balancedPressurePrice f := by
  have hs:=actual_nonmagnetic_storage_nonnegative f
  have hp:=actual_balanced_pressure_storage_price f
  linarith only [hs,hp]

/-- The complete frozen localization mouth now consumes the actual A pressure
on both inputs; the joint Noether source remains in its original ordered place. -/
theorem actual_localization_radial_pressure_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    |ActualBalancedForceRetardedPayment.balancedLocalizationContact m ell F z hz g-
      (1/6:ℝ)*(jointNoetherForcing m ell F z hz g).re|/(2*phaseCoefficient) ≤
      (1/6962:ℝ)*(balancedPressurePrice
        (SourceClockYukawaCubicCurrent.resolventCore F z hz
          (ReverseScalarGaugeWard.balancedCompressionForce F
            (SourceClockYukawaCubicCurrent.resolventCore F z hz g)))+
        balancedPressurePrice (SourceClockYukawaCubicCurrent.resolventCore F z hz g)) := by
  have hr:=actual_localization_radial_source_price m ell F z hz g
  have hf:=actual_balanced_pressure_storage_price
    (SourceClockYukawaCubicCurrent.resolventCore F z hz
      (ReverseScalarGaugeWard.balancedCompressionForce F
        (SourceClockYukawaCubicCurrent.resolventCore F z hz g)))
  have hg:=actual_balanced_pressure_storage_price (SourceClockYukawaCubicCurrent.resolventCore F z hz g)
  nlinarith only [hr,hf,hg]

private theorem generator_skew(f h:QuantumTest):
    sourcePair f (balancedGenerator h)= -sourcePair (balancedGenerator f) h := by
  have hp:=(paid_shifted_response% phi_pair) f h
  have hg:=(paid_shifted_response% gauge_pair) f h
  have hc:=(paid_shifted_response% coframe_pair) f h
  unfold balancedGenerator
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,starRingEnd_apply,star_ofNat] at hp hg hc ⊢
  rw [hp,hg,hc]
  ring

/-- The pressure sign is generated by the actual skew A and Hermitian S. -/
theorem actual_balanced_pressure_pair_source(f:QuantumTest):
    phaseCoefficient*balancedPressurePrice f=
      (sourcePair (balancedGenerator f) (nonmagneticSecondField f)).re+
      (3*phaseCoefficient*sourceTime 0*‖vacuum‖^2/2)*‖embed f‖^2 := by
  have hA:=generator_skew f (nonmagneticSecondField f)
  have hS:=ActualNonmagneticPressureStorage.actual_nonmagnetic_source_pair f (balancedGenerator f)
  have hr:(sourcePair (nonmagneticSecondField f) (balancedGenerator f)).re=
      (sourcePair (balancedGenerator f) (nonmagneticSecondField f)).re := by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) _ _
  have he:(sourcePair f (balancedPressureJet nonmagneticSecondField f)).re=
      -2*(sourcePair (balancedGenerator f) (nonmagneticSecondField f)).re := by
    unfold balancedPressureJet
    simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right,Complex.sub_re]
    simp only [sourcePair] at hA hS hr
    rw [hA,hS,Complex.neg_re,hr]
    ring
  unfold balancedPressurePrice
  rw [he]
  have hc:phaseCoefficient≠0:=actual_phase_coefficient_positive.ne'
  field_simp [hc]

private theorem star_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

/-- The original A pressure meets the same-F resolvent through one whole
BF source reader, the CF mass term and the actual affine cutoff contact. -/
theorem actual_balanced_pressure_retarded_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    let w:=SourceNativeCutoffContact.thetaAction m ell q
    let u:=compensatedReader m ell F z hz g
    phaseCoefficient*balancedPressurePrice w=
      (sourcePair (SourceNativeCutoffContact.thetaAction m ell
        (resolventCore F z hz (balancedGenerator g))) (nonmagneticSecondField w)).re-
      (sourcePair u (ReverseScalarGaugeWard.balancedCompressionForce F q)).re-
      18*(sourcePair u (compressionCore F q)).re+
      (sourcePair (((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) q)
        (nonmagneticSecondField w)).re+
      (3*phaseCoefficient*sourceTime 0*‖vacuum‖^2/2)*‖embed w‖^2 := by
  dsimp only
  let q:=resolventCore F z hz g
  let w:=SourceNativeCutoffContact.thetaAction m ell q
  let u:=compensatedReader m ell F z hz g
  have hInv:=LinearMap.congr_fun (paid_balanced_inverse% balancedGenerator F z hz) g
  have hBF:=actual_balanced_generator_source F
  have hA:balancedGenerator q=resolventCore F z hz (balancedGenerator g)-
      resolventCore F z hz (ReverseScalarGaugeWard.balancedCompressionForce F q)-
      (18:ℂ) • resolventCore F z hz (compressionCore F q) := by
    unfold q
    rw [show compressionCore F*balancedGenerator-balancedGenerator*compressionCore F=
      -(ReverseScalarGaugeWard.balancedCompressionForce F+(18:ℂ) • compressionCore F) by
        linear_combination (norm:=module) hBF] at hInv
    simp only [LinearMap.add_apply,Module.End.mul_apply,LinearMap.neg_apply,LinearMap.smul_apply,
      map_add,map_neg,map_smul] at hInv
    linear_combination (norm:=module) hInv
  have ht:=LinearMap.congr_fun (actual_balanced_cutoff_source m ell) q
  have hw:balancedGenerator w=SourceNativeCutoffContact.thetaAction m ell
      (resolventCore F z hz (balancedGenerator g))-
      SourceNativeCutoffContact.thetaAction m ell
        (resolventCore F z hz (ReverseScalarGaugeWard.balancedCompressionForce F q))-
      (18:ℂ) • SourceNativeCutoffContact.thetaAction m ell
        (resolventCore F z hz (compressionCore F q))+
      ((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) q := by
    unfold w
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply] at ht
    rw [hA] at ht
    simp only [map_sub,map_smul] at ht
    simp only [LinearMap.smul_apply]
    linear_combination (norm:=module) ht
  have hR(v h:QuantumTest):sourcePair (resolventCore F z hz v) h=
      sourcePair v (resolventCore F (star z) (star_nonreal z hz) h) := by
    simpa only [star_star] using
      ((paid_balanced_covariance% resolvent_pair) F z hz v h).symm
  have htheta(v h:QuantumTest):sourcePair (SourceNativeCutoffContact.thetaAction m ell v) h=
      sourcePair v (SourceNativeCutoffContact.thetaAction m ell h) := by
    unfold SourceNativeCutoffContact.thetaAction
    exact (multiply_pair _ _ _ _).symm
  have hread(v:QuantumTest):
      (sourcePair (SourceNativeCutoffContact.thetaAction m ell (resolventCore F z hz v))
        (nonmagneticSecondField w)).re=(sourcePair u v).re := by
    rw [htheta,hR]
    change (sourcePair v u).re=(sourcePair u v).re
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) _ _
  have hp:=actual_balanced_pressure_pair_source w
  rw [hw] at hp
  norm_num [sourcePair,map_add,map_sub,map_smul,inner_add_left,inner_sub_left,inner_smul_left,
    starRingEnd_apply,star_ofNat,Complex.add_re,Complex.sub_re,Complex.mul_re] at hp
  simp only [sourcePair] at hread
  rw [hread (ReverseScalarGaugeWard.balancedCompressionForce F q),hread (compressionCore F q)] at hp
  convert hp using 1
  simp only [sourcePair,LinearMap.smul_apply,map_smul,inner_smul_left,starRingEnd_apply,
    star_ofNat,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  ring

/-- The localization and localized BF source terms receive the same genuine
positive pressure. Neither leakage leg is discarded or separately budgeted. -/
theorem actual_balanced_localization_pressure_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    let w:=SourceNativeCutoffContact.thetaAction m ell q
    let u:=compensatedReader m ell F z hz g
    balancedLocalizationContact m ell F z hz g+
      (phaseCoefficient/6)*balancedPressurePrice w+
      (1/6:ℝ)*(sourcePair (localizedPressureReader m ell F z hz g)
        (ReverseScalarGaugeWard.balancedCompressionForce F w)).re=
      (1/6:ℝ)*((sourcePair (SourceNativeCutoffContact.thetaAction m ell
        (resolventCore F z hz (balancedGenerator g))) (nonmagneticSecondField w)).re-
        18*(sourcePair u (compressionCore F q)).re+
        (sourcePair (((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) q)
          (nonmagneticSecondField w)).re+
        (3*phaseCoefficient*sourceTime 0*‖vacuum‖^2/2)*‖embed w‖^2)+
      radialBalancedContact m ell F z hz g := by
  dsimp only
  have hp:=actual_balanced_pressure_retarded_return m ell F z hz g
  dsimp only at hp
  have hl:=actual_balanced_localization_joint_return m ell F z hz g
  unfold jointBalancedNoether at hl
  simp only [Complex.sub_re] at hl
  linear_combination (norm:=ring_nf) hl+(1/6:ℝ)*hp

/-- The original native-plus-Own current consumes the pressure return without
changing its signed direction. The BF fixed-contact department remains inside
sourceNativeInvoice at its original coefficient. -/
theorem actual_whole_native_pressure_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    let w:=SourceNativeCutoffContact.thetaAction m ell q
    let u:=compensatedReader m ell F z hz g
    (ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F z hz g).re+
      (phaseCoefficient/6)*balancedPressurePrice w=
      ActualLocalizedNativeWorkReturn.sourceNativeInvoice m ell F z hz g+
      (1/6:ℝ)*((sourcePair (SourceNativeCutoffContact.thetaAction m ell
        (resolventCore F z hz (balancedGenerator g))) (nonmagneticSecondField w)).re-
        18*(sourcePair u (compressionCore F q)).re+
        (sourcePair (((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) q)
          (nonmagneticSecondField w)).re+
        (3*phaseCoefficient*sourceTime 0*‖vacuum‖^2/2)*‖embed w‖^2)+
      radialBalancedContact m ell F z hz g := by
  dsimp only
  rw [ActualLocalizedNativeWorkReturn.actual_whole_source_native_invoice,
    actual_balanced_pressure_localized_return]
  have h:=actual_balanced_localization_pressure_return m ell F z hz g
  dsimp only at h
  linear_combination (norm:=ring_nf) h

end LowEnergy.ActualBalancedPressureWardPayment
