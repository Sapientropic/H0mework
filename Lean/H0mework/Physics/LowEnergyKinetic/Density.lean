import H0mework.Physics.LowEnergyKinetic.Jet
import H0mework.Physics.LowEnergyPreparationDynamics.Spin
import H0mework.Physics.LowEnergyFullPhase.Derivative
import H0mework.Physics.SpinPair.DiracActual
import H0mework.Physics.Coframe.CoframeLocalDifferentiability

/-! The time pairing is read from the original densitized action and its actual affine jet. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Kinetic
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracCliffordRepresentation DiracExteriorMatterAction StageNineFullDiracAdjointMaterial
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation
open StageNineDiracDualFormNativeMatterVariation StageNineDiracDualFormNativeMotherAction
open StageNineP286GaugeConnectionVariationDensity StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open SU7ExteriorBreakingYukawa
open scoped Matrix
noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem exchange_gamma_time : diracAdjointSpinSwap * diracGamma 0 = diracGammaFive := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracAdjointSpinSwap,diracGamma,diracGammaZero,diracGammaFive,
      Matrix.mul_apply,Fin.sum_univ_four,Matrix.diagonal_apply]

theorem exchange_time_action (velocity : DiracExteriorMatterCarrier) :
    Quantum.spinExchange (diracMatrixMatterAction (diracGamma 0) velocity) =
      diracMatrixMatterAction diracGammaFive velocity := by
  unfold Quantum.spinExchange
  rw [← LinearMap.comp_apply,← diracMatrixMatterAction_mul,exchange_gamma_time]

theorem canonical_time_pair (matter velocity : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint matter (diracMatrixMatterAction (diracGamma 0) velocity) =
      Quantum.coordinatePair matter (diracMatrixMatterAction diracGammaFive velocity) := by
  rw [Quantum.canonicalDual_full_response,Quantum.spinExchange_selfAdjoint,exchange_time_action]

theorem pair_smul_right (scalar : ℂ) (left right : DiracExteriorMatterCarrier) :
    Quantum.coordinatePair left (scalar • right)=scalar*Quantum.coordinatePair left right := by
  simp only [Quantum.coordinatePair,map_smul,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

def kineticPair (density : ℝ) (left right : DiracExteriorMatterCarrier) : ℂ :=
  (density : ℂ)*Quantum.coordinatePair left (diracMatrixMatterAction diracGammaFive right)

def phaseChargePair (density : ℝ) (left right : DiracExteriorMatterCarrier) : ℂ :=
  kineticPair density left (FullPhase.phaseGenerator right)

def baseField (density : ℝ) (matter : DiracExteriorMatterCarrier) : StageNineContinuumPointField :=
  toContinuumPointField (configuration density matter 0) 0

theorem temporal_vector (density : ℝ) (matter velocity : DiracExteriorMatterCarrier) :
    diracDualMatterFieldVariationVector positiveSmoothUnifiedSource 0 (baseField density matter)
      0 (timeIncrement velocity) =
      (Complex.I*(lapse : ℂ)⁻¹) • diracMatrixMatterAction (diracGamma 0) velocity := by
  unfold diracDualMatterFieldVariationVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [map_zero,add_zero,matterDerivativeFrameRelative_zeroChart]
  have frame : (baseField density matter).coframe=homogeneousCoframe lapse := rfl
  rw [frame]
  simp [timeIncrement,Fin.sum_univ_four,homogeneousInverseGamma lapse (ne_of_gt lapse_pos),
    coframeDiracMatrixMatterAction_smul_matrix,smul_smul]

theorem temporal_coefficient (density : ℝ) (matter velocity : DiracExteriorMatterCarrier) :
    diracDualMatterFirstVariationDensity positiveSmoothUnifiedSource 0 (baseField density matter)
      0 (timeIncrement velocity) =
      density*(Complex.I*Quantum.coordinatePair matter (diracMatrixMatterAction diracGammaFive velocity)).re := by
  unfold diracDualMatterFirstVariationDensity
  rw [temporal_vector]
  have volume : generatedVolumeDensity (baseField density matter)=lapse := by
    change |(homogeneousCoframe lapse).det|=lapse
    rw [homogeneousCoframe_det,abs_of_pos lapse_pos]
  have dual : (baseField density matter).conjugateMatter=(density : ℂ) • fullCanonicalDiracAdjoint matter := by
    simp [baseField,toContinuumPointField,configuration,profile]
  rw [volume,dual,LinearMap.smul_apply,map_smul,canonical_time_pair]
  rw [← Complex.ofReal_inv]
  simp only [smul_eq_mul,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_add,one_mul,sub_zero,zero_sub]
  field_simp [ne_of_gt lapse_pos]

theorem timeIncrement_smul (parameter : ℝ) (velocity : DiracExteriorMatterCarrier) :
    timeIncrement (parameter • velocity)=parameter • timeIncrement velocity := by
  funext mu
  change timeIncrement ((parameter : ℂ) • velocity) mu =
    (parameter : ℂ) • timeIncrement velocity mu
  by_cases temporal : mu=0 <;> simp [timeIncrement,temporal]

theorem original_action_time_affine (density parameter : ℝ)
    (matter velocity : DiracExteriorMatterCarrier) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 0
      (toContinuumPointField (configuration density matter (parameter • velocity)) 0) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 0
        (baseField density matter) + parameter * density *
          (Complex.I*Quantum.coordinatePair matter (diracMatrixMatterAction diracGammaFive velocity)).re := by
  rw [point_origin,timeIncrement_smul]
  have affine := generatedDiracDualFormNativeUnifiedLocalDensity_withMatterJets_affine
    positiveSmoothUnifiedSource 0 (baseField density matter) 0 (timeIncrement velocity) parameter
  rw [temporal_coefficient] at affine
  have zeroMatter : parameter • (0 : DiracExteriorMatterCarrier)=0 := by
    change (parameter : ℂ) • (0 : DiracExteriorMatterCarrier)=0
    exact smul_zero _
  have value : (baseField density matter).matter=matter := by
    simp [baseField,toContinuumPointField,configuration,profile]
  rw [zeroMatter,add_zero,value] at affine
  simpa only [sourceGeneratedDiracDualFormNativeUnifiedLocalDensity,baseField,toContinuumPointField,
    mul_assoc] using affine

theorem phase_rate_coefficient (density : ℝ) (matter : DiracExteriorMatterCarrier) :
    diracDualMatterFirstVariationDensity positiveSmoothUnifiedSource 0 (baseField density matter)
      0 (timeIncrement ((-Complex.I) • FullPhase.phaseGenerator matter)) =
      (phaseChargePair density matter matter).re := by
  rw [temporal_coefficient,map_smul,pair_smul_right]
  have coefficient : Complex.I*(-Complex.I)=1 := by simp
  rw [← mul_assoc,coefficient,one_mul]
  simp [phaseChargePair,kineticPair,Complex.mul_re]

theorem original_action_phase_rate (density parameter : ℝ) (matter : DiracExteriorMatterCarrier) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 0
      (toContinuumPointField (configuration density matter
        (parameter • ((-Complex.I) • FullPhase.phaseGenerator matter))) 0) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 0
        (baseField density matter) + parameter*(phaseChargePair density matter matter).re := by
  rw [original_action_time_affine]
  have coefficient := phase_rate_coefficient density matter
  rw [temporal_coefficient] at coefficient
  rw [mul_assoc,coefficient]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Kinetic
