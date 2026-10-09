import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCurrentMomentumContacts

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNumberRadialReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumLegendreCurrentReturn PreparationVacuumGaussMeasureReturn
open PreparationVacuumSpinGaussContraction
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier SourceQuantumScalarChart
open Stage9C.Material.SpinPair GaussLiveMomentum
open scoped Topology ContDiff BigOperators Matrix

private def sourceRadialCoordinate (i : Fin 6) : SourceCoordinateSlice→L[ℝ] ℝ:=
  (PiLp.proj 2 (fun _ : Fin 6=>ℝ) i).comp (ContinuousLinearMap.fst ℝ Coframe Slice)

def sourceRadialVolumeGradient (z : SourceCoordinateSlice) (i : Fin 6) : ℝ:=
  (GaussCoframeCore.coframeDirection i).1 0*z.1 2*z.1 5+
    z.1 0*(GaussCoframeCore.coframeDirection i).1 2*z.1 5+
      z.1 0*z.1 2*(GaussCoframeCore.coframeDirection i).1 5

private theorem sourceRadialVolume_derivative (z : SourceCoordinateSlice) (i : Fin 6) :
    fderiv ℝ GaussNativeEnergy.volume z (GaussCoframeCore.coframeDirection i)=sourceRadialVolumeGradient z i:=by
  have actual:=(((sourceRadialCoordinate 0).hasFDerivAt (x:=z)).mul
    ((sourceRadialCoordinate 2).hasFDerivAt (x:=z))).mul ((sourceRadialCoordinate 5).hasFDerivAt (x:=z))
  change HasFDerivAt GaussNativeEnergy.volume _ z at actual
  rw [actual.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change (z.1 0*z.1 2)*(GaussCoframeCore.coframeDirection i).1 5+
    z.1 5*(z.1 0*(GaussCoframeCore.coframeDirection i).1 2+
      z.1 2*(GaussCoframeCore.coframeDirection i).1 0)=_
  unfold sourceRadialVolumeGradient
  ring

theorem sourceRadialVolume_numberConnection (z : physicalChart) (i : Fin 6) :
    sourceRadialVolumeGradient z.val i=2*GaussNativeEnergy.volume z.val*sourceNumberConnection z.val.1 i:=by
  have positive:=(GaussNativeEnergy.volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at positive
  have q0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  have q2:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).2
  have q5:=(mul_ne_zero_iff.mp positive).2
  fin_cases i <;>
    simp [sourceRadialVolumeGradient,GaussCoframeCore.coframeDirection,GaussNativeEnergy.volume,
      sourceNumberConnection] <;> field_simp

theorem sourceRadialCoefficient_derivative (z : physicalChart) (i j : Fin 6) :
    fderiv ℝ (sourceRadialCoefficient i) z.val (GaussCoframeCore.coframeDirection j)=
      -(lapse/(4*GaussNativeEnergy.volume z.val))*
        ((if i=j then 1 else 0)-2*z.val.1 i*sourceNumberConnection z.val.1 j):=by
  have volume:=(GaussNativeEnergy.volume_smooth.differentiable (by simp)).differentiableAt (x:=z.val)
  have denominator : 4*GaussNativeEnergy.volume z.val≠0:=mul_ne_zero (by norm_num) (GaussNativeEnergy.volume_pos z).ne'
  have denominatorJet:=(hasFDerivAt_const (4:ℝ) z.val).mul volume.hasFDerivAt
  have inverseJet:=(hasFDerivAt_inv denominator).comp z.val denominatorJet
  have actual:=((hasFDerivAt_const lapse z.val).mul inverseJet).neg.mul
    (sourceRadialCoordinate i).hasFDerivAt
  change HasFDerivAt (sourceRadialCoefficient i) _ z.val at actual
  rw [actual.fderiv]
  have coord (w : SourceCoordinateSlice) : sourceRadialCoordinate i w=w.1 i:=rfl
  simp only [add_apply,smul_apply,neg_apply,zero_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,Pi.mul_apply,Pi.neg_apply,
    Function.comp_apply,coord,mul_zero,add_zero]
  rw [sourceRadialVolume_derivative,sourceRadialVolume_numberConnection]
  have coordinate : (GaussCoframeCore.coframeDirection j).1 i=if i=j then 1 else 0:=by
    simp [GaussCoframeCore.coframeDirection]
  rw [coordinate]
  have nonzero:=(GaussNativeEnergy.volume_pos z).ne'
  field_simp
  ring

theorem sourceRadialEuler_numberConnection (z : physicalChart) :
    ∑i : Fin 6,z.val.1 i*sourceNumberConnection z.val.1 i=(3/2:ℝ):=by
  have positive:=(GaussNativeEnergy.volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at positive
  have q0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  have q2:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).2
  have q5:=(mul_ne_zero_iff.mp positive).2
  norm_num [Fin.sum_univ_six,sourceNumberConnection]
  field_simp
  ring

theorem sourceRadialCoefficient_divergence (z : physicalChart) :
    (∑i : Fin 6,fderiv ℝ (sourceRadialCoefficient i) z.val (GaussCoframeCore.coframeDirection i))=
      -3*lapse/(4*GaussNativeEnergy.volume z.val):=by
  simp only [sourceRadialCoefficient_derivative,ite_true,mul_sub,mul_one,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_assoc,←Finset.mul_sum]
  rw [sourceRadialEuler_numberConnection]
  ring

theorem sourceRadialCoefficient_density (z : physicalChart) :
    (∑i : Fin 6,sourceRadialCoefficient i z.val*sourceNumberConnection z.val.1 i)=
      -3*lapse/(8*GaussNativeEnergy.volume z.val):=by
  simp only [sourceRadialCoefficient,mul_assoc,←Finset.mul_sum]
  rw [sourceRadialEuler_numberConnection]
  ring

end LowEnergy.PreparationVacuumNumberRadialReturn
