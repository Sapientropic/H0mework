import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceDilationRemainder
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceOriginalKineticSquare

/-! The original full Hamiltonian generates an exact signed square on its own core. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceOriginalHamiltonianSquare
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussCoframeForm GaussMatterCore GaussDiagonalHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceKineticTranspose SourceHamiltonianVolume SourceDilationKinetic SourceDilationRemainder
open SourceOriginalKineticSquare (radialCoefficient)
open scoped InnerProductSpace

def signedAction : CoreEnd :=
  gaugeKinetic+(1/2 : ℂ) • matterAction+(3/2 : ℂ) • localAction+spatialAction

def symmetricScale : CoreEnd :=
  diagonalAction*volumeAction+(2*Complex.I*(radialCoefficient : ℂ)) • dilation

theorem symmetric_scale_source :
    symmetricScale=(1/2 : ℂ) • (diagonalAction*volumeAction+volumeAction*diagonalAction) := by
  have h := full_source_volume_current
  have he : volumeAction*diagonalAction=
      diagonalAction*volumeAction-(-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation := by
    rw [←h]
    abel
  rw [he]
  unfold symmetricScale radialCoefficient
  push_cast
  module

theorem symmetric_scale_pair (f g : QuantumTest) :
    sourcePair (symmetricScale f) g=sourcePair f (symmetricScale g) := by
  have hH (x y : QuantumTest) : sourcePair (diagonalAction x) y=sourcePair x (diagonalAction y) :=
    (diagonalAction_pair x y).symm
  have hU (x y : QuantumTest) : sourcePair (volumeAction x) y=sourcePair x (volumeAction y) :=
    (multiply_pair _ _ x y).symm
  rw [symmetric_scale_source]
  change sourcePair ((1/2 : ℂ) • (diagonalAction (volumeAction f)+volumeAction (diagonalAction f))) g=
    sourcePair f ((1/2 : ℂ) • (diagonalAction (volumeAction g)+volumeAction (diagonalAction g)))
  simp only [sourcePair,map_smul,map_add,inner_smul_left,inner_smul_right,inner_add_left,
    inner_add_right,map_div₀,map_one,map_ofNat]
  change (1/2 : ℂ)*(sourcePair (diagonalAction (volumeAction f)) g+
      sourcePair (volumeAction (diagonalAction f)) g)=
    (1/2 : ℂ)*(sourcePair f (diagonalAction (volumeAction g))+
      sourcePair f (volumeAction (diagonalAction g)))
  rw [hH (volumeAction f) g,hU f (diagonalAction g),hU (diagonalAction f) g,hH f (volumeAction g)]
  ring

theorem matter_volume : Commute matterAction volumeAction := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,matterAction,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  exact LinearMap.congr_fun
    (scalar_volume_commutes (fun z => GaussQuantumMultiplier.quantized (localMatrix i b z))
      (GaussMatterCore.local_smooth i b)).eq f

theorem signed_volume : Commute signedAction volumeAction :=
  ((gauge_kinetic_volume.add_left (matter_volume.smul_left (1/2 : ℂ))).add_left
    ((real_volume _ _).smul_left (3/2 : ℂ))).add_left (real_volume _ _)

set_option maxRecDepth 2048 in
theorem original_scale_current :
    symmetricScale*dilation-dilation*symmetricScale=
      (8*Complex.I/3) • (volumeAction*signedAction) := by
  have h : dilation*diagonalAction-diagonalAction*dilation=
      (2*Complex.I) • diagonalAction-(8*Complex.I/3) • signedAction := by
    rw [full_source_scale_current,original_action_split]
    unfold signedAction
    module
  unfold symmetricScale
  exact SourceKineticSquare.scale_current (R := CoreEnd) diagonalAction volumeAction dilation
    signedAction radialCoefficient h volume_scale_current signed_volume.eq

theorem original_hamiltonian_square (f : QuantumTest) :
    ‖embed (diagonalAction (volumeAction f))‖^2=
      ‖embed (symmetricScale f)‖^2+4*radialCoefficient^2*‖embed (dilation f)‖^2+
        sourceTime 0*(sourcePair f (volumeAction (gaugeKinetic f))).re+
        (sourceTime 0/2)*(sourcePair f (volumeAction (matterAction f))).re+
        (3*sourceTime 0/2)*(sourcePair f (volumeAction (localAction f))).re+
        sourceTime 0*(sourcePair f (volumeAction (spatialAction f))).re := by
  have hs := SourceKineticSquare.current_square embed symmetricScale dilation
    (volumeAction*signedAction) symmetric_scale_pair (fun x y => (dilation_pair x y).symm)
      original_scale_current radialCoefficient f
  have hvalue : symmetricScale f-(2*Complex.I*(radialCoefficient : ℂ)) • dilation f=
      diagonalAction (volumeAction f) := by
    change (diagonalAction (volumeAction f)+(2*Complex.I*(radialCoefficient : ℂ)) • dilation f)-
      (2*Complex.I*(radialCoefficient : ℂ)) • dilation f=_
    abel
  have hc : 16*radialCoefficient/3=sourceTime 0 := by unfold radialCoefficient; ring
  rw [hvalue,hc] at hs
  change ‖embed (diagonalAction (volumeAction f))‖^2=
    ‖embed (symmetricScale f)‖^2+4*radialCoefficient^2*‖embed (dilation f)‖^2+
      sourceTime 0*(sourcePair f (volumeAction (signedAction f))).re at hs
  have hp : sourcePair f (volumeAction (signedAction f))=
      sourcePair f (volumeAction (gaugeKinetic f))+
      (1/2 : ℂ)*sourcePair f (volumeAction (matterAction f))+
      (3/2 : ℂ)*sourcePair f (volumeAction (localAction f))+
      sourcePair f (volumeAction (spatialAction f)) := by
    simp only [signedAction,LinearMap.add_apply,LinearMap.smul_apply,sourcePair,
      map_add,map_smul,inner_add_right,inner_smul_right]
  rw [hp] at hs
  norm_num [Complex.add_re,Complex.mul_re,Complex.div_re,Complex.div_im] at hs
  convert hs using 1
  ring

end LowEnergy.SourceOriginalHamiltonianSquare
