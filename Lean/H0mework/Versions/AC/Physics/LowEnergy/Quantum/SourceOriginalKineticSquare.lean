import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceDilationKinetic

/-! The actual source scale and volume currents generate the original kinetic square. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceOriginalKineticSquare
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussCoframeForm SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceKineticTranspose SourceHamiltonianVolume SourceDilationKinetic
open scoped InnerProductSpace

def radialCoefficient : ℝ := 3*sourceTime 0/16

def symmetricScale : CoreEnd :=
  kineticAction*volumeAction+(2*Complex.I*(radialCoefficient : ℂ)) • dilation

theorem symmetric_scale_source :
    symmetricScale=(1/2 : ℂ) • (kineticAction*volumeAction+volumeAction*kineticAction) := by
  have h := kinetic_volume_current
  have he : volumeAction*kineticAction=
      kineticAction*volumeAction-(-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation := by
    rw [←h]
    abel
  rw [he]
  unfold symmetricScale radialCoefficient
  push_cast
  module

theorem symmetric_scale_pair (f g : QuantumTest) :
    sourcePair (symmetricScale f) g=sourcePair f (symmetricScale g) := by
  have hH (x y : QuantumTest) : sourcePair (kineticAction x) y=sourcePair x (kineticAction y) := by
    have h := kinetic_pair (coreEquiv x) (coreEquiv y)
    change sourcePair (kineticAction (coreEquiv.symm (coreEquiv x))) y=
      sourcePair x (kineticAction (coreEquiv.symm (coreEquiv y))) at h
    simpa only [coreEquiv.symm_apply_apply] using h
  have hU (x y : QuantumTest) : sourcePair (volumeAction x) y=sourcePair x (volumeAction y) :=
    (multiply_pair _ _ x y).symm
  rw [symmetric_scale_source]
  change sourcePair ((1/2 : ℂ) • (kineticAction (volumeAction f)+volumeAction (kineticAction f))) g=
    sourcePair f ((1/2 : ℂ) • (kineticAction (volumeAction g)+volumeAction (kineticAction g)))
  simp only [sourcePair,map_smul,map_add,inner_smul_left,inner_smul_right,inner_add_left,
    inner_add_right,map_div₀,map_one,map_ofNat]
  change (1/2 : ℂ)*(sourcePair (kineticAction (volumeAction f)) g+
      sourcePair (volumeAction (kineticAction f)) g)=
    (1/2 : ℂ)*(sourcePair f (kineticAction (volumeAction g))+
      sourcePair f (volumeAction (kineticAction g)))
  rw [hH (volumeAction f) g,hU f (kineticAction g),hU (kineticAction f) g,hH f (volumeAction g)]
  ring

set_option maxRecDepth 2048 in
theorem original_scale_current :
    symmetricScale*dilation-dilation*symmetricScale=
      (8*Complex.I/3) • (volumeAction*gaugeKinetic) :=
by
  unfold symmetricScale
  exact SourceKineticSquare.scale_current (R := CoreEnd) kineticAction volumeAction dilation
    gaugeKinetic radialCoefficient kinetic_scale_current volume_scale_current gauge_kinetic_volume.eq

theorem original_kinetic_square (f : QuantumTest) :
    ‖embed (kineticAction (volumeAction f))‖^2=
      ‖embed (symmetricScale f)‖^2+4*radialCoefficient^2*‖embed (dilation f)‖^2+
        sourceTime 0*(sourcePair f (volumeAction (gaugeKinetic f))).re := by
  have hs := SourceKineticSquare.current_square embed symmetricScale dilation
    (volumeAction*gaugeKinetic) symmetric_scale_pair (fun x y => (dilation_pair x y).symm) original_scale_current
    radialCoefficient f
  have hvalue : symmetricScale f-(2*Complex.I*(radialCoefficient : ℂ)) • dilation f=
      kineticAction (volumeAction f) := by
    change (kineticAction (volumeAction f)+(2*Complex.I*(radialCoefficient : ℂ)) • dilation f)-
      (2*Complex.I*(radialCoefficient : ℂ)) • dilation f=_
    abel
  have hc : 16*radialCoefficient/3=sourceTime 0 := by unfold radialCoefficient; ring
  rw [hvalue,hc] at hs
  exact hs

end LowEnergy.SourceOriginalKineticSquare
