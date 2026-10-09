import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0RealPrimitives
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0LocalSpinNumber
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarVirialBulk SourceScalarGaugeScale SourceGaugeRadialCurrent SourceGaugeRadialPair
open SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure SourceScalarDoubleCurrent
open SourceCoframeVolumeCurrent SourceDilationAlgebra SourceDilationMultiplier SourceHamiltonianScaleJet
open SourceClockPhiOriginalGaussianH0Recognition SourceClockPhiOriginalGaussianH0RealPrimitives
open SourceCoframeCovariantSquare SourceCoframeVolume SourceCoframeVolumeCurrent
open scoped Topology ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev a:End:=inverseRootAction
private abbrev D:End:=combinedGenerator
private theorem combined_invariant_local(T:End)(B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (law:∀f z,T f z=B z (f z))
    (hPhi:∀r z,B (SourceClockPhiOriginalGaussianH0RealPrimitives.phiScale r z)=B z)
    (hGauge:∀r z,B (gaugeScale r z)=B z):Commute D T:=by
  have hp:=phi_invariant_local T B law hPhi
  have hg:=gauge_invariant_local T B law hGauge
  have hsrc:bracket D T=deltaPhi T-deltaGauge T:=by
    have h1:=SourceScalarAffineScaleTransport.generator_commutator T
    have h2:=SourceGaugeScaleTransport.generator_commutator T
    calc
      bracket D T=(SourceScalarAffineScaleTransport.generator*T-
        T*SourceScalarAffineScaleTransport.generator)-
        (SourceGaugeScaleTransport.generator*T-
          T*SourceGaugeScaleTransport.generator):=by
          unfold bracket D combinedGenerator
          noncomm_ring
      _=_:=by rw [h1,h2]
  rw [hp,hg,sub_self] at hsrc
  exact sub_eq_zero.mp hsrc
private theorem root_local(T:End)(B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (law:∀f z,T f z=B z (f z)):Commute a T:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (inverseRootVolume z:ℂ) • T f z=T (a f) z
  rw [law,law]
  exact ((B z).map_smul (inverseRootVolume z:ℂ) (f z)).symm
private theorem inverse_of_root(T:End)(h:Commute a T):Commute U T:=by
  have hs:a*a=U:=by
    apply LinearMap.ext
    exact inverse_root_square
  rw [←hs]
  exact h.mul_left h

private theorem spin_local(i:Fin 7):
    Commute D (GaussCoframeSpin.current i) ∧
    Commute a (GaussCoframeSpin.current i):=by
  let B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber:=
    fun _=>GaussQuantumMultiplier.quantized (GaussCoframeSpin.full i)
  have law:∀f z,GaussCoframeSpin.current i f z=B z (f z):=by
    intro f z
    rfl
  exact ⟨combined_invariant_local _ B law (by intros; rfl) (by intros; rfl),
    root_local _ B law⟩

private theorem number_local:
    Commute D GaussCoframeForm.number ∧
    Commute a GaussCoframeForm.number:=by
  let B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber:=fun _=>fiberNumber
  have law:∀f z,GaussCoframeForm.number f z=B z (f z):=by
    intro f z
    apply PiLp.ext
    intro word
    exact (GaussCoframeForm.number_apply f z word).trans
      (fiberNumber_apply (f z) word).symm
  exact ⟨combined_invariant_local _ B law (by intros; rfl) (by intros; rfl),
    root_local _ B law⟩

private theorem inverse_volume_local:
    Commute D (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth) ∧
    Commute a (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth):=by
  let T:End:=multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth
  let B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber:=
    fun z=>(GaussCoframeForm.inverseVolume z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
  have law:∀f z,T f z=B z (f z):=by
    intro f z
    rfl
  have hp:∀r z,B (SourceClockPhiOriginalGaussianH0RealPrimitives.phiScale r z)=B z:=by
    intro r z
    rfl
  have hg:∀r z,B (gaugeScale r z)=B z:=by
    intro r z
    rfl
  exact ⟨combined_invariant_local T B law hp hg,root_local T B law⟩

private theorem number_coefficient_local:
    Commute D (multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth) ∧
    Commute a (multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth):=by
  let T:End:=multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth
  let B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber:=
    fun z=>(GaussCoframeForm.numberCoefficient z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
  have law:∀f z,T f z=B z (f z):=by intro f z; rfl
  have hp:∀r z,B (SourceClockPhiOriginalGaussianH0RealPrimitives.phiScale r z)=B z:=by
    intro r z
    rfl
  have hg:∀r z,B (gaugeScale r z)=B z:=by intro r z; rfl
  exact ⟨combined_invariant_local T B law hp hg,root_local T B law⟩

private theorem spin_remainder_local:
    Commute D spinRemainder ∧ Commute a spinRemainder:=by
  constructor
  · unfold spinRemainder
    exact Commute.sum_right _ _ _ (fun i _=>
      (((spin_local i).1.mul_right inverse_volume_local.1).mul_right (spin_local i).1).smul_right _)
  · unfold spinRemainder
    exact Commute.sum_right _ _ _ (fun i _=>
      (((spin_local i).2.mul_right inverse_volume_local.2).mul_right (spin_local i).2).smul_right _)

private theorem number_shift_local:
    Commute D GaussCoframeForm.numberShift ∧
    Commute a GaussCoframeForm.numberShift:=by
  constructor
  · unfold GaussCoframeForm.numberShift
    exact ((number_local.1.mul_right number_coefficient_local.1).add_right
      (number_coefficient_local.1.mul_right number_local.1)).smul_right _
  · unfold GaussCoframeForm.numberShift
    exact ((number_local.2.mul_right number_coefficient_local.2).add_right
      (number_coefficient_local.2.mul_right number_local.2)).smul_right _

private theorem scale_of_dilation(T:End)
    (h:SourceCoframeVolumeCurrent.dilation*T-T*SourceCoframeVolumeCurrent.dilation=
      (2*Complex.I) • T):scaleDerivative T=(-3:ℂ) • T:=by
  change (3*Complex.I/2:ℂ) •
    (SourceCoframeVolumeCurrent.dilation*T-T*SourceCoframeVolumeCurrent.dilation)=_
  rw [h,smul_smul]
  congr 1
  calc
    (3*Complex.I/2:ℂ)*(2*Complex.I)=3*(Complex.I*Complex.I):=by ring
    _=(-3:ℂ):=by rw [Complex.I_mul_I];ring

private theorem spin_remainder_scale:scaleDerivative spinRemainder=(-3:ℂ) • spinRemainder:=by
  have hterm(i:Fin 7):
      dilation*((SourceCoframeCovariantSquare.residualWeight i:ℂ) •
        (GaussCoframeSpin.current i*
          multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
          GaussCoframeSpin.current i))-
      ((SourceCoframeCovariantSquare.residualWeight i:ℂ) •
        (GaussCoframeSpin.current i*
          multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
          GaussCoframeSpin.current i))*dilation=
      (2*Complex.I) • ((SourceCoframeCovariantSquare.residualWeight i:ℂ) •
        (GaussCoframeSpin.current i*
          multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
          GaussCoframeSpin.current i)):=by
    have hs:dilation*GaussCoframeSpin.current i-
        GaussCoframeSpin.current i*dilation=(0:ℂ) • GaussCoframeSpin.current i:=by
      simpa only [zero_smul] using SourceDilationKinetic.spin_current i
    have h1:=homogeneous_mul dilation (GaussCoframeSpin.current i)
      (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth)
      0 (2*Complex.I) hs inverse_volume_commutator
    have h2:=homogeneous_mul dilation
      (GaussCoframeSpin.current i*
        multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth)
      (GaussCoframeSpin.current i) (0+2*Complex.I) 0 h1 hs
    have h3:=homogeneous_smul dilation
      (GaussCoframeSpin.current i*
        multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
        GaussCoframeSpin.current i) (2*Complex.I)
      (SourceCoframeCovariantSquare.residualWeight i:ℂ)
      (by simpa only [zero_add,add_zero] using h2)
    exact h3
  have h:=homogeneous_sum dilation (fun i:Fin 7=>(SourceCoframeCovariantSquare.residualWeight i:ℂ) •
    (GaussCoframeSpin.current i*
      multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
      GaussCoframeSpin.current i)) (2*Complex.I) hterm
  exact scale_of_dilation spinRemainder (by simpa only [spinRemainder] using h)

private theorem number_shift_scale:scaleDerivative GaussCoframeForm.numberShift=
    (-3:ℂ) • GaussCoframeForm.numberShift:=
  scale_of_dilation _ SourceDilationKinetic.number_shift_current

theorem spin_remainder_complete_current:
    SourceClockPhiMatchedDiffusionSource.completeCurrent spinRemainder=
      (-12:ℂ) • (U*spinRemainder):=by
  have hd:=spin_remainder_local.1
  have ha:=spin_remainder_local.2
  have hu:=inverse_of_root _ ha
  have hD:bracket D spinRemainder=(-0:ℂ) • spinRemainder:=by
    change D*spinRemainder-spinRemainder*D=_
    rw [hd.eq,sub_self]
    simp
  have hl:=forward_bracket_of_scale spinRemainder (-3) hu spin_remainder_scale
  have h:=complete_current_homogeneous spinRemainder (-2/3) 0 hu ha hD
    (by convert hl using 1; norm_num)
  simpa only [show (0:ℂ)*0-3*0+18*(-2/3)=(-12:ℂ) by norm_num] using h

theorem number_shift_complete_current:
    SourceClockPhiMatchedDiffusionSource.completeCurrent GaussCoframeForm.numberShift=
      (-12:ℂ) • (U*GaussCoframeForm.numberShift):=by
  have hd:=number_shift_local.1
  have ha:=number_shift_local.2
  have hu:=inverse_of_root _ ha
  have hD:bracket D GaussCoframeForm.numberShift=(-0:ℂ) • GaussCoframeForm.numberShift:=by
    change D*GaussCoframeForm.numberShift-GaussCoframeForm.numberShift*D=_
    rw [hd.eq,sub_self]
    simp
  have hl:=forward_bracket_of_scale GaussCoframeForm.numberShift (-3) hu number_shift_scale
  have h:=complete_current_homogeneous GaussCoframeForm.numberShift (-2/3) 0 hu ha hD
    (by convert hl using 1; norm_num)
  simpa only [show (0:ℂ)*0-3*0+18*(-2/3)=(-12:ℂ) by norm_num] using h

end LowEnergy.SourceClockPhiOriginalGaussianH0LocalSpinNumber
