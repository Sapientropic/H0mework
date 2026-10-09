import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0Recognition
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceDilationMomentum
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ClockPhiCoframeDriftMomentumPrimitive
open GaussCoreDifferential GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceClockPhiOriginalGaussianH0FirstJet SourceClockPhiMatchedDiffusionSource
open SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarDoubleCurrent
open SourceClockPhiCombinedScalePressure
open SourceDilationMomentum SourceDilationMultiplier
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev V:End:=volumeAction
private abbrev P(i:Fin 6):End:=GaussCoframeCore.momentum i
private abbrev G(i:Fin 6):End:=gradientAction i
private abbrev Ci(i:Fin 6):End:=sourceCurrentColumn i
private abbrev Dc:End:=SourceCoframeVolumeCurrent.dilation
private abbrev D:End:=combinedGenerator
private abbrev B:End:=SourceClockPhiMatchedDiffusionSource.driftClock

private theorem uv_right:V*U=(1:End):=by
  apply LinearMap.ext
  exact volume_inverse
private theorem uv_commute:Commute U V:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)=
    (volume z:ℂ) • ((reciprocalVolume z:ℂ) • f z)
  simp only [smul_smul]
  congr 1
  ring
private theorem uv_left:U*V=(1:End):=by
  rw [uv_commute.eq]
  exact uv_right
private theorem ug_commute(i:Fin 6):Commute U (G i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z:ℂ) • ((volumeGradient z i:ℂ) • f z)=
    (volumeGradient z i:ℂ) • ((reciprocalVolume z:ℂ) • f z)
  simp only [smul_smul]
  congr 1
  ring
private theorem current_factor(i:Fin 6):Ci i=U*G i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (((reciprocalVolume z*volumeGradient z i:ℝ):ℂ) • f z)=
    (reciprocalVolume z:ℂ) • ((volumeGradient z i:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_mul]
private theorem current_u_commute(i:Fin 6):Commute (Ci i) U:=by
  rw [current_factor]
  exact ((Commute.refl U).mul_right (ug_commute i)).symm
private theorem p_volume(i:Fin 6):P i*V=V*P i+(-Complex.I) • G i:=by
  apply LinearMap.ext
  exact momentum_volume i

theorem bare_momentum_inverse_volume(i:Fin 6):
    P i*U=U*P i+Complex.I • (U*Ci i):=by
  have hVP:V*P i=P i*V+Complex.I • G i:=by
    linear_combination (norm:=module) -(p_volume i)
  calc
    P i*U=(U*V)*(P i*U):=by rw [uv_left];simp
    _=U*((V*P i)*U):=by noncomm_ring
    _=U*((P i*V+Complex.I • G i)*U):=by rw [hVP]
    _=U*P i+Complex.I • (U*Ci i):=by
      rw [current_factor]
      simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc]
      rw [mul_assoc (P i) V U,uv_right]
      simp only [mul_one]
      rw [←(ug_commute i).eq]

private theorem d_p(i:Fin 6):bracket Dc (P i)=(2*Complex.I/3) • P i:=
  SourceDilationMomentum.coframe_momentum_current i
private theorem d_u:bracket Dc U=(2*Complex.I) • U:=by
  have h:=congrArg (fun X:End=>(-2*Complex.I/3) • X) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=1:=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  have hc:(-2*Complex.I/3)*(-3:ℂ)=2*Complex.I:=by ring
  rw [hi,one_smul,hc] at h
  exact h
private theorem p_u(i:Fin 6):bracket (P i) U=Complex.I • (U*Ci i):=by
  unfold bracket
  linear_combination (norm:=module) bare_momentum_inverse_volume i
private theorem bracket_smul_right(X Y:End)(c:ℂ):
    bracket X (c • Y)=c • bracket X Y:=by
  unfold bracket
  simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bracket_smul_left(X Y:End)(c:ℂ):
    bracket (c • X) Y=c • bracket X Y:=by
  unfold bracket
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_product(X Y Z:End):
    bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z:=by
  unfold bracket
  noncomm_ring
private theorem bracket_jacobi(X Y Z:End):
    bracket X (bracket Y Z)=bracket (bracket X Y) Z+bracket Y (bracket X Z):=by
  unfold bracket
  noncomm_ring

private theorem current_dilation(i:Fin 6):
    bracket Dc (Ci i)=(2*Complex.I/3) • Ci i:=by
  have hj:=bracket_jacobi Dc (P i) U
  rw [p_u,bracket_smul_right,d_p,d_u,bracket_smul_left,bracket_smul_right,p_u] at hj
  have hUC:bracket Dc (U*Ci i)=(8*Complex.I/3) • (U*Ci i):=by
    have hh:=congrArg (fun X:End=>(-Complex.I) • X) hj
    simp only [smul_add,smul_smul] at hh
    have h1:(-Complex.I)*Complex.I=(1:ℂ):=by
      calc _= -(Complex.I*Complex.I):=by ring
           _=_:=by rw [Complex.I_mul_I];ring
    have h2:(-Complex.I)*((2*Complex.I/3)*Complex.I)=2*Complex.I/3:=by
      calc _=((-Complex.I)*Complex.I)*(2*Complex.I/3):=by ring
           _=2*Complex.I/3:=by rw [h1,one_mul]
    have h3:(-Complex.I)*(2*Complex.I*Complex.I)=2*Complex.I:=by
      calc _=((-Complex.I)*Complex.I)*(2*Complex.I):=by ring
           _=2*Complex.I:=by rw [h1,one_mul]
    rw [h1,one_smul,h2,h3,←add_smul] at hh
    convert hh using 1
    ring
  rw [bracket_product,d_u] at hUC
  simp only [smul_mul_assoc] at hUC
  have hU:U*bracket Dc (Ci i)=(2*Complex.I/3) • (U*Ci i):=by
    linear_combination (norm:=module) hUC
  have hh:=congrArg (fun X:End=>V*X) hU
  simpa only [←mul_assoc,uv_right,one_mul,mul_smul_comm,smul_mul_assoc] using hh

private theorem combined_delta(T:End):bracket D T=deltaPhi T-deltaGauge T:=by
  unfold D combinedGenerator bracket
  rw [sub_mul,mul_sub]
  have hp:=SourceScalarAffineScaleTransport.generator_commutator T
  have hg:=SourceGaugeScaleTransport.generator_commutator T
  linear_combination (norm:=module) hp-hg
private theorem p_d(i:Fin 6):P i*D=D*P i:=by
  have hp:=original_coframe_direction_phi_gauge i
  have h:bracket D (P i)=0:=by
    rw [combined_delta,hp.1,hp.2.1,sub_self]
  exact (sub_eq_zero.mp h).symm
private theorem drift_decompose:
    B=U*D+(3*Complex.I) • (Dc*U)+(3:ℂ) • U:=by
  rfl

theorem bare_momentum_drift_row(i:Fin 6):
    P i*B=B*P i+(2:ℂ) • (U*P i)+Complex.I • (Ci i*B):=by
  have h1:P i*U-U*P i-Complex.I • (U*Ci i)=0:=sub_eq_zero.mpr (p_u i)
  have h2:P i*D-D*P i=0:=sub_eq_zero.mpr (p_d i)
  have h3:Dc*P i-P i*Dc-(2*Complex.I/3) • P i=0:=sub_eq_zero.mpr (d_p i)
  have h4:Dc*Ci i-Ci i*Dc-(2*Complex.I/3) • Ci i=0:=
    sub_eq_zero.mpr (current_dilation i)
  have h5:U*Ci i-Ci i*U=0:=sub_eq_zero.mpr (current_u_commute i).eq.symm
  have hI:(Complex.I*Complex.I+1:ℂ) •
      ((2:ℂ) • (P i*U)+(3:ℂ) • (Ci i*Dc*U)-
        (3:ℂ) • (Dc*U*Ci i))=0:=by
    have hi:(Complex.I*Complex.I+1:ℂ)=0:=by rw [Complex.I_mul_I];ring
    rw [hi,zero_smul]
  rw [drift_decompose]
  linear_combination (norm:=noncomm_ring)
    h1*D + U*h2 + Complex.I • (h5*D) +
    (3*Complex.I) • (Dc*h1) + (5:ℂ) • h1 -
    (3*Complex.I) • (h3*U) - (3:ℂ) • (Dc*h5) -
    (3:ℂ) • (h4*U) + (5*Complex.I) • h5 - hI
  module

end LowEnergy.ClockPhiCoframeDriftMomentumPrimitive
