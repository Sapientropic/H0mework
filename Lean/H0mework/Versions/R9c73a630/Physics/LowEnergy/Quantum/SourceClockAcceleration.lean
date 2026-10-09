import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceCharacteristicRadiusCurrent
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceDilationRemainder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockAcceleration
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumScalarChart
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceCoframeDilation
open SourceScalarPairedTransport SourceCharacteristicRadiusCurrent SourceKineticTranspose SourceDilationRemainder
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction dilation

def clock : End := (1/2:ℂ) • (characteristicAction false+characteristicAction true)
def clockCurrent : End := Complex.I • (diagonalAction*clock-clock*diagonalAction)
def clockAcceleration : End := (-Complex.I) • (diagonalAction*clockCurrent-clockCurrent*diagonalAction)

private theorem log_smooth (z : physicalChart) : ContDiffAt ℝ ∞ (fun x => Real.log (volume x)) z.val :=
  volume_smooth.contDiffAt.log (volume_pos z).ne'

theorem original_clock : clock=multiply (fun z => Real.log (volume z)) log_smooth := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (1/2:ℂ) • ((characteristic false z : ℂ) • f z+(characteristic true z : ℂ) • f z)=_
  change _=(Real.log (volume z) : ℂ) • f z
  simp only [characteristic,orientation,Bool.false_eq_true,↓reduceIte,Complex.ofReal_add,
    Complex.ofReal_mul,Complex.ofReal_neg,smul_smul,←add_smul]
  congr 1
  ring

private def gradient (i : Fin 6) (z : SourceCoordinateSlice) : ℝ := volumeGradient z i/volume z
private theorem gradient_smooth (i : Fin 6) (z : physicalChart) : ContDiffAt ℝ ∞ (gradient i) z.val := by
  have hg : ContDiff ℝ ∞ (fun x : SourceCoordinateSlice => volumeGradient x i) := by
    fin_cases i <;> dsimp [volumeGradient] <;> fun_prop
  exact hg.contDiffAt.div volume_smooth.contDiffAt (volume_pos z).ne'
private def gradientAction (i : Fin 6) : End := multiply (gradient i) (gradient_smooth i)
private def flux : End := ∑ i : Fin 6, ∑ j : Fin 6,
  (GaussCoframeCore.adjoint i*(coefficientAction i j*gradientAction j)+
    gradientAction i*(coefficientAction i j*GaussCoframeCore.momentum j))
private def nativeGradient (negative : Bool) (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  orientation negative*(inner ℝ (z.2.1 : Scalar) v.1/(4*radius z))
private theorem native_gradient_smooth (negative : Bool) (v : Ambient) : ContDiff ℝ ∞ (nativeGradient negative v) :=
  contDiff_const.mul (((scalarCoordinate.contDiff.inner ℝ contDiff_const).div
    (contDiff_const.mul radius_smooth) (fun z => mul_ne_zero (by norm_num) (radius_pos z).ne')))
private def nativeContact (negative : Bool) (v : Ambient) : End :=
  multiply (nativeGradient negative v) (fun _ => (native_gradient_smooth negative v).contDiffAt)
private def scalarFlux (negative : Bool) : End := ∑ a : ScalarIndex,
  (GaussMomentumAdjoint.adjoint (scalarDirection a)*(multiply scalarWeight scalarWeight_smooth*nativeContact negative (scalarDirection a))+
  nativeContact negative (scalarDirection a)*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)))
private theorem native_contact_neg (v : Ambient) : nativeContact true v= -nativeContact false v := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((nativeGradient true v z : ℝ) : ℂ) • f z= -(((nativeGradient false v z : ℝ) : ℂ) • f z)
  simp only [nativeGradient,orientation,Bool.false_eq_true,↓reduceIte,neg_mul,Complex.ofReal_neg,neg_smul]
private theorem scalar_flux_neg : scalarFlux true= -scalarFlux false := by
  unfold scalarFlux
  simp only [native_contact_neg,mul_neg,neg_mul,←neg_add,Finset.sum_neg_distrib]

private theorem clock_current_flux : clockCurrent=flux := by
  have hp := original_characteristic_current false
  have hm := original_characteristic_current true
  have hx : diagonalAction*clock-clock*diagonalAction=
      (1/2:ℂ) • (characteristicCurrent false+characteristicCurrent true) := by
    rw [←hp,←hm]
    unfold clock
    simp only [mul_smul_comm,smul_mul_assoc,mul_add,add_mul,smul_add]
    module
  unfold clockCurrent
  rw [hx]
  change Complex.I • ((1/2:ℂ) • (((-Complex.I) • flux+(-Complex.I/2) • scalarFlux false)+
    ((-Complex.I) • flux+(-Complex.I/2) • scalarFlux true)))=flux
  rw [scalar_flux_neg]
  have he : (((-Complex.I) • flux+(-Complex.I/2) • scalarFlux false)+
      ((-Complex.I) • flux+(-Complex.I/2) • (-scalarFlux false)))=(-2*Complex.I) • flux := by module
  rw [he,smul_smul,smul_smul]
  have hi : Complex.I*(1/2:ℂ)*(-2*Complex.I)=1 := by
    calc
      _= -(Complex.I*Complex.I) := by ring
      _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul]

private theorem gradient_contraction (i : Fin 6) :
    (∑ j : Fin 6,coefficientAction i j*gradientAction j)=
      ((sourceTime 0:ℂ)/4) • (coordinateAction i*inverseVolumeAction) := by
  have he (j : Fin 6) : coefficientAction i j*gradientAction j=
      (coefficientAction i j*SourceCoframeVolume.gradientAction j)*inverseVolumeAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (GaussCoframeKinetic.coefficient i j z : ℂ) • ((gradient j z : ℂ) • f z)=
      (GaussCoframeKinetic.coefficient i j z : ℂ) • ((volumeGradient z j : ℂ) • ((reciprocalVolume z : ℂ) • f z))
    simp only [gradient,reciprocalVolume,Complex.ofReal_inv,smul_smul,div_eq_mul_inv,Complex.ofReal_mul]
  simp_rw [he]
  rw [←Finset.sum_mul,source_gradient_contraction,smul_mul_assoc]
  push_cast
  rfl

private theorem gradient_left (j : Fin 6) :
    (∑ i : Fin 6,gradientAction i*coefficientAction i j)=
      ((sourceTime 0:ℂ)/4) • (inverseVolumeAction*coordinateAction j) := by
  have he (i : Fin 6) : gradientAction i*coefficientAction i j=coefficientAction j i*gradientAction i := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (gradient i z : ℂ) • ((GaussCoframeKinetic.coefficient i j z : ℂ) • f z)=
      (GaussCoframeKinetic.coefficient j i z : ℂ) • ((gradient i z : ℂ) • f z)
    rw [GaussCoframeKinetic.coefficient_symmetric]
    exact smul_comm _ _ _
  simp_rw [he]
  rw [gradient_contraction]
  congr 1
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (z.1 j : ℂ) (reciprocalVolume z : ℂ) (f z)

private def eulerMomentum : End := ∑ i : Fin 6,coordinateAction i*GaussCoframeCore.momentum i
private def eulerAdjoint : End := ∑ i : Fin 6,GaussCoframeCore.adjoint i*coordinateAction i
private def densityShift : End := GaussCoframeForm.number+(4:ℂ) • (1:End)
private theorem euler_momentum : eulerMomentum=(-Complex.I) • eulerAction := by
  unfold eulerMomentum eulerAction GaussCoframeCore.momentum
  simp only [mul_smul_comm,←Finset.smul_sum]
private theorem euler_pair_sum : eulerAdjoint+eulerMomentum=(3:ℂ) • dilation := by
  unfold eulerAdjoint eulerMomentum dilation
  rw [←Finset.sum_add_distrib,smul_smul]
  norm_num
private theorem dilation_euler : dilation=(2/3:ℂ) • eulerMomentum+(-Complex.I) • densityShift := by
  rw [euler_momentum,dilation_operator]
  unfold densityShift
  simp only [smul_add,smul_smul]
  module
private theorem density_inverse : Commute densityShift inverseVolumeAction := by
  have hn : Commute GaussCoframeForm.number inverseVolumeAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    unfold GaussCoframeForm.number GaussQuantumMultiplier.action inverseVolumeAction
    change GaussQuantumMultiplier.quantized _
      ((reciprocalVolume z:ℂ) • f z)=(reciprocalVolume z:ℂ) •
      GaussQuantumMultiplier.quantized _ (f z)
    exact map_smul _ _ _
  exact hn.add_left ((Commute.one_left inverseVolumeAction).smul_left (4:ℂ))

/-- The original Number-weighted transpose is retained in the symmetric volume current. -/
theorem original_clock_current : clockCurrent=(3*(sourceTime 0:ℂ)/8) •
    (inverseVolumeAction*dilation+dilation*inverseVolumeAction) := by
  rw [clock_current_flux]
  have hf : flux=((sourceTime 0:ℂ)/4) •
      (eulerAdjoint*inverseVolumeAction+inverseVolumeAction*eulerMomentum) := by
    unfold flux eulerAdjoint eulerMomentum
    simp only [Finset.sum_add_distrib]
    have hR : (∑ i : Fin 6,∑ j : Fin 6,GaussCoframeCore.adjoint i*(coefficientAction i j*gradientAction j))=
        ((sourceTime 0:ℂ)/4) • ((∑ i : Fin 6,GaussCoframeCore.adjoint i*coordinateAction i)*inverseVolumeAction) := by
      simp only [←Finset.mul_sum,gradient_contraction,mul_smul_comm,←Finset.smul_sum,Finset.sum_mul,mul_assoc]
    have hL : (∑ i : Fin 6,∑ j : Fin 6,gradientAction i*(coefficientAction i j*GaussCoframeCore.momentum j))=
        ((sourceTime 0:ℂ)/4) • (inverseVolumeAction*(∑ j : Fin 6,coordinateAction j*GaussCoframeCore.momentum j)) := by
      rw [Finset.sum_comm]
      simp only [←mul_assoc,←Finset.sum_mul,gradient_left,smul_mul_assoc]
      simp only [←Finset.smul_sum,Finset.mul_sum,mul_assoc]
    rw [hR,hL,smul_add]
  rw [hf]
  have ha : eulerAdjoint=(3:ℂ) • dilation-eulerMomentum := by
    exact eq_sub_iff_add_eq.mpr euler_pair_sum
  rw [ha,dilation_euler]
  simp only [add_mul,mul_add,sub_mul,smul_mul_assoc,mul_smul_comm]
  rw [density_inverse.eq]
  module

/-- All five original coframe weights, with the original CAR and potential terms. -/
def scaleForce : End := (2:ℂ) • kineticAction-(8/3:ℂ) • gaugeKinetic+
  (2/3:ℂ) • GaussMatterCore.matterAction-(2:ℂ) • localAction-(2/3:ℂ) • spatialAction

private def commutator (H : End) : End →ₗ[ℂ] End where
  toFun A := H*A-A*H
  map_add' A B := by noncomm_ring
  map_smul' c A := by simp only [mul_smul_comm,smul_mul_assoc,smul_sub];rfl
private theorem commutator_mul (H A B : End) :
    commutator H (A*B)=commutator H A*B+A*commutator H B := by
  change H*(A*B)-(A*B)*H=(H*A-A*H)*B+A*(H*B-B*H)
  noncomm_ring
private theorem h_dilation : commutator diagonalAction dilation=(-Complex.I) • scaleForce := by
  have h := SourceDilationRemainder.full_source_scale_current
  have hs : dilation*diagonalAction-diagonalAction*dilation=Complex.I • scaleForce := by
    rw [h]
    unfold scaleForce
    simp only [smul_add,smul_sub,smul_smul]
    module
  change diagonalAction*dilation-dilation*diagonalAction=_
  rw [←neg_sub (dilation*diagonalAction),hs]
  module
private theorem h_inverse : commutator diagonalAction inverseVolumeAction=
    (3*Complex.I*(sourceTime 0:ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction) :=
  SourceScalarInverseRetardedBudget.original_inverse_current

private theorem inverse_dilation : dilation*inverseVolumeAction-inverseVolumeAction*dilation=
    (2*Complex.I) • inverseVolumeAction := by
  have h := congrArg (fun A : End => (-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) •
      (dilation*inverseVolumeAction-inverseVolumeAction*dilation))=
    (-2*Complex.I/3) • ((-3:ℂ) • inverseVolumeAction) at h
  simp only [smul_smul] at h
  have hi : (-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring

private theorem acceleration_symmetric : clockAcceleration=
    (9*(sourceTime 0:ℂ)^2/32) •
      ((inverseVolumeAction*dilation*inverseVolumeAction)*dilation+
        dilation*(inverseVolumeAction*dilation*inverseVolumeAction))-
    (3*(sourceTime 0:ℂ)/8) • (inverseVolumeAction*scaleForce+scaleForce*inverseVolumeAction) := by
  change (-Complex.I) • (commutator diagonalAction clockCurrent)=_
  rw [original_clock_current,map_smul,map_add,commutator_mul,commutator_mul,h_dilation,h_inverse]
  simp only [smul_mul_assoc,mul_smul_comm,smul_add,smul_smul]
  have h1 : (-Complex.I)*((3*(sourceTime 0:ℂ)/8)*(3*Complex.I*(sourceTime 0:ℂ)/4))=
      9*(sourceTime 0:ℂ)^2/32 := by
    calc _= -(9*(sourceTime 0:ℂ)^2/32)*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  have h2 : (-Complex.I)*((3*(sourceTime 0:ℂ)/8)*(-Complex.I))= -(3*(sourceTime 0:ℂ)/8) := by
    calc _=(3*(sourceTime 0:ℂ)/8)*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [h1,h2]
  module

private theorem dilation_symmetric_square :
    (inverseVolumeAction*dilation*inverseVolumeAction)*dilation+
      dilation*(inverseVolumeAction*dilation*inverseVolumeAction)=
      (2:ℂ) • (inverseVolumeAction*dilation*dilation*inverseVolumeAction) := by
  have h := inverse_dilation
  have h1 := congrArg (fun A : End => A*dilation*inverseVolumeAction) h
  have h2 := congrArg (fun A : End => inverseVolumeAction*dilation*A) h
  simp only [smul_mul_assoc,mul_smul_comm] at h1 h2
  linear_combination (norm := (noncomm_ring; module)) h1-h2

/-- The original density correction combines with the complete clock square without a negative volume remainder. -/
theorem original_clock_acceleration : clockAcceleration=
    (9*(sourceTime 0:ℂ)^2/16) • (inverseVolumeAction*dilation*dilation*inverseVolumeAction)-
      (3*(sourceTime 0:ℂ)/8) • (inverseVolumeAction*scaleForce+scaleForce*inverseVolumeAction) := by
  rw [acceleration_symmetric,dilation_symmetric_square]
  simp only [smul_smul]
  module

/-- The clock acceleration meets the actual graded compression through its complete original defect. -/
theorem original_compression_clock_acceleration (F : Index) :
    (-Complex.I) • (compressionCore F*clockCurrent-clockCurrent*compressionCore F)=
      clockAcceleration+Complex.I • (defectAction F*clockCurrent-clockCurrent*defectAction F) := by
  unfold clockAcceleration defectAction
  simp only [sub_mul,mul_sub,smul_sub]
  module

/-- Source energy compensation cancels the entire independent-dual matter action algebraically. -/
def completedAcceleration : End := clockAcceleration+( (sourceTime 0:ℂ)/4) •
  (inverseVolumeAction*diagonalAction+diagonalAction*inverseVolumeAction)

/-- The matter-free completed force retains the reflected kinetic and both original potential grades. -/
theorem original_completed_acceleration : completedAcceleration=
    (9*(sourceTime 0:ℂ)^2/16) • (inverseVolumeAction*dilation*dilation*inverseVolumeAction)-
      ((sourceTime 0:ℂ)/2) • (inverseVolumeAction*kineticAction+kineticAction*inverseVolumeAction)+
      (sourceTime 0:ℂ) • (inverseVolumeAction*gaugeKinetic+gaugeKinetic*inverseVolumeAction)+
      (sourceTime 0:ℂ) • (inverseVolumeAction*localAction+localAction*inverseVolumeAction)+
      ((sourceTime 0:ℂ)/2) • (inverseVolumeAction*spatialAction+spatialAction*inverseVolumeAction) := by
  unfold completedAcceleration
  rw [original_clock_acceleration,original_action_split]
  unfold scaleForce
  simp only [mul_add,add_mul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  module

private theorem vu : inverseVolumeAction*volumeAction=(1:End) := by
  have hc : Commute inverseVolumeAction volumeAction := SourceHamiltonianVolume.real_volume _ _
  exact hc.eq.trans (LinearMap.ext volume_inverse)
private theorem uv : volumeAction*inverseVolumeAction=(1:End) := LinearMap.ext volume_inverse
private theorem inverse_commute (A : End) (hA : Commute A volumeAction) : Commute A inverseVolumeAction := by
  change A*inverseVolumeAction=inverseVolumeAction*A
  calc
    _=(inverseVolumeAction*volumeAction)*A*inverseVolumeAction := by rw [vu];simp
    _=inverseVolumeAction*(A*volumeAction)*inverseVolumeAction := by rw [hA.eq];noncomm_ring
    _=_ := by simp only [mul_assoc,uv,mul_one]
private theorem symmetric_volume_return (A : End) :
    inverseVolumeAction*((1/2:ℂ) • (A*volumeAction+volumeAction*A))*inverseVolumeAction=
      (1/2:ℂ) • (inverseVolumeAction*A+A*inverseVolumeAction) := by
  simp only [mul_smul_comm,smul_mul_assoc]
  congr 1
  calc
    _=inverseVolumeAction*A*(volumeAction*inverseVolumeAction)+
        (inverseVolumeAction*volumeAction)*A*inverseVolumeAction := by noncomm_ring
    _=_ := by rw [uv,vu];simp

/-- This is the full source form on the single generated input V f, with the matter grade cancelled. -/
def clockBulk : End := (9*(sourceTime 0:ℂ)^2/16) • (dilation*dilation)-
    (sourceTime 0:ℂ) • SourceOriginalKineticSquare.symmetricScale+
    (2*(sourceTime 0:ℂ)) • (volumeAction*gaugeKinetic)+
    (2*(sourceTime 0:ℂ)) • (volumeAction*localAction)+
    (sourceTime 0:ℂ) • (volumeAction*spatialAction)

theorem original_completed_volume_source :
    completedAcceleration=inverseVolumeAction*clockBulk*inverseVolumeAction := by
  have hg := (inverse_commute gaugeKinetic SourceHamiltonianVolume.gauge_kinetic_volume).eq
  have hl := (inverse_commute localAction (SourceHamiltonianVolume.real_volume _ _)).eq
  have hs := (inverse_commute spatialAction (SourceHamiltonianVolume.real_volume _ _)).eq
  have hg' : inverseVolumeAction*(volumeAction*gaugeKinetic)*inverseVolumeAction=gaugeKinetic*inverseVolumeAction := by
    simp only [←mul_assoc,vu,one_mul]
  have hl' : inverseVolumeAction*(volumeAction*localAction)*inverseVolumeAction=localAction*inverseVolumeAction := by
    simp only [←mul_assoc,vu,one_mul]
  have hs' : inverseVolumeAction*(volumeAction*spatialAction)*inverseVolumeAction=spatialAction*inverseVolumeAction := by
    simp only [←mul_assoc,vu,one_mul]
  rw [original_completed_acceleration]
  unfold clockBulk
  simp only [mul_add,add_mul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  rw [SourceOriginalKineticSquare.symmetric_scale_source,symmetric_volume_return,hg',hl',hs',hg,hl,hs]
  simp only [mul_assoc,smul_smul]
  module

/-- The completed source current is read on V f; its genuine dilation square is positive and every other source term is retained. -/
theorem original_completed_source_form (f : QuantumTest) :
    (sourcePair f (completedAcceleration f)).re=
      (9*(sourceTime 0)^2/16)*‖embed (dilation (inverseVolumeAction f))‖^2-
      sourceTime 0*(sourcePair (inverseVolumeAction f)
        (SourceOriginalKineticSquare.symmetricScale (inverseVolumeAction f))).re+
      (2*sourceTime 0)*(sourcePair (inverseVolumeAction f)
        (volumeAction (gaugeKinetic (inverseVolumeAction f)))).re+
      (2*sourceTime 0)*(sourcePair (inverseVolumeAction f)
        (volumeAction (localAction (inverseVolumeAction f)))).re+
      sourceTime 0*(sourcePair (inverseVolumeAction f)
        (volumeAction (spatialAction (inverseVolumeAction f)))).re := by
  rw [original_completed_volume_source]
  change (sourcePair f (inverseVolumeAction (clockBulk (inverseVolumeAction f)))).re=_
  have hv (a b : QuantumTest) : sourcePair a (inverseVolumeAction b)=sourcePair (inverseVolumeAction a) b :=
    multiply_pair reciprocalVolume reciprocal_volume_smooth a b
  rw [hv]
  have hd : sourcePair (inverseVolumeAction f) (dilation (dilation (inverseVolumeAction f)))=
      sourcePair (dilation (inverseVolumeAction f)) (dilation (inverseVolumeAction f)) := dilation_pair _ _
  change (sourcePair (inverseVolumeAction f) (clockBulk (inverseVolumeAction f))).re=_
  simp only [clockBulk,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_add,map_sub,map_smul,inner_add_right,inner_sub_right,inner_smul_right]
  change inner ℂ (embed (inverseVolumeAction f)) (embed (dilation (dilation (inverseVolumeAction f))))=
      inner ℂ (embed (dilation (inverseVolumeAction f))) (embed (dilation (inverseVolumeAction f))) at hd
  rw [hd]
  have hc : (9*(sourceTime 0:ℂ)^2/16)=((9*(sourceTime 0)^2/16:ℝ):ℂ) := by push_cast;rfl
  have hc2 : 2*(sourceTime 0:ℂ)=((2*sourceTime 0:ℝ):ℂ) := by push_cast;rfl
  rw [hc,hc2]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hn : (inner ℂ (embed (dilation (inverseVolumeAction f)))
      (embed (dilation (inverseVolumeAction f)))).re=‖embed (dilation (inverseVolumeAction f))‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hn]

end LowEnergy.SourceClockAcceleration
