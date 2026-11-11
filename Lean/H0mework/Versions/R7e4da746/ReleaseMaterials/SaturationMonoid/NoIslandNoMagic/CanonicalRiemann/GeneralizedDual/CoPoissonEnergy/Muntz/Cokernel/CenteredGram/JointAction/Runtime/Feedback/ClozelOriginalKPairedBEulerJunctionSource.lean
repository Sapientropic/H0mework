import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.SourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.TwoPieceFourierAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Spectral.Direct.Fourier.ClozelBurnolPaFourierPairedAction
import H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.Phi
import H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Generated

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open scoped ENNReal Topology BigOperators FourierTransform
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Eq" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction

theorem junctionShift_pos : 0<junctionShift := by
  apply Real.log_pos
  change (1:ℝ)<Real.sqrt 3
  exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

theorem junctionPoint_bounds : 0<junctionPoint ∧ junctionPoint<q := by
  have small:Real.exp (-junctionShift)<1:=Real.exp_lt_one_iff.mpr (by linarith [junctionShift_pos])
  unfold junctionPoint
  constructor
  · positivity
  · nlinarith

theorem junction_scaled : Real.exp junctionShift*junctionPoint=q := by
  have cancel:Real.exp junctionShift*Real.exp (-junctionShift)=1:=by
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  unfold junctionPoint
  calc
    _=q*(Real.exp junctionShift*Real.exp (-junctionShift)) := by ring
    _=q := by rw [cancel,mul_one]

theorem source_B_first (c:BurnolCompletedMellinCoordinate) :
    sourceFirst c+S (sourceSecond c)=sourceDrive c 0 :=
  burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs (sourceAction c))

theorem source_B_second (c:BurnolCompletedMellinCoordinate) :
    S (sourceFirst c)+sourceSecond c=sourceDrive c 1 :=
  burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs (sourceAction c))

theorem source_B_inverse (c:BurnolCompletedMellinCoordinate) :
    sourceFirst c=burnolMeanZeroBlockInverse (sourceDrive c 0-S (sourceDrive c 1)) := rfl

theorem original_face_charge (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    originalOuter c i q-originalGap c i=originalCharge c i := by
  fin_cases i
  · exact Kernel.position_jump c
  · change (burnolRieszSingleFourierSourceRaw c q+fourierMean c)-fourierMean c=Kernel.beta c
    unfold Kernel.beta
    ring

/-- The internal trace is emitted by the actual original K/FK jump, with the paired half retained. -/
theorem source_internal_jump (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    sourceOuterRaw c i junctionPoint-sourceInnerRaw c i junctionPoint=sourceJump c i := by
  unfold sourceOuterRaw sourceInnerRaw sourceJump
  rw [junction_scaled]
  calc
    _=(Real.exp (junctionShift/2):ℂ)/2*(originalOuter c i q-originalGap c i) := by ring
    _=_ := by rw [original_face_charge]

private theorem reflection_sub (left right:M) :
    sourceMeanZeroReflection (left-right)=sourceMeanZeroReflection left-sourceMeanZeroReflection right := by
  apply Subtype.ext
  exact map_sub (reflectRestricted q) (left:Hq) (right:Hq)

private theorem oneMinusSquare_reflect (state:M) :
    burnolMeanZeroOneMinusSquare (sourceMeanZeroReflection state)=
      sourceMeanZeroReflection (burnolMeanZeroOneMinusSquare state) := by
  change sourceMeanZeroReflection state-S (S (sourceMeanZeroReflection state))=_
  rw [sourceMeanZeroFourier_reflect,sourceMeanZeroFourier_reflect]
  exact (reflection_sub state (S (S state))).symm

private theorem source_drive_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    sourceMeanZeroReflection (sourceDrive c i)=sourceDrive c i := by
  apply Subtype.ext
  fin_cases i
  · exact burnolAmbientMeanZeroPosition_reflection_fixed _
  · exact burnolAmbientMeanZeroFourier_reflection_fixed _

private theorem source_first_even (c:BurnolCompletedMellinCoordinate) :
    sourceMeanZeroReflection (sourceFirst c)=sourceFirst c := by
  have source:burnolMeanZeroOneMinusSquare (sourceFirst c)=sourceDrive c 0-S (sourceDrive c 1) := by
    rw [source_B_inverse]
    change (burnolMeanZeroOneMinusSquare*burnolMeanZeroBlockInverse) _=_
    rw [burnolMeanZeroBlockInverse_right]
    rfl
  have reflected:burnolMeanZeroOneMinusSquare (sourceMeanZeroReflection (sourceFirst c))=
      sourceDrive c 0-S (sourceDrive c 1) := by
    rw [oneMinusSquare_reflect,source,reflection_sub,←sourceMeanZeroFourier_reflect,
      source_drive_even,source_drive_even]
  have recovered:=congrArg burnolMeanZeroBlockInverse (reflected.trans source.symm)
  change (burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare) _=
    (burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare) _ at recovered
  have inverse:burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare=1:=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  rw [inverse] at recovered
  exact recovered

theorem source_correction_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    reflectRestricted q (sourceCorrection c i:Hq)=sourceCorrection c i := by
  have first:=source_first_even c
  have second:sourceMeanZeroReflection (sourceSecond c)=sourceSecond c := by
    have equality:sourceSecond c=sourceDrive c 1-S (sourceFirst c):=eq_sub_of_add_eq' (source_B_second c)
    rw [equality,reflection_sub,←sourceMeanZeroFourier_reflect,source_drive_even,first]
  fin_cases i
  · exact congrArg (fun state:M=>(state:Hq)) first
  · exact congrArg (fun state:M=>(state:Hq)) second

def originalFace (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : BurnolL2 :=
  ![(burnolCompletedMellinRieszVector c:BurnolL2),fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)] i

def originalRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℝ→ℂ :=
  ![burnolRieszStateRaw c,burnolRieszFourierRaw c] i

def pairedRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  ((Real.exp (junctionShift/2):ℂ)*originalRaw c i (Real.exp junctionShift*x)+
    (Real.exp (-junctionShift/2):ℂ)*originalRaw c i (Real.exp (-junctionShift)*x))/2

private theorem original_raw_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (originalFace c i:ℝ→ℂ)=ᵐ[volume]originalRaw c i := by
  fin_cases i
  · exact burnolRieszState_ae_raw c
  · exact burnolRieszFourier_ae_raw c

private theorem source_face_actual (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    sourceFace c i=pairedBurnolMultiplicativeDilation junctionShift (originalFace c i) := by
  fin_cases i
  · rfl
  · exact (pairedBurnolMultiplicativeDilation_fourier junctionShift _).symm

private theorem source_face_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (sourceFace c i:ℝ→ℂ)=ᵐ[volume]pairedRaw c i := by
  have dilation (h:ℝ) :
      (burnolMultiplicativeDilation h (originalFace c i):ℝ→ℂ)=ᵐ[volume]
        fun x=>(Real.exp (h/2):ℂ)*originalRaw c i (Real.exp h*x) := by
    have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp h*x) volume volume:=by
      simpa only [smul_eq_mul] using
        (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=Real.exp h) (Real.exp_ne_zero h))
    filter_upwards [burnolMultiplicativeDilation_coeFn h (originalFace c i),
      scale.ae (original_raw_read c i)] with x actual raw
    rw [actual]
    change (Real.exp (h/2):ℂ)*originalFace c i (Real.exp h*x)=_
    rw [raw]
  rw [source_face_actual]
  let first:=burnolMultiplicativeDilation junctionShift (originalFace c i)
  let second:=burnolMultiplicativeDilation (-junctionShift) (originalFace c i)
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (first+second),Lp.coeFn_add first second,
    dilation junctionShift,dilation (-junctionShift)] with x scalar sum firstRead secondRead
  change ((1/2:ℂ) • (first+second):BurnolL2) x=_
  rw [scalar]
  change (1/2:ℂ)*(first+second:BurnolL2) x=_
  rw [sum]
  change (1/2:ℂ)*(first x+second x)=_
  rw [firstRead,secondRead]
  unfold pairedRaw
  rw [neg_div]
  ring

private theorem original_raw_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) :
    originalRaw c i (-x)=originalRaw c i x := by
  fin_cases i
  · exact burnolRieszStateRaw_even c x
  · exact fourier_raw_even c x

private theorem paired_raw_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) :
    pairedRaw c i (-x)=pairedRaw c i x := by
  simp only [pairedRaw,mul_neg,original_raw_even]

private theorem original_raw_inner (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (inside:|x|≤q) : originalRaw c i x=originalGap c i := by
  have belongs:x∈symmetricInterval q:=abs_le.mp inside
  fin_cases i
  · exact burnolRieszStateRaw_eq_quarterInner_of_mem c belongs
  · exact burnolRieszFourierRaw_gap_read c belongs

private theorem original_raw_outer (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (outside:q<x) : originalRaw c i x=originalOuter c i x := by
  fin_cases i
  · exact burnolRieszStateRaw_eq_positiveOuter c outside
  · exact (fourier_raw_eq_exterior c outside).trans (fourier_exterior_source_read c x)

private theorem source_drive_position (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    sourceDrive c i=burnolAmbientMeanZeroPosition (sourceFace c i) := by
  fin_cases i
  · rfl
  · change burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
        (Rq (fourierL2 (burnolAmbientEvenPart (sourceAction c))))=
      burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
        (Rq (burnolAmbientEvenPart (fourierL2 (sourceAction c))))
    rw [fourierL2_burnolAmbientEvenPart]

private theorem source_drive_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (sourceDrive c i:Hq)=ᵐ[volume.restrict (symmetricInterval q)]
      fun x=>pairedRaw c i x-sourceMean c i := by
  rw [source_drive_position]
  filter_upwards [burnolPositionMeanZero_ae_raw (sourceFace c i) (pairedRaw c i)
    (source_face_read c i)] with x actual
  rw [actual]
  unfold burnolPositionMeanZeroRaw burnolEvenRaw burnolMeanZeroRaw sourceMean
  dsimp only
  rw [paired_raw_even]
  ring

private theorem source_correction_relation (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    sourceCorrection c i=sourceDrive c i-S (sourcePartner c i) := by
  fin_cases i
  · exact eq_sub_of_add_eq (source_B_first c)
  · exact eq_sub_of_add_eq' (source_B_second c)

private theorem paired_correction_positive_raw (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (positive:0<x) (small:x≤q) :
    pairedRaw c i x-sourceMean c i-burnolMeanZeroFourierRaw (sourcePartner c i) x=sourceRaw c i x := by
  have inward:|Real.exp (-junctionShift)*x|≤q := by
    rw [abs_of_pos (mul_pos (Real.exp_pos _) positive)]
    have scale:Real.exp (-junctionShift)≤1:=Real.exp_le_one_iff.mpr (by linarith [junctionShift_pos])
    nlinarith [Real.exp_pos (-junctionShift)]
  unfold pairedRaw sourceRaw
  rw [abs_of_pos positive,original_raw_inner c i _ inward]
  by_cases inner:x≤junctionPoint
  · have inside:|Real.exp junctionShift*x|≤q := by
      rw [abs_of_pos (mul_pos (Real.exp_pos _) positive)]
      have inequality:=mul_le_mul_of_nonneg_left inner (Real.exp_pos junctionShift).le
      rw [junction_scaled] at inequality
      exact inequality
    rw [if_pos inner,original_raw_inner c i _ inside,sourceInnerRaw]
    ring
  · have outside:q<Real.exp junctionShift*x := by
      have inequality:=mul_lt_mul_of_pos_left (lt_of_not_ge inner) (Real.exp_pos junctionShift)
      rw [junction_scaled] at inequality
      exact inequality
    rw [if_neg inner,original_raw_outer c i _ outside,sourceOuterRaw]

/-- The piecewise source is the actual original paired B correction, including its two centering means. -/
theorem source_correction_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (sourceCorrection c i:Hq)=ᵐ[volume.restrict (symmetricInterval q)]sourceRaw c i := by
  have source:(sourceCorrection c i:Hq)=ᵐ[volume.restrict (symmetricInterval q)]
      fun x=>pairedRaw c i x-sourceMean c i-burnolMeanZeroFourierRaw (sourcePartner c i) x := by
    rw [source_correction_relation]
    filter_upwards [Lp.coeFn_sub (sourceDrive c i:Hq) (S (sourcePartner c i):Hq),
      source_drive_read c i,burnolMeanZeroFourier_ae_raw (sourcePartner c i)] with x sub drive returned
    change ((sourceDrive c i:Hq)-(S (sourcePartner c i):Hq):Hq) x=_
    rw [sub]
    change (sourceDrive c i:Hq) x-(S (sourcePartner c i):Hq) x=_
    rw [drive,returned]
  let reflection:=negMeasurePreserving_restrict q
  have reflected:=Lp.coeFn_compMeasurePreserving (sourceCorrection c i:Hq) reflection
  change (reflectRestricted q (sourceCorrection c i:Hq):ℝ→ℂ)=ᵐ[_]
    (fun x=>(sourceCorrection c i:Hq) (-x)) at reflected
  rw [source_correction_even] at reflected
  have positive:∀ᵐ x:ℝ ∂volume.restrict (symmetricInterval q),0<x→
      (sourceCorrection c i:Hq) x=sourceRaw c i x := by
    filter_upwards [source,ae_restrict_mem (measurableSet_symmetricInterval q)] with x actual inside pos
    exact actual.trans (paired_correction_positive_raw c i x pos inside.2)
  filter_upwards [positive,reflection.quasiMeasurePreserving.ae positive,reflected,
    ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x first second even nonzero
  by_cases pos:0<x
  · exact first pos
  · have negpos:0< -x:=by
      have negative:x<0:=lt_of_le_of_ne (le_of_not_gt pos) nonzero
      linarith
    rw [even,second negpos]
    simp only [sourceRaw,abs_neg]


def originalOuterSlope (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  ![positionExteriorDerivative c x,sourceRawDerivative c x] i

private theorem original_outer_hasDerivAt (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (outside:q<x) :
    HasDerivAt (originalOuter c i) (originalOuterSlope c i x) x := by
  fin_cases i
  · exact position_exterior_hasDerivAt c outside
  · exact (sourceRaw_hasDerivAt c x (by linarith)).add_const (fourierMean c)

private theorem original_outer_continuousAt (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (positive:0<x) : ContinuousAt (originalOuter c i) x := by
  fin_cases i
  · change ContinuousAt (burnolRieszStatePositiveOuterRaw c) x
    rw [funext (position_exterior_return_read c)]
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const x
      (-star c.value) (Or.inr positive.ne'))).sub
        ((burnolRieszReturnRaw_continuous c).continuousAt.add continuousAt_const)
  · exact ((sourceRaw_hasDerivAt c x positive.ne').continuousAt).add continuousAt_const

private theorem original_outer_slope_continuousAt (c:BurnolCompletedMellinCoordinate)
    (i:Fin 2) (x:ℝ) (positive:0<x) : ContinuousAt (originalOuterSlope c i) x := by
  fin_cases i
  · change ContinuousAt (positionExteriorDerivative c) x
    unfold positionExteriorDerivative
    exact (continuousAt_const.mul (continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const x (-(star c.value+1))
        (Or.inr positive.ne')))).sub
          ((burnolRieszReturnRawDerivative_continuous c).continuousAt)
  · change ContinuousAt (sourceRawDerivative c) x
    unfold sourceRawDerivative
    exact (((continuousAt_const.mul
      (Translator.ForcingWhole.raw_continuousAt c positive.ne')).add
        (continuousAt_const.mul (Edge.raw_continuous q).continuousAt)).div
          Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr positive.ne')).add
            ((Constructor.fourierDerivative_continuous _
              (burnolRieszReturnRaw_continuous c)).continuousAt)


def driveInnerRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℝ→ℂ :=
  fun _=>(((Real.exp (junctionShift/2):ℂ)+(Real.exp (-junctionShift/2):ℂ))/2)*originalGap c i-
    sourceMean c i

def driveOuterRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  ((Real.exp (junctionShift/2):ℂ)*originalOuter c i (Real.exp junctionShift*x)+
    (Real.exp (-junctionShift/2):ℂ)*originalGap c i)/2-sourceMean c i

def driveOuterSlope (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  (Real.exp (junctionShift/2):ℂ)/2*(Real.exp junctionShift:ℂ)*
    originalOuterSlope c i (Real.exp junctionShift*x)

def driveRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  if |x|≤junctionPoint then driveInnerRaw c i |x| else driveOuterRaw c i |x|

private theorem drive_outer_hasDerivAt (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (outside:junctionPoint<x) :
    HasDerivAt (driveOuterRaw c i) (driveOuterSlope c i x) x := by
  have scaled:q<Real.exp junctionShift*x := by
    have inequality:=mul_lt_mul_of_pos_left outside (Real.exp_pos junctionShift)
    rw [junction_scaled] at inequality
    exact inequality
  have original:=(original_outer_hasDerivAt c i _ scaled).scomp x
    ((hasDerivAt_id x).const_mul (Real.exp junctionShift))
  have actual:=(((original.const_mul (Real.exp (junctionShift/2):ℂ)).add_const
    ((Real.exp (-junctionShift/2):ℂ)*originalGap c i)).div_const (2:ℂ)).sub_const
      (sourceMean c i)
  convert! actual using 1
  dsimp [driveOuterRaw,driveOuterSlope]
  ring

private theorem drive_outer_continuousOn (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    ContinuousOn (driveOuterRaw c i) (Icc junctionPoint q) := by
  intro x belongs
  have positive:0<x:=junctionPoint_bounds.1.trans_le belongs.1
  exact ((((original_outer_continuousAt c i _
      (mul_pos (Real.exp_pos _) positive)).comp (by fun_prop)).const_mul _).add
        continuousAt_const |>.div_const (2:ℂ) |>.sub continuousAt_const).continuousWithinAt

private theorem drive_outer_slope_continuousOn (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    ContinuousOn (driveOuterSlope c i) (Icc junctionPoint q) := by
  intro x belongs
  have positive:0<x:=junctionPoint_bounds.1.trans_le belongs.1
  exact ((continuousAt_const.mul continuousAt_const).mul
    ((original_outer_slope_continuousAt c i _
      (mul_pos (Real.exp_pos _) positive)).comp (by fun_prop))).continuousWithinAt

private theorem drive_raw_sub_return (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) : driveRaw c i x-burnolMeanZeroFourierRaw (sourcePartner c i) |x|=sourceRaw c i x := by
  unfold driveRaw sourceRaw
  split <;> rfl

private theorem drive_raw_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (sourceDrive c i:Hq)=ᵐ[volume.restrict (symmetricInterval q)]driveRaw c i := by
  have positive:∀ᵐ x:ℝ ∂volume.restrict (symmetricInterval q),0<x→
      (sourceDrive c i:Hq) x=driveRaw c i x := by
    filter_upwards [source_drive_read c i,ae_restrict_mem (measurableSet_symmetricInterval q)]
      with x actual member pos
    rw [actual]
    have branch:=paired_correction_positive_raw c i x pos member.2
    rw [←drive_raw_sub_return,abs_of_pos pos] at branch
    linear_combination branch
  have reflected:=Lp.coeFn_compMeasurePreserving (sourceDrive c i:Hq) (negMeasurePreserving_restrict q)
  change (reflectRestricted q (sourceDrive c i:Hq):ℝ→ℂ)=ᵐ[_]
    (fun x=>(sourceDrive c i:Hq) (-x)) at reflected
  have fixed:reflectRestricted q (sourceDrive c i:Hq)=sourceDrive c i:=
    congrArg (fun state:M=>(state:Hq)) (source_drive_even c i)
  rw [fixed] at reflected
  filter_upwards [positive,(negMeasurePreserving_restrict q).quasiMeasurePreserving.ae positive,
    reflected,ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x first second reflected nonzero
  by_cases pos:0<x
  · exact first pos
  · have negpos:0< -x:=by
      have negative:x<0:=lt_of_le_of_ne (le_of_not_gt pos) nonzero
      linarith
    rw [reflected,second negpos]
    simp only [driveRaw,abs_neg]


def sourceInnerSlope (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  -Constructor.fourierDerivative (sourcePartner c i:Hq) x

def sourceOuterSlope (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  driveOuterSlope c i x-Constructor.fourierDerivative (sourcePartner c i:Hq) x

private theorem source_inner_hasDerivAt (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) : HasDerivAt (sourceInnerRaw c i) (sourceInnerSlope c i x) x := by
  have actual:=(hasDerivAt_const x
    ((((Real.exp (junctionShift/2):ℂ)+(Real.exp (-junctionShift/2):ℂ))/2)*originalGap c i-
      sourceMean c i)).sub (TwoPieceFourierAction.meanZero_fourier_hasDerivAt (sourcePartner c i) x)
  change HasDerivAt ((fun _:ℝ=>
    (((Real.exp (junctionShift/2):ℂ)+(Real.exp (-junctionShift/2):ℂ))/2)*originalGap c i-
      sourceMean c i)-burnolMeanZeroFourierRaw (sourcePartner c i)) _ x
  simpa only [sourceInnerSlope,zero_sub] using actual

private theorem source_outer_hasDerivAt (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (outside:junctionPoint<x) :
    HasDerivAt (sourceOuterRaw c i) (sourceOuterSlope c i x) x :=
  (drive_outer_hasDerivAt c i x outside).sub
    (TwoPieceFourierAction.meanZero_fourier_hasDerivAt (sourcePartner c i) x)

private theorem source_inner_continuousOn (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    ContinuousOn (sourceInnerRaw c i) (Icc 0 junctionPoint) :=
  (continuous_iff_continuousAt.mpr (fun x=>(source_inner_hasDerivAt c i x).continuousAt)).continuousOn

private theorem source_inner_slope_continuousOn (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    ContinuousOn (sourceInnerSlope c i) (Icc 0 junctionPoint) :=
  (TwoPieceFourierAction.state_fourierSlope_continuous (sourcePartner c i:Hq)).neg.continuousOn

private theorem source_outer_continuousOn (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    ContinuousOn (sourceOuterRaw c i) (Icc junctionPoint q) :=
  (drive_outer_continuousOn c i).sub
    (OriginalCommonInverseForcing.InverseEuler.meanZeroRaw_continuous (sourcePartner c i)).continuousOn

private theorem source_outer_slope_continuousOn (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    ContinuousOn (sourceOuterSlope c i) (Icc junctionPoint q) :=
  (drive_outer_slope_continuousOn c i).sub
    (TwoPieceFourierAction.state_fourierSlope_continuous (sourcePartner c i:Hq)).continuousOn

/-- The regular bulk is generated by the actual two branches, rather than a global smoothness assumption. -/
def sourceBulk (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : Hq :=
  TwoPieceFourierAction.pieceBulk junctionPoint junctionPoint_bounds.1 junctionPoint_bounds.2
    (sourceInnerRaw c i) (sourceInnerSlope c i) (sourceOuterRaw c i) (sourceOuterSlope c i)
    (source_inner_continuousOn c i) (source_inner_slope_continuousOn c i)
    (source_outer_continuousOn c i) (source_outer_slope_continuousOn c i)

def sourceBulkRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℝ→ℂ :=
  TwoPieceFourierAction.bulkRaw junctionPoint
    (sourceInnerRaw c i) (sourceInnerSlope c i) (sourceOuterRaw c i) (sourceOuterSlope c i)

def sourceEulerBulk (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
  Constructor.zeroMean (sourceBulk c i)


theorem source_bulk_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (sourceBulk c i:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]sourceBulkRaw c i :=
  TwoPieceFourierAction.pieceBulk_read junctionPoint junctionPoint_bounds.1 junctionPoint_bounds.2
    (sourceInnerRaw c i) (sourceInnerSlope c i) (sourceOuterRaw c i) (sourceOuterSlope c i)
    (source_inner_continuousOn c i) (source_inner_slope_continuousOn c i)
    (source_outer_continuousOn c i) (source_outer_slope_continuousOn c i)

/-- Both contact carriers are retained; the internal one is at the actual scaled quarter boundary. -/
theorem source_weak_euler (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    GapEuler.euler (Eq (sourceCorrection c i:Hq):TemperedDistribution ℝ ℂ)=
      (Eq (sourceBulk c i):TemperedDistribution ℝ ℂ)+
      ((junctionPoint:ℂ)*sourceJump c i) •
        (TemperedDistribution.delta junctionPoint+TemperedDistribution.delta (-junctionPoint))-
      ((q:ℂ)*sourceTrace c i) • (TemperedDistribution.delta q+TemperedDistribution.delta (-q)) := by
  have actual:=TwoPieceFourierAction.weak_two_piece_euler
    junctionPoint junctionPoint_bounds.1 junctionPoint_bounds.2
    (sourceInnerRaw c i) (sourceInnerSlope c i) (sourceOuterRaw c i) (sourceOuterSlope c i)
    (source_inner_continuousOn c i) (source_inner_slope_continuousOn c i)
    (source_outer_continuousOn c i) (source_outer_slope_continuousOn c i)
    (fun x _=>source_inner_hasDerivAt c i x) (fun x hx=>source_outer_hasDerivAt c i x hx.1)
    (sourceCorrection c i:Hq) (source_correction_read c i)
  rw [source_internal_jump] at actual
  exact actual

theorem source_bulk_mean (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    burnolQuarterMeanCoefficient (sourceBulk c i)=
      sourceTrace c i-((junctionPoint/q:ℝ):ℂ)*sourceJump c i := by
  have actual:=TwoPieceFourierAction.pieceBulk_mean
    junctionPoint junctionPoint_bounds.1 junctionPoint_bounds.2
    (sourceInnerRaw c i) (sourceInnerSlope c i) (sourceOuterRaw c i) (sourceOuterSlope c i)
    (source_inner_continuousOn c i) (source_inner_slope_continuousOn c i)
    (source_outer_continuousOn c i) (source_outer_slope_continuousOn c i)
    (fun x _=>source_inner_hasDerivAt c i x) (fun x hx=>source_outer_hasDerivAt c i x hx.1)
    (sourceCorrection c i:Hq) (source_correction_read c i)
  rw [Constructor.mean_zero,source_internal_jump,mul_zero,sub_zero] at actual
  exact actual

theorem source_fourier_euler (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    Constructor.zeroMean (TwoPieceFourierAction.smoothFourierBulk (sourceCorrection c i))+
      S (sourceEulerBulk c i)=sourceContact c i := by
  have actual:=TwoPieceFourierAction.centered_two_piece_fourier_action
    junctionPoint junctionPoint_bounds.1 junctionPoint_bounds.2
    (sourceInnerRaw c i) (sourceInnerSlope c i) (sourceOuterRaw c i) (sourceOuterSlope c i)
    (source_inner_continuousOn c i) (source_inner_slope_continuousOn c i)
    (source_outer_continuousOn c i) (source_outer_slope_continuousOn c i)
    (fun x _=>source_inner_hasDerivAt c i x) (fun x hx=>source_outer_hasDerivAt c i x hx.1)
    (sourceCorrection c i) (source_correction_read c i)
  rw [source_internal_jump] at actual
  exact actual


def driveBulk (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : Hq :=
  TwoPieceFourierAction.pieceBulk junctionPoint junctionPoint_bounds.1 junctionPoint_bounds.2
    (driveInnerRaw c i) (fun _=>0) (driveOuterRaw c i) (driveOuterSlope c i)
    continuousOn_const continuousOn_const (drive_outer_continuousOn c i)
    (drive_outer_slope_continuousOn c i)

def driveEuler (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
  Constructor.zeroMean (driveBulk c i)

private theorem drive_bulk_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (driveBulk c i:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]
      TwoPieceFourierAction.bulkRaw junctionPoint
        (driveInnerRaw c i) (fun _=>0) (driveOuterRaw c i) (driveOuterSlope c i) :=
  TwoPieceFourierAction.pieceBulk_read junctionPoint junctionPoint_bounds.1 junctionPoint_bounds.2
    (driveInnerRaw c i) (fun _=>0) (driveOuterRaw c i) (driveOuterSlope c i)
    continuousOn_const continuousOn_const (drive_outer_continuousOn c i)
    (drive_outer_slope_continuousOn c i)

private theorem source_partner_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    reflectRestricted q (sourcePartner c i:Hq)=sourcePartner c i := by
  fin_cases i
  · exact source_correction_even c 1
  · exact source_correction_even c 0

private theorem return_raw_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) :
    burnolMeanZeroFourierRaw (sourcePartner c i) (-x)=burnolMeanZeroFourierRaw (sourcePartner c i) x := by
  let state:Hq:=sourcePartner c i
  let value:=fourierL2 (Eq state)
  have even:reflectL2 value=value := by
    change reflectL2 (fourierL2 (burnolRadiusZeroExtension q state))=_
    rw [←fourierL2_reflectL2_commute,burnolRadiusZeroExtension_reflect,source_partner_even]
    rfl
  have read:(value:ℝ→ℂ)=ᵐ[volume]burnolRadiusTruncatedFourierRaw q state:=
    burnolRadiusFourierL2_zeroExtension_ae_eq_raw state
  have reflected:(fun y:ℝ=>burnolRadiusTruncatedFourierRaw q state (-y))=ᵐ[volume]
      burnolRadiusTruncatedFourierRaw q state := by
    filter_upwards [Lp.coeFn_compMeasurePreserving value negMeasurePreserving,
      negMeasurePreserving.quasiMeasurePreserving.ae read,read] with y reflection negative direct
    change reflectL2 value y=value (-y) at reflection
    rw [even] at reflection
    exact negative.symm.trans (reflection.symm.trans direct)
  have regular:=burnolRadiusTruncatedFourierRaw_continuous state
  have pointwise:=congrFun (Measure.eq_of_ae_eq (μ:=(volume:Measure ℝ)) reflected
    (regular.comp continuous_neg) regular) x
  change burnolRadiusTruncatedFourierRaw q state (-x)-_=
    burnolRadiusTruncatedFourierRaw q state x-_
  rw [pointwise]

private theorem return_slope_neg (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) :
    Constructor.fourierDerivative (sourcePartner c i:Hq) (-x)=
      -Constructor.fourierDerivative (sourcePartner c i:Hq) x := by
  have reflected:=(TwoPieceFourierAction.meanZero_fourier_hasDerivAt (sourcePartner c i) (-x)).scomp x
    (hasDerivAt_id x).neg
  have functionRead:(fun y:ℝ=>burnolMeanZeroFourierRaw (sourcePartner c i) (-y))=
      burnolMeanZeroFourierRaw (sourcePartner c i):=funext (return_raw_even c i)
  change HasDerivAt (fun y:ℝ=>burnolMeanZeroFourierRaw (sourcePartner c i) (-y))
    ((-1:ℝ) • Constructor.fourierDerivative (sourcePartner c i:Hq) (-x)) x at reflected
  rw [functionRead] at reflected
  have unique:=reflected.unique (TwoPieceFourierAction.meanZero_fourier_hasDerivAt (sourcePartner c i) x)
  simpa only [neg_one_smul,neg_eq_iff_eq_neg] using unique

private theorem return_bulk_abs (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) :
    ((|x|:ℝ):ℂ)*Constructor.fourierDerivative (sourcePartner c i:Hq) |x|+
      (1/2:ℂ)*burnolMeanZeroFourierRaw (sourcePartner c i) |x|=
    (x:ℂ)*Constructor.fourierDerivative (sourcePartner c i:Hq) x+
      (1/2:ℂ)*burnolMeanZeroFourierRaw (sourcePartner c i) x := by
  by_cases nonnegative:0≤x
  · rw [abs_of_nonneg nonnegative]
  · rw [abs_of_neg (lt_of_not_ge nonnegative),return_slope_neg,return_raw_even]
    push_cast
    ring

/-- The regular derivative uses the same two actual B branches and the actual S-partner. -/
theorem source_bulk_drive (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    sourceBulk c i=driveBulk c i-TwoPieceFourierAction.smoothFourierBulk (sourcePartner c i) := by
  apply Lp.ext
  filter_upwards [source_bulk_read c i,drive_bulk_read c i,
    TwoPieceFourierAction.smoothFourierBulk_read (sourcePartner c i),
    Lp.coeFn_sub (driveBulk c i) (TwoPieceFourierAction.smoothFourierBulk (sourcePartner c i))]
    with x source drive returned difference
  rw [source,difference]
  change sourceBulkRaw c i x=(driveBulk c i) x-
    (TwoPieceFourierAction.smoothFourierBulk (sourcePartner c i)) x
  rw [drive,returned,←return_bulk_abs c i x]
  unfold sourceBulkRaw TwoPieceFourierAction.bulkRaw TwoPieceFourierAction.pieceRaw
  split <;> dsimp [sourceInnerRaw,sourceInnerSlope,sourceOuterRaw,sourceOuterSlope,
    driveInnerRaw,driveOuterRaw] <;> ring

theorem source_B_euler_first (c:BurnolCompletedMellinCoordinate) :
    sourceEulerBulk c 0-S (sourceEulerBulk c 1)=driveEuler c 0-sourceContact c 1 := by
  have linear:=congrArg Constructor.zeroMean (source_bulk_drive c 0)
  rw [map_sub] at linear
  have fourier:=source_fourier_euler c 1
  have returned:=eq_sub_of_add_eq fourier
  change sourceEulerBulk c 0=driveEuler c 0-
    Constructor.zeroMean (TwoPieceFourierAction.smoothFourierBulk (sourceCorrection c 1)) at linear
  rw [returned] at linear
  rw [linear]
  module

theorem source_B_euler_second (c:BurnolCompletedMellinCoordinate) :
    sourceEulerBulk c 1-S (sourceEulerBulk c 0)=driveEuler c 1-sourceContact c 0 := by
  have linear:=congrArg Constructor.zeroMean (source_bulk_drive c 1)
  rw [map_sub] at linear
  have fourier:=source_fourier_euler c 0
  have returned:=eq_sub_of_add_eq fourier
  change sourceEulerBulk c 1=driveEuler c 1-
    Constructor.zeroMean (TwoPieceFourierAction.smoothFourierBulk (sourceCorrection c 0)) at linear
  rw [returned] at linear
  rw [linear]
  module

def sourceEulerDrive (c:BurnolCompletedMellinCoordinate) : M :=
  driveEuler c 0+S (driveEuler c 1)-sourceContact c 1-S (sourceContact c 0)

/-- The original B inverse now consumes the generated bulk forcing and both actual junction contacts. -/
theorem source_B_euler_action (c:BurnolCompletedMellinCoordinate) :
    sourceEulerBulk c 0=burnolMeanZeroBlockInverse (sourceEulerDrive c) := by
  have second:=congrArg S (source_B_euler_second c)
  rw [map_sub,map_sub] at second
  have generated:burnolMeanZeroOneMinusSquare (sourceEulerBulk c 0)=sourceEulerDrive c := by
    change sourceEulerBulk c 0-S (S (sourceEulerBulk c 0))=_
    unfold sourceEulerDrive
    linear_combination (norm:=module) source_B_euler_first c+second
  have recovered:=congrArg burnolMeanZeroBlockInverse generated
  change (burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare) _=_ at recovered
  have inverse:burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare=1:=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  rw [inverse] at recovered
  exact recovered


def originalSource (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
  ![burnolRieszSingleFourierSource c,S (burnolRieszSingleFourierSource c)] i

def originalSourceRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℝ→ℂ :=
  ![burnolRieszSingleFourierSourceRaw c,burnolRieszReturnRaw c] i

def originalSourceBulk (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : Hq :=
  ![weightedState c,Constructor.returnEulerAmbient c] i

def originalSourceBulkRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℝ→ℂ :=
  ![weightedRaw c,Constructor.returnEulerRaw c] i

private theorem original_source_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (originalSource c i:Hq)=ᵐ[volume.restrict (symmetricInterval q)]originalSourceRaw c i := by
  fin_cases i
  · exact burnolRieszSingleFourierSource_ae_raw c
  · exact Constructor.returnState_read c

private theorem original_source_bulk_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (originalSourceBulk c i:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]originalSourceBulkRaw c i := by
  fin_cases i
  · exact weightedState_read c
  · exact Constructor.compact_read _ (Constructor.returnEulerRaw_continuous c)

private theorem original_source_hasDerivAt (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (nonzero:x≠0) : HasDerivAt (originalSourceRaw c i)
      ((originalSourceBulkRaw c i x-(1/2:ℂ)*originalSourceRaw c i x)/(x:ℂ)) x := by
  fin_cases i
  · exact source_hasDerivAt c x nonzero
  · have original:=burnolRieszReturnRaw_hasDerivAt c x
    convert! original using 1
    change (Constructor.returnEulerRaw c x-(1/2:ℂ)*burnolRieszReturnRaw c x)/(x:ℂ)=_
    unfold Constructor.returnEulerRaw
    field_simp [Complex.ofReal_ne_zero.mpr nonzero]
    ring

private theorem original_source_raw_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) : originalSourceRaw c i (-x)=originalSourceRaw c i x := by
  fin_cases i
  · exact source_raw_even c x
  · exact OriginalRieszFinitePairing.return_raw_even c x

private theorem original_source_bulk_raw_even (c:BurnolCompletedMellinCoordinate)
    (i:Fin 2) (x:ℝ) : originalSourceBulkRaw c i (-x)=originalSourceBulkRaw c i x := by
  by_cases nonzero:x=0
  · simp only [nonzero,neg_zero]
  · have reflected:=(original_source_hasDerivAt c i (-x) (neg_ne_zero.mpr nonzero)).scomp x
      (hasDerivAt_id x).neg
    have functionRead:originalSourceRaw c i ∘ Neg.neg=originalSourceRaw c i:=
      funext (original_source_raw_even c i)
    rw [functionRead] at reflected
    have unique:=reflected.unique (original_source_hasDerivAt c i x nonzero)
    simp only [neg_smul,one_smul,original_source_raw_even] at unique
    push_cast at unique
    field_simp [Complex.ofReal_ne_zero.mpr nonzero] at unique
    linear_combination unique / 2

private theorem original_source_half_origin (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    Tendsto (fun x:ℝ=>(Real.sqrt |x|:ℂ)*originalSourceRaw c i x) (𝓝 0) (𝓝 0) := by
  fin_cases i
  · exact source_halfWeight_origin c
  · change Tendsto (fun x:ℝ=>(Real.sqrt |x|:ℂ)*burnolRieszReturnRaw c x) (𝓝 0) (𝓝 0)
    have original:=halfWeight_origin.mul ((burnolRieszReturnRaw_continuous c).tendsto (0:ℝ))
    simpa only [zero_mul] using original

private theorem native_pair_integrable (left right:Hq) (f g:ℝ→ℂ)
    (leftRead:(left:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]f)
    (rightRead:(right:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]g) :
    Integrable (fun x:ℝ=>star (f x)*g x) (volume.restrict (symmetricInterval q)) := by
  apply (L2.integrable_inner (𝕜:=ℂ) left right).congr
  filter_upwards [leftRead,rightRead] with x first second
  rw [first,second]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

def mixedDensity (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) (x:ℝ) : ℂ :=
  star (originalSourceBulkRaw c i x)*sourceRaw c j x+
    star (originalSourceRaw c i x)*sourceBulkRaw c j x

private theorem mixed_density_integrable (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
    IntervalIntegrable (mixedDensity c i j) volume (-q) q := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr
  exact (native_pair_integrable (originalSourceBulk c i) (sourceCorrection c j:Hq)
    _ _ (original_source_bulk_read c i) (source_correction_read c j)).add
    (native_pair_integrable (originalSource c i:Hq) (sourceBulk c j) _ _
      (original_source_read c i) (source_bulk_read c j))

private theorem mixed_density_even (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) (x:ℝ) :
    mixedDensity c i j (-x)=mixedDensity c i j x := by
  simp only [mixedDensity,original_source_raw_even,original_source_bulk_raw_even,
    sourceRaw,sourceBulkRaw,TwoPieceFourierAction.bulkRaw,TwoPieceFourierAction.pieceRaw,abs_neg]

private theorem mixed_half_weight_flux (g : ℝ → ℂ)
    (origin : Tendsto (fun x : ℝ => (Real.sqrt |x| : ℂ) * g x) (𝓝 0) (𝓝 0)) :
    Tendsto (fun x : ℝ => (x : ℂ) * star (g x)) (𝓝 0) (𝓝 0) := by
  have root := (Real.continuous_sqrt.comp continuous_abs).tendsto (0 : ℝ)
  have generated := root.mul origin.norm
  simp only [Function.comp_apply, abs_zero, Real.sqrt_zero, norm_zero, zero_mul] at generated
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply generated.congr'
  filter_upwards with x
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (abs_nonneg x)]

private def mixedPieceDensity (g weighted f df : ℝ → ℂ) (x : ℝ) : ℂ :=
  star (weighted x) * f x + star (g x) * ((x : ℂ) * df x + (1/2 : ℂ) * f x)

private theorem mixed_product_derivative (g weighted f df : ℝ → ℂ) (x : ℝ) (positive : 0 < x)
    (hg : HasDerivAt g ((weighted x - (1/2 : ℂ) * g x) / (x : ℂ)) x)
    (hf : HasDerivAt f (df x) x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * star (g y) * f y)
      (mixedPieceDensity g weighted f df x) x := by
  have castDerivative : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := x))
  have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  convert (castDerivative.mul hg.star).mul hf using 1
  all_goals first | rfl | (dsimp only [mixedPieceDensity, Pi.mul_apply, Pi.add_apply]; simp; field_simp; ring)

private theorem positive_two_piece (p radius : ℝ) (positive : 0 < p) (inside : p < radius)
    (g weighted f0 df0 f1 df1 : ℝ → ℂ)
    (hg : ∀ x : ℝ, 0 < x → HasDerivAt g ((weighted x - (1/2 : ℂ) * g x) / (x : ℂ)) x)
    (origin : Tendsto (fun x : ℝ => (Real.sqrt |x| : ℂ) * g x) (𝓝 0) (𝓝 0))
    (cf0 : ContinuousOn f0 (Icc 0 p)) (cf1 : ContinuousOn f1 (Icc p radius))
    (hf0 : ∀ x ∈ Ioo 0 p, HasDerivAt f0 (df0 x) x)
    (hf1 : ∀ x ∈ Ioo p radius, HasDerivAt f1 (df1 x) x)
    (int0 : IntervalIntegrable (mixedPieceDensity g weighted f0 df0) volume 0 p)
    (int1 : IntervalIntegrable (mixedPieceDensity g weighted f1 df1) volume p radius) :
    (∫ x : ℝ in 0..p, mixedPieceDensity g weighted f0 df0 x) +
      (∫ x : ℝ in p..radius, mixedPieceDensity g weighted f1 df1 x) =
        (radius : ℂ) * star (g radius) * f1 radius - (p : ℂ) * star (g p) * (f1 p - f0 p) := by
  have f0Right := cf0.continuousWithinAt (show (0 : ℝ) ∈ Icc 0 p from ⟨le_rfl, positive.le⟩)
  change Tendsto f0 (𝓝[Icc 0 p] (0 : ℝ)) (𝓝 (f0 0)) at f0Right
  rw [nhdsWithin_Icc_eq_nhdsGE positive] at f0Right
  have f0Positive : Tendsto f0 (𝓝[>] (0 : ℝ)) (𝓝 (f0 0)) :=
    f0Right.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have lower := ((mixed_half_weight_flux g origin).mono_left nhdsWithin_le_nhds).mul f0Positive
  simp only [zero_mul] at lower
  have f0Left := cf0.continuousWithinAt (show p ∈ Icc 0 p from ⟨positive.le, le_rfl⟩)
  change Tendsto f0 (𝓝[Icc 0 p] p) (𝓝 (f0 p)) at f0Left
  rw [nhdsWithin_Icc_eq_nhdsLE positive] at f0Left
  have f0Before : Tendsto f0 (𝓝[<] p) (𝓝 (f0 p)) :=
    f0Left.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have fluxAtP : ContinuousAt (fun x : ℝ => (x : ℂ) * star (g x)) p :=
    Complex.continuous_ofReal.continuousAt.mul (hg p positive).continuousAt.star
  have upper := (fluxAtP.tendsto.mono_left nhdsWithin_le_nhds).mul f0Before
  have first := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto positive
    (fun x member => mixed_product_derivative g weighted f0 df0 x member.1 (hg x member.1) (hf0 x member))
    int0 lower upper
  have continuousSecond : ContinuousOn (fun x : ℝ => (x : ℂ) * star (g x) * f1 x) (Icc p radius) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact Complex.continuous_ofReal.continuousOn
      · intro x member
        exact (hg x (positive.trans_le member.1)).continuousAt.star.continuousWithinAt
    · exact cf1
  have second := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.le continuousSecond
    (fun x member => mixed_product_derivative g weighted f1 df1 x (positive.trans member.1)
      (hg x (positive.trans member.1)) (hf1 x member)) int1
  simp only [sub_zero] at first
  linear_combination first + second

private theorem mixed_density_inner (c:BurnolCompletedMellinCoordinate) (i j:Fin 2)
    (x:ℝ) (positive:0<x) (small:x<junctionPoint) :
    mixedDensity c i j x=mixedPieceDensity (originalSourceRaw c i) (originalSourceBulkRaw c i)
      (sourceInnerRaw c j) (sourceInnerSlope c j) x := by
  simp only [mixedDensity,sourceRaw,sourceBulkRaw,TwoPieceFourierAction.bulkRaw,
    TwoPieceFourierAction.pieceRaw,abs_of_pos positive,if_pos small.le,mixedPieceDensity]

private theorem mixed_density_outer (c:BurnolCompletedMellinCoordinate) (i j:Fin 2)
    (x:ℝ) (outside:junctionPoint<x) :
    mixedDensity c i j x=mixedPieceDensity (originalSourceRaw c i) (originalSourceBulkRaw c i)
      (sourceOuterRaw c j) (sourceOuterSlope c j) x := by
  have positive:0<x:=junctionPoint_bounds.1.trans outside
  simp only [mixedDensity,sourceRaw,sourceBulkRaw,TwoPieceFourierAction.bulkRaw,
    TwoPieceFourierAction.pieceRaw,abs_of_pos positive,if_neg outside.not_ge,mixedPieceDensity]

private theorem mixed_positive_green (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
    (∫x:ℝ in 0..q,mixedDensity c i j x)=
      (q:ℂ)*star (originalSourceRaw c i q)*sourceTrace c j-
        (junctionPoint:ℂ)*star (originalSourceRaw c i junctionPoint)*sourceJump c j := by
  have full:=mixed_density_integrable c i j
  have first:IntervalIntegrable (mixedDensity c i j) volume 0 junctionPoint:=
    full.mono_set (by
      rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num:-q≤q)]
      intro x hx
      exact ⟨by linarith [hx.1],hx.2.trans junctionPoint_bounds.2.le⟩)
  have second:IntervalIntegrable (mixedDensity c i j) volume junctionPoint q:=
    full.mono_set (by
      rw [uIcc_of_le junctionPoint_bounds.2.le,uIcc_of_le (by norm_num:-q≤q)]
      intro x hx
      exact ⟨by linarith [hx.1,junctionPoint_bounds.1],hx.2⟩)
  have firstEq:EqOn (mixedDensity c i j)
      (mixedPieceDensity (originalSourceRaw c i) (originalSourceBulkRaw c i)
        (sourceInnerRaw c j) (sourceInnerSlope c j)) (uIoo 0 junctionPoint) := by
    rw [uIoo_of_le junctionPoint_bounds.1.le]
    intro x hx
    exact mixed_density_inner c i j x hx.1 hx.2
  have secondEq:EqOn (mixedDensity c i j)
      (mixedPieceDensity (originalSourceRaw c i) (originalSourceBulkRaw c i)
        (sourceOuterRaw c j) (sourceOuterSlope c j)) (uIoo junctionPoint q) := by
    rw [uIoo_of_le junctionPoint_bounds.2.le]
    intro x hx
    exact mixed_density_outer c i j x hx.1
  have generated:=positive_two_piece junctionPoint q junctionPoint_bounds.1 junctionPoint_bounds.2
    (originalSourceRaw c i) (originalSourceBulkRaw c i)
    (sourceInnerRaw c j) (sourceInnerSlope c j) (sourceOuterRaw c j) (sourceOuterSlope c j)
    (fun x hx=>original_source_hasDerivAt c i x hx.ne') (original_source_half_origin c i)
    (source_inner_continuousOn c j) (source_outer_continuousOn c j)
    (fun x _=>source_inner_hasDerivAt c j x) (fun x hx=>source_outer_hasDerivAt c j x hx.1)
    (first.congr_uIoo firstEq) (second.congr_uIoo secondEq)
  rw [source_internal_jump] at generated
  rw [←intervalIntegral.integral_add_adjacent_intervals first second,
    intervalIntegral.integral_congr_uIoo firstEq,intervalIntegral.integral_congr_uIoo secondEq]
  exact generated

private theorem mixed_full_green (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
    (∫x:ℝ in (-q)..q,mixedDensity c i j x)=
      (2*q:ℂ)*star (originalSourceRaw c i q)*sourceTrace c j-
        (2*(junctionPoint:ℂ))*star (originalSourceRaw c i junctionPoint)*sourceJump c j := by
  have full:=mixed_density_integrable c i j
  have negative:=full.mono_set (show uIcc (-q) 0⊆uIcc (-q) q by
    rw [uIcc_of_le (by norm_num:-q≤(0:ℝ)),uIcc_of_le (by norm_num:-q≤q)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have positive:=full.mono_set (show uIcc 0 q⊆uIcc (-q) q by
    rw [uIcc_of_le (by norm_num:(0:ℝ)≤q),uIcc_of_le (by norm_num:-q≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have reflection:=intervalIntegral.integral_comp_neg (f:=mixedDensity c i j) (a:=0) (b:=q)
  simp only [mixed_density_even,neg_zero] at reflection
  rw [←intervalIntegral.integral_add_adjacent_intervals negative positive,←reflection]
  linear_combination 2*mixed_positive_green c i j

private theorem native_pair_read (left right:Hq) (f g:ℝ→ℂ)
    (leftRead:(left:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]f)
    (rightRead:(right:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]g) :
    inner ℂ left right=∫x:ℝ in (-q)..q,star (f x)*g x := by
  rw [L2.inner_def,intervalIntegral.integral_of_le (by norm_num:-q≤q),←integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [leftRead,rightRead] with x first second
  rw [first,second]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

/-- The actual original source and return consume both paired-B junction charges. -/
theorem source_mixed_green (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
    inner ℂ (Constructor.zeroMean (originalSourceBulk c i)) (sourceCorrection c j)+
      inner ℂ (originalSource c i) (sourceEulerBulk c j)=
      (2*q:ℂ)*star (originalSourceRaw c i q)*sourceTrace c j-
        (2*(junctionPoint:ℂ))*star (originalSourceRaw c i junctionPoint)*sourceJump c j := by
  have pair0:=native_pair_integrable (originalSourceBulk c i) (sourceCorrection c j:Hq)
    _ _ (original_source_bulk_read c i) (source_correction_read c j)
  have pair1:=native_pair_integrable (originalSource c i:Hq) (sourceBulk c j)
    _ _ (original_source_read c i) (source_bulk_read c j)
  have int0:IntervalIntegrable
      (fun x:ℝ=>star (originalSourceBulkRaw c i x)*sourceRaw c j x) volume (-q) q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr pair0
  have int1:IntervalIntegrable
      (fun x:ℝ=>star (originalSourceRaw c i x)*sourceBulkRaw c j x) volume (-q) q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr pair1
  change inner ℂ (Constructor.zeroMean (originalSourceBulk c i)) (sourceCorrection c j)+
    inner ℂ (originalSource c i) (Constructor.zeroMean (sourceBulk c j))=_
  unfold Constructor.zeroMean
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [native_pair_read _ _ _ _ (original_source_bulk_read c i) (source_correction_read c j),
    native_pair_read _ _ _ _ (original_source_read c i) (source_bulk_read c j),
    ←intervalIntegral.integral_add int0 int1]
  exact mixed_full_green c i j


private def other (i:Fin 2) : Fin 2 := ![1,0] i
private theorem other_other (i:Fin 2) : other (other i)=i := by fin_cases i <;> rfl

private theorem source_B_pair (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    sourceCorrection c i+S (sourceCorrection c (other i))=sourceDrive c i := by
  fin_cases i
  · exact source_B_first c
  · exact (add_comm _ _).trans (source_B_second c)

private theorem source_euler_pair (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    sourceEulerBulk c i-S (sourceEulerBulk c (other i))=driveEuler c i-sourceContact c (other i) := by
  fin_cases i
  · exact source_B_euler_first c
  · exact source_B_euler_second c

private theorem source_bulk_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    reflectRestricted q (sourceBulk c i)=sourceBulk c i := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (sourceBulk c i) (negMeasurePreserving_restrict q),
    (negMeasurePreserving_restrict q).quasiMeasurePreserving.ae (source_bulk_read c i),
    source_bulk_read c i] with x reflection negative direct
  change reflectRestricted q (sourceBulk c i) x=(sourceBulk c i) (-x) at reflection
  rw [reflection,negative,direct]
  simp only [sourceBulkRaw,TwoPieceFourierAction.bulkRaw,TwoPieceFourierAction.pieceRaw,abs_neg]

private theorem source_euler_bulk_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    reflectRestricted q (sourceEulerBulk c i:Hq)=sourceEulerBulk c i := by
  change reflectRestricted q (burnolQuarterMeanZeroProjection (sourceBulk c i))=_
  rw [←burnolQuarterMeanZeroProjection_reflect,source_bulk_even]
  rfl

private theorem actual_pair_drive (c:BurnolCompletedMellinCoordinate) (left:M) (i:Fin 2) :
    inner ℂ left (sourceCorrection c i)+inner ℂ (S left) (sourceCorrection c (other i))=
      inner ℂ left (sourceDrive c i) := by
  rw [meanZero_fourier_pairing_of_reflection left _ (source_correction_even c (other i)),
    ←inner_add_right,source_B_pair]

private theorem actual_bulk_drive (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    inner ℂ (burnolRieszSingleFourierSource c) (sourceEulerBulk c i)-
      inner ℂ (S (burnolRieszSingleFourierSource c)) (sourceEulerBulk c (other i))=
      inner ℂ (burnolRieszSingleFourierSource c) (driveEuler c i-sourceContact c (other i)) := by
  rw [meanZero_fourier_pairing_of_reflection _ _ (source_euler_bulk_even c (other i)),
    ←inner_sub_right,source_euler_pair]

def pairedJunctionFlux (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℂ :=
  (2*q:ℂ)*(star (Kernel.beta c)*sourceTrace c i-
    star (burnolRieszReturnRaw c q)*sourceTrace c (other i))-
  (2*(junctionPoint:ℂ))*(star (burnolRieszSingleFourierSourceRaw c junctionPoint)*sourceJump c i-
    star (burnolRieszReturnRaw c junctionPoint)*sourceJump c (other i))

/-- The original two source equations and the actual paired correction produce the full junction Ward law. -/
theorem actual_paired_B_euler_action (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    star (star c.value-1/2)*inner ℂ (burnolRieszSingleFourierSource c) (sourceDrive c i)+
      star (Kernel.A c)*inner ℂ Response.u (sourceDrive c i)-
      star (Kernel.beta c)*inner ℂ Response.u (sourceDrive c (other i))+
      inner ℂ (burnolRieszSingleFourierSource c) (driveEuler c i-sourceContact c (other i))=
      pairedJunctionFlux c i := by
  have first:=source_mixed_green c 0 i
  change inner ℂ (Constructor.zeroMean (weightedState c)) (sourceCorrection c i)+
    inner ℂ (burnolRieszSingleFourierSource c) (sourceEulerBulk c i)=_ at first
  rw [weightedState_centered] at first
  have second:=source_mixed_green c 1 (other i)
  change inner ℂ (Constructor.returnEuler c) (sourceCorrection c (other i))+
    inner ℂ (S (burnolRieszSingleFourierSource c)) (sourceEulerBulk c (other i))=_ at second
  rw [Euler.sourceEuler_eq] at first
  rw [Euler.returnEuler_eq] at second
  simp only [inner_add_left,inner_sub_left,inner_smul_left,star_neg,
    starRingEnd_apply] at first second
  have original:=actual_pair_drive c (burnolRieszSingleFourierSource c) i
  have response:=actual_pair_drive c Response.u i
  change inner ℂ Response.u (sourceCorrection c i)+inner ℂ Response.v (sourceCorrection c (other i))=
    inner ℂ Response.u (sourceDrive c i) at response
  have swapped:=actual_pair_drive c Response.u (other i)
  rw [other_other] at swapped
  change inner ℂ Response.u (sourceCorrection c (other i))+inner ℂ Response.v (sourceCorrection c i)=
    inner ℂ Response.u (sourceDrive c (other i)) at swapped
  have bulk:=actual_bulk_drive c i
  unfold pairedJunctionFlux
  change _=(2*q:ℂ)*(star (Kernel.beta c)*sourceTrace c i-
    star (burnolRieszReturnRaw c q)*sourceTrace c (other i))-
    (2*(junctionPoint:ℂ))*(star (burnolRieszSingleFourierSourceRaw c junctionPoint)*sourceJump c i-
      star (burnolRieszReturnRaw c junctionPoint)*sourceJump c (other i))
  change _=(2*q:ℂ)*star (Kernel.beta c)*sourceTrace c i-
    (2*(junctionPoint:ℂ))*star (burnolRieszSingleFourierSourceRaw c junctionPoint)*sourceJump c i at first
  change _=(2*q:ℂ)*star (burnolRieszReturnRaw c q)*sourceTrace c (other i)-
    (2*(junctionPoint:ℂ))*star (burnolRieszReturnRaw c junctionPoint)*sourceJump c (other i) at second
  linear_combination first-second-star (star c.value-1/2)*original-
    star (Kernel.A c)*response+star (Kernel.beta c)*swapped-bulk

end OriginalKPairedBEulerJunctionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
