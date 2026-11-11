import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.WeakWard.Source
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedWeakWardSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open scoped InnerProductSpace Topology BigOperators
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "J" => burnolMeanZeroBlockInverse
local notation "μq" => volume.restrict (symmetricInterval q)
local instance : CompleteSpace M :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

open private outer_coupling gap_coupling from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.PsiDrive

theorem literal_zero_field (c:BurnolCompletedMellinCoordinate) :
 nativeField c false 0=(burnolCompletedMellinRieszVector c:BurnolL2) ∧ nativeField c true 0=0 := by
 constructor
 · unfold nativeField pairedBurnolMultiplicativeDilation
   simp only [Bool.false_eq_true,if_false,neg_zero,smul_apply,
    add_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,burnolMultiplicativeDilation_zero]
   module
 · simp only [nativeField,if_true,neg_zero,burnolMultiplicativeDilation_zero,
    sub_self,smul_zero]

private theorem original_gap_drives_zero (c:BurnolCompletedMellinCoordinate) :
 burnolAmbientMeanZeroPosition (burnolCompletedMellinRieszVector c:BurnolL2)=0 ∧
 burnolAmbientMeanZeroFourier (burnolCompletedMellinRieszVector c:BurnolL2)=0 := by
 have even:=mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
 have evenPart:burnolAmbientEvenPart (burnolCompletedMellinRieszVector c:BurnolL2)=
   (burnolCompletedMellinRieszVector c:BurnolL2) := by
  unfold burnolAmbientEvenPart
  rw [even]
  module
 constructor
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
    (burnolAmbientEvenPart (burnolCompletedMellinRieszVector c:BurnolL2)))=0
   rw [evenPart]
   apply (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
   exact (burnolCompletedMellinRieszVector c).property.1.1
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
    (fourierL2 (burnolAmbientEvenPart (burnolCompletedMellinRieszVector c:BurnolL2))))=0
   rw [evenPart]
   apply (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
   exact (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector c)).property.1.1

theorem native_zero_columns (c:BurnolCompletedMellinCoordinate) (odd:Bool) :
 first c odd 0=0 ∧ second c odd 0=0 := by
 have drivers:drive c odd 0 0=0 ∧ drive c odd 0 1=0 := by
  cases odd
  · simpa only [drive,(literal_zero_field c).1,Matrix.cons_val_zero,Matrix.cons_val_one] using original_gap_drives_zero c
  · simp only [drive,(literal_zero_field c).2,Matrix.cons_val_zero,Matrix.cons_val_one]
    constructor <;> simp only [burnolAmbientMeanZeroPosition,burnolAmbientMeanZeroFourier,
     burnolAmbientEvenPart,map_zero,zero_add,smul_zero]
 have firstZero:first c odd 0=0 := by
  change J (drive c odd 0 0-S (drive c odd 0 1))=0
  rw [drivers.1,drivers.2,map_zero,sub_zero,map_zero]
 have secondZero:second c odd 0=0 := by
  have equation:=fixed_B_second c odd 0
  rw [firstZero,map_zero,zero_add,drivers.2] at equation
  exact equation
 exact ⟨firstZero,secondZero⟩

theorem native_zero_charge (c:BurnolCompletedMellinCoordinate) (odd:Bool) :nativeCharge c odd 0=0 := by
 rw [nativeCharge,(native_zero_columns c odd).2,inner_zero_right,mul_zero]
theorem native_zero_B0_retained (c:BurnolCompletedMellinCoordinate) (odd:Bool) :
 nativeB0 c odd 0=sourceMean c odd 0 0 := by
 simp only [nativeB0,returnedMean,solution,Matrix.cons_val_one,Matrix.cons_val_zero,
  (native_zero_columns c odd).2,ZeroMemClass.coe_zero,map_zero,burnolQuarterMeanCoefficient,inner_zero_right,zero_div,sub_zero]

/-- A concrete local action, not an assumption on the source constructor. -/
def WeakSystem (c:BurnolCompletedMellinCoordinate) : Prop :=
 ∀h∈Ioo 0 junctionShift,∀odd:Bool,
 HasDerivAt (nativeCharge c odd)
  (-lambda c*nativeCharge c (!odd) h+forcing c odd h) h

private theorem test_raw_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
 (test c i:Hq)=ᵐ[μq]testRaw c i := by
 fin_cases i
 · change (-(S (powerResponse c):Hq))=ᵐ[μq]fun x=> -burnolMeanZeroFourierRaw (powerResponse c) x
   filter_upwards [burnolMeanZeroFourier_ae_raw (powerResponse c),
     Lp.coeFn_neg (S (powerResponse c):Hq)] with x read negRead
   rw [negRead]
   change -(S (powerResponse c):Hq) x= -_
   rw [read]
 · change (powerResponse c:Hq)=ᵐ[μq]fun x=>
    centeredPowerRaw c x+burnolMeanZeroFourierRaw (S (powerResponse c)) x
   have equation:powerResponse c-S (S (powerResponse c))=power c := by
    change (burnolMeanZeroOneMinusSquare*J) (power c)=_
    rw [burnolMeanZeroBlockInverse_right,one_apply_eq_self]
   have state:(powerResponse c:Hq)=(power c:Hq)+(S (S (powerResponse c)):Hq) :=
    congrArg Subtype.val (eq_add_of_sub_eq equation)
   have powerRead:(power c:Hq)=ᵐ[μq]centeredPowerRaw c := by
    change (Constructor.zeroMean (SingularCounting.powerL2
     (OriginalPrimitiveRankBalance.conjugateCoordinate c)):Hq)=ᵐ[μq]_
    rw [Constructor.zeroMean_read]
    filter_upwards [Lp.coeFn_sub (SingularCounting.powerL2
      (OriginalPrimitiveRankBalance.conjugateCoordinate c))
      (burnolQuarterMeanCoefficient (SingularCounting.powerL2
       (OriginalPrimitiveRankBalance.conjugateCoordinate c)) • intervalConstant q),
     Lp.coeFn_smul (burnolQuarterMeanCoefficient (SingularCounting.powerL2
       (OriginalPrimitiveRankBalance.conjugateCoordinate c))) (intervalConstant q),
     SingularCounting.power_coeFn (OriginalPrimitiveRankBalance.conjugateCoordinate c),
     intervalConstant_coeFn q] with x subRead smulRead original constantRead
    rw [subRead]
    change (SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c)) x-
     (burnolQuarterMeanCoefficient (SingularCounting.powerL2
       (OriginalPrimitiveRankBalance.conjugateCoordinate c)) • intervalConstant q) x=_
    rw [smulRead]
    simp only [Pi.smul_apply,smul_eq_mul,original,constantRead,mul_one,centeredPowerRaw]
   rw [state]
   filter_upwards [Lp.coeFn_add (power c:Hq) (S (S (powerResponse c)):Hq),
     powerRead,burnolMeanZeroFourier_ae_raw (S (powerResponse c))] with x sumRead original fourierRead
   rw [sumRead]
   change (power c:Hq) x+(S (S (powerResponse c)):Hq) x=_
   rw [original,fourierRead]

open private qualified_S_pairing_left from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Price
open private fourier_even from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction

private theorem native_price_read (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) :
 inner ℂ (power c) (second c odd h)=∑i:Fin 2,inner ℂ (test c i) (drive c odd h i) := by
 have even:=congrArg (fun value:M=>(value:Hq))
  (OriginalKFiniteOrderRelease.UnitPowerJordanAction.log_B_even
   (OriginalPrimitiveRankBalance.conjugateCoordinate c) 0)
 have twiceEven:=congrArg (fun value:M=>(value:Hq))
  (fourier_even (powerResponse c)
   (OriginalKFiniteOrderRelease.UnitPowerJordanAction.log_B_even
    (OriginalPrimitiveRankBalance.conjugateCoordinate c) 0))
 have firstPair:=qualified_S_pairing_left (powerResponse c) (first c odd h) even
 have secondPair:=qualified_S_pairing_left (S (powerResponse c)) (second c odd h) twiceEven
 have firstEquation:=fixed_B_first c odd h
 have secondEquation:=fixed_B_second c odd h
 have native:powerResponse c-S (S (powerResponse c))=power c := by
  change (burnolMeanZeroOneMinusSquare*J) (power c)=_
  rw [burnolMeanZeroBlockInverse_right,one_apply_eq_self]
 simp only [Fin.sum_univ_two,test,Matrix.cons_val_zero,Matrix.cons_val_one]
 rw [←native,←firstEquation,←secondEquation]
 simp only [
  inner_sub_left,inner_add_right,inner_neg_left,firstPair,secondPair]
 ring

open private original_raw_read original_raw_even original_raw_inner original_raw_outer
 original_outer_continuousAt original_outer_slope_continuousAt native_pair_read native_pair_integrable from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource

private def signedRaw (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) (x:ℝ):ℂ:=
 outwardWeight odd i h*originalRaw c i (Real.exp h*x)+
 inwardWeight odd i h*originalRaw c i (Real.exp (-h)*x)

private theorem face_linear (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) :
 face c odd h i=
 ((if i=0 then 1 else epsilon odd)/2) • burnolMultiplicativeDilation h (originalFace c i)+
 ((if i=0 then epsilon odd else 1)/2) • burnolMultiplicativeDilation (-h) (originalFace c i) := by
 cases odd <;> fin_cases i
 · change (1/2:ℂ) •
    (burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector c:BurnolL2)+
     burnolMultiplicativeDilation (-h) (burnolCompletedMellinRieszVector c:BurnolL2))=_
   rw [smul_add]
   rfl
 · change fourierL2 (pairedBurnolMultiplicativeDilation h
    (burnolCompletedMellinRieszVector c:BurnolL2))=
    ((1:ℂ)/2) • burnolMultiplicativeDilation h (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))+
    ((1:ℂ)/2) • burnolMultiplicativeDilation (-h) (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))
   rw [←pairedBurnolMultiplicativeDilation_fourier]
   change (1/2:ℂ) •
    (burnolMultiplicativeDilation h (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))+
     burnolMultiplicativeDilation (-h) (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)))=_
   rw [smul_add]

 · change (1/2:ℂ) •
    (burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector c:BurnolL2)-
     burnolMultiplicativeDilation (-h) (burnolCompletedMellinRieszVector c:BurnolL2))=
    ((1:ℂ)/2) • burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector c:BurnolL2)+
    ((-1:ℂ)/2) • burnolMultiplicativeDilation (-h) (burnolCompletedMellinRieszVector c:BurnolL2)
   module
 · change fourierL2 ((1/2:ℂ) •
    (burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector c:BurnolL2)-
     burnolMultiplicativeDilation (-h) (burnolCompletedMellinRieszVector c:BurnolL2)))=
    ((-1:ℂ)/2) • burnolMultiplicativeDilation h (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))+
    ((1:ℂ)/2) • burnolMultiplicativeDilation (-h) (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))
   rw [map_smul,map_sub,fourierL2_burnolMultiplicativeDilation,fourierL2_burnolMultiplicativeDilation,neg_neg]
   module

private theorem face_read (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) :
 (face c odd h i:ℝ→ℂ)=ᵐ[volume] signedRaw c odd h i := by
 have dilation (s:ℝ) :
   (burnolMultiplicativeDilation s (originalFace c i):ℝ→ℂ)=ᵐ[volume]
    fun x=>(Real.exp (s/2):ℂ)*originalRaw c i (Real.exp s*x) := by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp s*x) volume volume:=by
   simpa only [smul_eq_mul] using
    (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=Real.exp s) (Real.exp_ne_zero s))
  filter_upwards [burnolMultiplicativeDilation_coeFn s (originalFace c i),
   scale.ae (original_raw_read c i)] with x actual raw
  rw [actual]
  change (Real.exp (s/2):ℂ)*originalFace c i (Real.exp s*x)=_
  rw [raw]
 rw [face_linear]
 let a:ℂ:=(if i=0 then 1 else epsilon odd)/2
 let b:ℂ:=(if i=0 then epsilon odd else 1)/2
 let left:=burnolMultiplicativeDilation h (originalFace c i)
 let right:=burnolMultiplicativeDilation (-h) (originalFace c i)
 filter_upwards [Lp.coeFn_add (a•left) (b•right),Lp.coeFn_smul a left,Lp.coeFn_smul b right,
  dilation h,dilation (-h)] with x addition firstRead secondRead firstRaw secondRaw
 change (a•left+b•right:BurnolL2) x=_
 rw [addition]
 change (a•left:BurnolL2) x+(b•right:BurnolL2) x=_
 rw [firstRead,secondRead]
 change a*left x+b*right x=_
 rw [firstRaw,secondRaw]
 simp only [a,b,signedRaw,outwardWeight,inwardWeight,neg_div]
 ring

private theorem signedRaw_even (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) (x:ℝ) :
 signedRaw c odd h i (-x)=signedRaw c odd h i x := by
 simp only [signedRaw,mul_neg,original_raw_even]

private theorem drive_position (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) :
 drive c odd h i=burnolAmbientMeanZeroPosition (face c odd h i) := by
 fin_cases i
 · rfl
 · change burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
    (burnolQuarterRestriction (fourierL2 (burnolAmbientEvenPart (nativeField c odd h))))=
   burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
    (burnolQuarterRestriction (burnolAmbientEvenPart (fourierL2 (nativeField c odd h))))
   rw [fourierL2_burnolAmbientEvenPart]

private theorem drive_read (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) :
 (drive c odd h i:Hq)=ᵐ[μq]fun x=>signedRaw c odd h i x-sourceMean c odd h i := by
 rw [drive_position]
 filter_upwards [burnolPositionMeanZero_ae_raw (face c odd h i) (signedRaw c odd h i)
  (face_read c odd h i)] with x actual
 rw [actual]
 unfold burnolPositionMeanZeroRaw burnolEvenRaw burnolMeanZeroRaw sourceMean
 dsimp only
 rw [signedRaw_even]
 ring

private theorem radius_positive (h:ℝ):0<radius h:=mul_pos (by norm_num) (Real.exp_pos _)
private theorem radius_inside (h:ℝ) (positive:0<h):radius h<q:=by
 exact (mul_lt_mul_of_pos_left (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr positive)) (by norm_num)).trans_eq (mul_one q)

private theorem source_trace (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2)
 (nonnegative:0≤h) (x:ℝ) (positive:0<x) (inside:x≤q) :
 signedRaw c odd h i x-sourceMean c odd h i=
 if x≤radius h then driverInner c odd h i else driverOuter c odd h i x := by
 have inward:Real.exp (-h)*x≤q:=by
  calc
   _ ≤ 1*q:=mul_le_mul (Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)) inside positive.le (by norm_num)
   _ =q:=one_mul _
 have inwardRaw:originalRaw c i (Real.exp (-h)*x)=originalGap c i:=
  original_raw_inner c i _ (by rw [abs_of_pos (mul_pos (Real.exp_pos _) positive)];exact inward)
 have scaled:Real.exp h*radius h=q:=by
  unfold radius
  rw [←mul_assoc,mul_comm (Real.exp h) q,mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
 unfold signedRaw
 rw [inwardRaw]
 split_ifs with interior
 · have outward:Real.exp h*x≤q:=by simpa only [scaled] using mul_le_mul_of_nonneg_left interior (Real.exp_pos h).le
   rw [original_raw_inner c i _ (by rw [abs_of_pos (mul_pos (Real.exp_pos _) positive)];exact outward)]
   unfold driverInner
   ring
 · have outward:q<Real.exp h*x:=by
    rw [←scaled]
    exact mul_lt_mul_of_pos_left (lt_of_not_ge interior) (Real.exp_pos h)
   rw [original_raw_outer c i _ outward]
   rfl

private theorem drive_piece_read (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2)
 (nonnegative:0≤h) :(drive c odd h i:Hq)=ᵐ[μq]driverRaw c odd h i := by
 filter_upwards [drive_read c odd h i,
  ae_restrict_mem (show MeasurableSet (symmetricInterval q) from measurableSet_Icc),
  ae_restrict_of_ae (s:=symmetricInterval q) (volume.ae_ne (0:ℝ))] with x raw inside nonzero
 have bound:|x|≤q:=abs_le.mpr inside
 have absolute:signedRaw c odd h i |x|=signedRaw c odd h i x := by
  rcases le_total 0 x with pos|neg
  · rw [abs_of_nonneg pos]
  · rw [abs_of_nonpos neg,signedRaw_even]
 have paid:=source_trace c odd h i nonnegative |x| (abs_pos.mpr nonzero) bound
 rw [absolute] at paid
 exact raw.trans paid

private def columnRaw (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) (x:ℝ):ℂ:=
 driverRaw c odd h i x-burnolMeanZeroFourierRaw (solution c odd h (![1,0] i)) x

private theorem column_native_read (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2)
 (nonnegative:0≤h) :(solution c odd h i:Hq)=ᵐ[μq]columnRaw c odd h i := by
 have equation:solution c odd h i+S (solution c odd h (![1,0] i))=drive c odd h i := by
  fin_cases i
  · exact fixed_B_first c odd h
  · exact (add_comm _ _).trans (fixed_B_second c odd h)
 have state:(solution c odd h i:Hq)=(drive c odd h i:Hq)-(S (solution c odd h (![1,0] i)):Hq):=
  congrArg Subtype.val (eq_sub_of_add_eq equation)
 rw [state]
 filter_upwards [Lp.coeFn_sub (drive c odd h i:Hq) (S (solution c odd h (![1,0] i)):Hq),
  drive_piece_read c odd h i nonnegative,
  burnolMeanZeroFourier_ae_raw (solution c odd h (![1,0] i))] with x difference sourceRead returnRead
 rw [difference]
 change (drive c odd h i:Hq) x-(S (solution c odd h (![1,0] i)):Hq) x=_
 rw [sourceRead,returnRead]
 rfl

private theorem column_source_jump (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) :
 (driverOuter c odd h i (radius h)-burnolMeanZeroFourierRaw (solution c odd h (![1,0] i)) (radius h))-
 (driverInner c odd h i-burnolMeanZeroFourierRaw (solution c odd h (![1,0] i)) (radius h))=jump c odd h i := by
 have scaled:Real.exp h*radius h=q := by
  unfold radius
  rw [←mul_assoc,mul_comm (Real.exp h) q,mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
 unfold driverOuter driverInner jump
 rw [scaled]
 linear_combination outwardWeight odd i h*(original_face_charge c i)

private theorem column_outer_trace (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) :
 driverOuter c odd h i q-burnolMeanZeroFourierRaw (solution c odd h (![1,0] i)) q=outerTrace c odd h i:=rfl

private theorem test_continuousAt (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) (positive:0<x) :
 ContinuousAt (testRaw c i) x := by
 fin_cases i
 · exact ((burnolRadiusTruncatedFourierRaw_continuous (powerResponse c:Hq)).sub continuous_const).continuousAt.neg
 · have native:ContinuousAt (SingularCounting.powerRaw (OriginalPrimitiveRankBalance.conjugateCoordinate c)) x:=
    (Complex.continuousAt_ofReal_cpow_const |x| _ (Or.inr (abs_ne_zero.mpr positive.ne'))).comp continuous_abs.continuousAt
   exact (native.sub continuousAt_const).add
    ((burnolRadiusTruncatedFourierRaw_continuous (S (powerResponse c):Hq)).sub continuous_const).continuousAt

private theorem meanZero_fourierRaw_even (value:M)
 (even:reflectRestricted q (value:Hq)=value) (x:ℝ) :
 burnolMeanZeroFourierRaw value (-x)=burnolMeanZeroFourierRaw value x := by
 let state:Hq:=value
 let whole:=fourierL2 (burnolQuarterZeroExtension state)
 have wholeEven:reflectL2 whole=whole := by
  change reflectL2 (fourierL2 (burnolRadiusZeroExtension q state))=_
  rw [←fourierL2_reflectL2_commute,burnolRadiusZeroExtension_reflect,even]
  rfl
 have read:(whole:ℝ→ℂ)=ᵐ[volume]burnolRadiusTruncatedFourierRaw q state:=
  burnolRadiusFourierL2_zeroExtension_ae_eq_raw state
 have reflected:(fun y:ℝ=>burnolRadiusTruncatedFourierRaw q state (-y))=ᵐ[volume]
  burnolRadiusTruncatedFourierRaw q state := by
  filter_upwards [Lp.coeFn_compMeasurePreserving whole negMeasurePreserving,
   negMeasurePreserving.quasiMeasurePreserving.ae read,read] with y reflection negative direct
  change reflectL2 whole y=whole (-y) at reflection
  rw [wholeEven] at reflection
  exact negative.symm.trans (reflection.symm.trans direct)
 have regular:=burnolRadiusTruncatedFourierRaw_continuous state
 have pointwise:=congrFun (Measure.eq_of_ae_eq (μ:=(volume:Measure ℝ)) reflected
  (regular.comp continuous_neg) regular) x
 change burnolRadiusTruncatedFourierRaw q state (-x)-_=
  burnolRadiusTruncatedFourierRaw q state x-_
 rw [pointwise]

private theorem test_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) :
 testRaw c i (-x)=testRaw c i x := by
 have even:sourceMeanZeroReflection (powerResponse c)=powerResponse c:=
  OriginalKFiniteOrderRelease.UnitPowerJordanAction.log_B_even
   (OriginalPrimitiveRankBalance.conjugateCoordinate c) 0
 have again:=fourier_even (powerResponse c) even
 fin_cases i
 · change -burnolMeanZeroFourierRaw (powerResponse c) (-x)=_
   rw [meanZero_fourierRaw_even _ (congrArg (fun v:M=>(v:Hq)) even)]
   rfl
 · change centeredPowerRaw c (-x)+burnolMeanZeroFourierRaw (S (powerResponse c)) (-x)=
    centeredPowerRaw c x+burnolMeanZeroFourierRaw (S (powerResponse c)) x
   rw [meanZero_fourierRaw_even _ (congrArg (fun v:M=>(v:Hq)) again)]
   simp only [centeredPowerRaw,SingularCounting.powerRaw,abs_neg]

private def annulusPair (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2):ℂ:=
 2*outwardWeight odd i h*
  ∫x:ℝ in (radius h)..q,star (testRaw c i x)*(originalOuter c i (Real.exp h*x)-originalGap c i)

private theorem native_driver_pair (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2)
 (positive:0<h) : inner ℂ (test c i) (drive c odd h i)=annulusPair c odd h i := by
 have raw:=drive_read c odd h i
 have testRead:=test_raw_read c i
 have native:=native_pair_read (test c i:Hq) (drive c odd h i:Hq) _ _ testRead raw
 have integrable:=native_pair_integrable (test c i:Hq) (drive c odd h i:Hq) _ _ testRead raw
 have testInt:IntervalIntegrable (fun x:ℝ=>star (testRaw c i x)) volume (-q) q := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr
  simpa only [mul_one,symmetricInterval,IntegrableOn] using native_pair_integrable (test c i:Hq) (intervalConstant q)
   (testRaw c i) (fun _=>1) testRead (intervalConstant_coeFn q)
 have zeroIntegral:(∫x:ℝ in (-q)..q,star (testRaw c i x))=0 := by
  have orthogonal:inner ℂ (intervalConstant q) (test c i:Hq)=0:=
   (Submodule.mem_orthogonal _ _).mp (test c i).property _ (Submodule.mem_span_singleton_self _)
  have reverse:inner ℂ (test c i:Hq) (intervalConstant q)=0 := by
   rw [←inner_conj_symm (test c i:Hq) (intervalConstant q),orthogonal,map_zero]
  have pair:=native_pair_read (test c i:Hq) (intervalConstant q)
   (testRaw c i) (fun _=>1) testRead (intervalConstant_coeFn q)
  simpa only [mul_one] using pair.symm.trans reverse
 let reduced (x:ℝ):ℂ:=star (testRaw c i x)*
  (signedRaw c odd h i x-sourceMean c odd h i-driverInner c odd h i)
 have reducedInt:IntervalIntegrable reduced volume (-q) q := by
  have originalInt:IntervalIntegrable
   (fun x:ℝ=>star (testRaw c i x)*(signedRaw c odd h i x-sourceMean c odd h i)) volume (-q) q:=
   (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr integrable
  convert originalInt.sub (testInt.mul_const (driverInner c odd h i)) using 1
  funext x
  dsimp only [reduced]
  ring
 have reducedEven (x:ℝ):reduced (-x)=reduced x := by
  dsimp only [reduced]
  rw [test_even,signedRaw_even]
 have reduction:(∫x:ℝ in (-q)..q,star (testRaw c i x)*
   (signedRaw c odd h i x-sourceMean c odd h i))=∫x:ℝ in (-q)..q,reduced x := by
  calc
   _ = (∫x:ℝ in (-q)..q,reduced x)+
       ∫x:ℝ in (-q)..q,star (testRaw c i x)*driverInner c odd h i := by
    rw [←intervalIntegral.integral_add reducedInt (testInt.mul_const _)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [reduced]
    ring
   _ = _ := by rw [intervalIntegral.integral_mul_const,zeroIntegral,zero_mul,add_zero]
 have low:=reducedInt.mono_set (show uIcc (-q) 0⊆uIcc (-q) q by
   rw [uIcc_of_le (by norm_num:-q≤0),uIcc_of_le (by norm_num:-q≤q)]
   exact Icc_subset_Icc le_rfl (by norm_num))
 have high:=reducedInt.mono_set (show uIcc 0 q⊆uIcc (-q) q by
   rw [uIcc_of_le (by norm_num:0≤q),uIcc_of_le (by norm_num:-q≤q)]
   exact Icc_subset_Icc (by norm_num) le_rfl)
 have negative:(∫x:ℝ in (-q)..0,reduced x)=∫x:ℝ in 0..q,reduced x := by
  have generated:=intervalIntegral.integral_comp_neg (f:=reduced) (a:=(0:ℝ)) (b:=q)
  simp only [neg_zero] at generated
  rw [←generated]
  apply intervalIntegral.integral_congr
  intro x _
  exact reducedEven x
 have lower:=high.mono_set (show uIcc 0 (radius h)⊆uIcc 0 q by
   rw [uIcc_of_le (radius_positive h).le,uIcc_of_le (by norm_num:0≤q)]
   exact Icc_subset_Icc le_rfl (radius_inside h positive).le)
 have upper:=high.mono_set (show uIcc (radius h) q⊆uIcc 0 q by
   rw [uIcc_of_le (radius_inside h positive).le,uIcc_of_le (by norm_num:0≤q)]
   exact Icc_subset_Icc (radius_positive h).le le_rfl)
 have zeroLower:(∫x:ℝ in 0..radius h,reduced x)=0 := by
  calc
   _ =∫x:ℝ in 0..radius h,(0:ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (radius_positive h).le
    intro x hx
    dsimp only [reduced]
    rw [source_trace c odd h i positive.le x hx.1 (hx.2.le.trans (radius_inside h positive).le),
     if_pos hx.2.le,sub_self,mul_zero]
   _ =0:=by simp only [intervalIntegral.integral_zero]
 have upperRead:(∫x:ℝ in radius h..q,reduced x)=
   outwardWeight odd i h*∫x:ℝ in radius h..q,star (testRaw c i x)*
    (originalOuter c i (Real.exp h*x)-originalGap c i) := by
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le (radius_inside h positive).le
  intro x hx
  dsimp only [reduced]
  rw [source_trace c odd h i positive.le x ((radius_positive h).trans hx.1) hx.2.le,
   if_neg (not_le_of_gt hx.1)]
  unfold driverOuter driverInner
  ring
 change inner ℂ (test c i:Hq) (drive c odd h i:Hq)=_
 rw [native,reduction,←intervalIntegral.integral_add_adjacent_intervals low high,negative,
  ←intervalIntegral.integral_add_adjacent_intervals lower upper,zeroLower,zero_add,upperRead]
 unfold annulusPair
 ring

private theorem parameter_integral_derivative
 (f df:ℝ→ℝ→ℂ) (regular:Continuous (Function.uncurry f))
 (slope:Continuous (Function.uncurry df))
 (derivative:∀s x,HasDerivAt (fun t=>f t x) (df s x) s) (h a b:ℝ) :
 HasDerivAt (fun s=>∫x in a..b,f s x) (∫x in a..b,df h x) h := by
 obtain ⟨bound,bounded⟩:=(isCompact_Icc.prod isCompact_uIcc).bddAbove_image
  (show ContinuousOn (fun v:ℝ×ℝ=>‖df v.1 v.2‖) ((Icc (h-1) (h+1))×ˢ(uIcc a b)) from
   slope.norm.continuousOn)
 have neighbourhood:Icc (h-1) (h+1)∈𝓝 h:=Icc_mem_nhds (by linarith) (by linarith)
 apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
   (F:=f) (F':=df) (bound:=fun _=>bound) neighbourhood
   (Eventually.of_forall fun s=>(regular.uncurry_left s).aestronglyMeasurable)
   ((regular.uncurry_left h).intervalIntegrable a b)
   (slope.uncurry_left h).aestronglyMeasurable ?_
   (continuous_const.intervalIntegrable a b) ?_).2
 · filter_upwards with x hx s hs
   exact bounded (mem_image_of_mem (fun v:ℝ×ℝ=>‖df v.1 v.2‖)
    (show (s,x)∈(Icc (h-1) (h+1))×ˢ(uIcc a b) from ⟨hs,uIoc_subset_uIcc hx⟩))
 · filter_upwards with x _ s _ using derivative s x

private theorem moving_integral_derivative
 (f df:ℝ→ℝ→ℂ) (regular:Continuous (Function.uncurry f))
 (slope:Continuous (Function.uncurry df))
 (derivative:∀s x,HasDerivAt (fun t=>f t x) (df s x) s)
 (p:ℝ→ℝ) (h b dp:ℝ) (boundary:HasDerivAt p dp h) :
 HasDerivAt (fun s=>∫x in p s..b,f s x)
  ((∫x in p h..b,df h x)-(dp:ℂ)*f h (p h)) h := by
 let primitive (s y:ℝ):ℂ:=∫x in y..b,f s x
 let firstDerivative (s y:ℝ):ℝ→L[ℝ]ℂ:=
  (1:ℝ→L[ℝ]ℝ).smulRight (∫x in y..b,df s x)
 let secondDerivative (s y:ℝ):ℝ→L[ℝ]ℂ:=
  (1:ℝ→L[ℝ]ℝ).smulRight (-f s y)
 have partialFirst:∀ᶠv:ℝ×ℝ in 𝓝 (h,p h),
   HasFDerivAt (fun s=>primitive s v.2) (firstDerivative v.1 v.2) v.1 :=
  Eventually.of_forall fun v=>(parameter_integral_derivative f df regular slope derivative v.1 v.2 b).hasFDerivAt
 have partialSecond:∀ᶠv:ℝ×ℝ in 𝓝 (h,p h),
   HasFDerivAt (primitive v.1) (secondDerivative v.1 v.2) v.2 := by
  filter_upwards with v
  exact (intervalIntegral.integral_hasDerivAt_left
   ((regular.uncurry_left v.1).intervalIntegrable v.2 b)
   (regular.uncurry_left v.1).stronglyMeasurable.stronglyMeasurableAtFilter
   (regular.uncurry_left v.1).continuousAt).hasFDerivAt
 have continuousIntegral:Continuous (fun v:ℝ×ℝ=>∫x in v.2..b,df v.1 x) := by
  have generated:=intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
   (μ:=volume) (a₀:=b) (f:=fun v:ℝ×ℝ=>df v.1)
   (slope.comp (continuous_fst.fst.prodMk continuous_snd)) continuous_snd
  convert! generated.neg using 1
  funext v
  exact intervalIntegral.integral_symm b v.2
 have firstContinuous:ContinuousAt (Function.uncurry firstDerivative) (h,p h) := by
  dsimp only [firstDerivative,Function.uncurry]
  exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1:ℝ→L[ℝ]ℝ)).continuous.comp continuousIntegral).continuousAt
 have secondContinuous:ContinuousAt (Function.uncurry secondDerivative) (h,p h) := by
  dsimp only [secondDerivative,Function.uncurry]
  exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1:ℝ→L[ℝ]ℝ)).continuous.comp regular.neg).continuousAt
 have generated:HasFDerivAt (Function.uncurry primitive)
   ((firstDerivative h (p h)).coprod (secondDerivative h (p h))) (h,p h):=
  (hasStrictFDerivAt_uncurry_coprod (𝕜:=ℝ) (f:=primitive)
   (f₁:=firstDerivative) (f₂:=secondDerivative)
   partialFirst partialSecond firstContinuous secondContinuous).hasFDerivAt
 have path:HasDerivAt (fun s=>(s,p s)) (1,dp) h:=(hasDerivAt_id h).prodMk boundary
 have paid:=generated.comp_hasDerivAt h path
 change HasDerivAt (fun s=>∫x in p s..b,f s x)
  ((1:ℝ) • (∫x in p h..b,df h x)+dp • (-f h (p h))) h at paid
 simpa only [one_smul,Complex.real_smul,mul_neg,sub_eq_add_neg] using paid

open private position_hasDerivAt from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice

private theorem outer_positive_derivative (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) (positive:0<x) :
 HasDerivAt (originalOuter c i) (originalOuterSlope c i x) x := by
 fin_cases i
 · have paid:=(position_hasDerivAt c x positive).add_const (positionMean c)
   convert! paid using 1
   funext y
   rw [positionSource_eq_outer_sub_mean]
   change burnolRieszStatePositiveOuterRaw c y=
    (burnolRieszStatePositiveOuterRaw c y-positionMean c)+positionMean c
   ring
 · exact (sourceRaw_hasDerivAt c x positive.ne').add_const (fourierMean c)

private theorem radius_continuous:Continuous radius:=continuous_const.mul (Real.continuous_exp.comp continuous_neg)
private theorem radius_derivative (h:ℝ):HasDerivAt radius (-radius h) h := by
 have paid:=((Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_id h).neg).const_mul q
 convert! paid using 1
 unfold radius
 ring

private theorem outward_derivative (odd:Bool) (i:Fin 2) (h:ℝ) :
 HasDerivAt (outwardWeight odd i) ((1/2:ℂ)*outwardWeight odd i h) h := by
 have realDerivative:HasDerivAt (fun s:ℝ=>Real.exp (s/2)) (Real.exp (h/2)/2) h := by
  convert! (Real.hasDerivAt_exp (h/2)).comp h ((hasDerivAt_id h).div_const 2) using 1
  ring
 have complexDerivative:HasDerivAt (fun s:ℝ=>(Real.exp (s/2):ℂ)) ((Real.exp (h/2)/2:ℝ):ℂ) h :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt h realDerivative
 change HasDerivAt (fun s=>(Real.exp (s/2):ℂ)/2*(if i=0 then 1 else epsilon odd)) _ h
 convert! (complexDerivative.div_const (2:ℂ)).mul_const (if i=0 then 1 else epsilon odd) using 1
 unfold outwardWeight
 push_cast
 ring

private theorem annulus_integral_derivative (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
 (h:ℝ) :
 HasDerivAt (fun s=>∫x:ℝ in radius s..q,star (testRaw c i x)*
   (originalOuter c i (Real.exp s*x)-originalGap c i))
  ((∫x:ℝ in radius h..q,star (testRaw c i x)*
    (((Real.exp h*x:ℝ):ℂ)*originalOuterSlope c i (Real.exp h*x)))+
   (radius h:ℂ)*star (testRaw c i (radius h))*originalCharge c i) h := by
 let a:ℝ:=min (radius h) q/2
 have minimumPositive:0<min (radius h) q:=lt_min (radius_positive h) (by norm_num)
 have apos:0<a:=half_pos minimumPositive
 let clamp (x:ℝ):ℝ:=max a x
 have clampContinuous:Continuous clamp:=continuous_const.max continuous_id
 have clampPositive (x:ℝ):0<clamp x:=apos.trans_le (le_max_left _ _)
 have testContinuous:Continuous (fun x:ℝ=>testRaw c i (clamp x)):=
  continuous_iff_continuousAt.mpr fun x=>(test_continuousAt c i _ (clampPositive x)).comp clampContinuous.continuousAt
 let scale (v:ℝ×ℝ):ℝ:=Real.exp v.1*clamp v.2
 have scaleContinuous:Continuous scale:=
  (Real.continuous_exp.comp continuous_fst).mul (clampContinuous.comp continuous_snd)
 have scalePositive (v:ℝ×ℝ):0<scale v:=mul_pos (Real.exp_pos _) (clampPositive _)
 have outerContinuous:Continuous (fun v:ℝ×ℝ=>originalOuter c i (scale v)):=
  continuous_iff_continuousAt.mpr fun v=>(original_outer_continuousAt c i _ (scalePositive v)).comp scaleContinuous.continuousAt
 have slopeContinuous:Continuous (fun v:ℝ×ℝ=>originalOuterSlope c i (scale v)):=
  continuous_iff_continuousAt.mpr fun v=>(original_outer_slope_continuousAt c i _ (scalePositive v)).comp scaleContinuous.continuousAt
 let f (s x:ℝ):ℂ:=star (testRaw c i (clamp x))*(originalOuter c i (Real.exp s*clamp x)-originalGap c i)
 let df (s x:ℝ):ℂ:=star (testRaw c i (clamp x))*
  (((Real.exp s*clamp x:ℝ):ℂ)*originalOuterSlope c i (Real.exp s*clamp x))
 have regular:Continuous (Function.uncurry f):=
  (testContinuous.comp continuous_snd).star.mul (outerContinuous.sub continuous_const)
 have slope:Continuous (Function.uncurry df):=
  (testContinuous.comp continuous_snd).star.mul
   ((Complex.continuous_ofReal.comp scaleContinuous).mul slopeContinuous)
 have derivative (s x:ℝ):HasDerivAt (fun t=>f t x) (df s x) s := by
  have moved:HasDerivAt (fun t:ℝ=>Real.exp t*clamp x) (Real.exp s*clamp x) s:=
   (Real.hasDerivAt_exp s).mul_const _
  have acted:HasDerivAt (fun t=>originalOuter c i (Real.exp t*clamp x))
    (((Real.exp s*clamp x:ℝ):ℂ)*originalOuterSlope c i (Real.exp s*clamp x)) s := by
   simpa only [Function.comp_def,Complex.real_smul] using!
    (outer_positive_derivative c i _ (scalePositive (s,x))).scomp s moved
  exact (acted.sub_const (originalGap c i)).const_mul _
 have generated:=moving_integral_derivative f df regular slope derivative radius h q (-radius h) (radius_derivative h)
 have low:a<min (radius h) q:=half_lt_self minimumPositive
 have lowRadius:a<radius h:=low.trans_le (min_le_left _ _)
 have lowQuarter:a<q:=low.trans_le (min_le_right _ _)
 have near:∀ᶠs in 𝓝 h,a<radius s:=
  radius_continuous.continuousAt.eventually (lt_mem_nhds lowRadius)
 have agree:(fun s=>∫x:ℝ in radius s..q,star (testRaw c i x)*
   (originalOuter c i (Real.exp s*x)-originalGap c i))=ᶠ[𝓝 h]
   (fun s=>∫x in radius s..q,f s x) := by
  filter_upwards [near] with s hs
  apply intervalIntegral.integral_congr
  intro x hx
  change min (radius s) q≤x ∧ x≤max (radius s) q at hx
  dsimp only [f,clamp]
  rw [max_eq_right ((le_min hs.le lowQuarter.le).trans hx.1)]
 have paid:=generated.congr_of_eventuallyEq agree
 have integralRead:(∫x in radius h..q,df h x)=
   ∫x:ℝ in radius h..q,star (testRaw c i x)*
    (((Real.exp h*x:ℝ):ℂ)*originalOuterSlope c i (Real.exp h*x)) := by
  apply intervalIntegral.integral_congr
  intro x hx
  change min (radius h) q≤x ∧ x≤max (radius h) q at hx
  dsimp only [df,clamp]
  rw [max_eq_right (low.le.trans hx.1)]
 have scaled:Real.exp h*radius h=q := by
  unfold radius
  rw [←mul_assoc,mul_comm (Real.exp h) q,mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
 have atBoundary:f h (radius h)=star (testRaw c i (radius h))*originalCharge c i := by
  dsimp only [f,clamp]
  rw [max_eq_right lowRadius.le,scaled,original_face_charge]
 convert! paid using 1
 rw [integralRead,atBoundary,Complex.ofReal_neg]
 ring

private def annulusSlope (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2):ℂ:=
 (1/2:ℂ)*annulusPair c odd h i+2*outwardWeight odd i h*
  ((∫x:ℝ in radius h..q,star (testRaw c i x)*
    (((Real.exp h*x:ℝ):ℂ)*originalOuterSlope c i (Real.exp h*x)))+
   (radius h:ℂ)*star (testRaw c i (radius h))*originalCharge c i)

private theorem annulus_derivative (c:BurnolCompletedMellinCoordinate) (odd:Bool) (i:Fin 2) (h:ℝ) :
 HasDerivAt (fun s=>annulusPair c odd s i) (annulusSlope c odd h i) h := by
 have paid:=((outward_derivative odd i h).const_mul (2:ℂ)).mul (annulus_integral_derivative c i h)
 apply paid.congr_deriv
 unfold annulusSlope annulusPair
 ring

private theorem annulus_forcing (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2)
 (nonnegative:0≤h) :annulusSlope c odd h i=
  -PsiDrive.sourceRate c i*annulusPair c odd h i+
   annulusForcing c odd h i+jumpForcing c odd h i := by
 have bounds:radius h≤q:=by
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative))
   (by norm_num:0≤q)).trans_eq (mul_one q)
 have pos:∀x∈uIcc (radius h) q,0<x:=by
  intro x hx
  rw [uIcc_of_le bounds] at hx
  exact (radius_positive h).trans_le hx.1
 have testRegular:ContinuousOn (testRaw c i) (uIcc (radius h) q):=
  fun x hx=>(test_continuousAt c i x (pos x hx)).continuousWithinAt
 have outerRegular:ContinuousOn (fun x:ℝ=>originalOuter c i (Real.exp h*x)) (uIcc (radius h) q):=
  fun x hx=>((original_outer_continuousAt c i _ (mul_pos (Real.exp_pos h) (pos x hx))).comp
   (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
 have slopeRegular:ContinuousOn (fun x:ℝ=>originalOuterSlope c i (Real.exp h*x)) (uIcc (radius h) q):=
  fun x hx=>((original_outer_slope_continuousAt c i _ (mul_pos (Real.exp_pos h) (pos x hx))).comp
   (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
 have originalInt:IntervalIntegrable (fun x:ℝ=>star (testRaw c i x)*
   (originalOuter c i (Real.exp h*x)-originalGap c i)) volume (radius h) q :=
  (testRegular.star.mul (outerRegular.sub continuousOn_const)).intervalIntegrable
 have slopeInt:IntervalIntegrable (fun x:ℝ=>star (testRaw c i x)*
   (((Real.exp h*x:ℝ):ℂ)*originalOuterSlope c i (Real.exp h*x))) volume (radius h) q :=
  (testRegular.star.mul
   ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).continuousOn.mul slopeRegular)).intervalIntegrable
 have scaled:Real.exp h*radius h=q := by
  unfold radius
  rw [←mul_assoc,mul_comm (Real.exp h) q,mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
 have integrated:(∫x:ℝ in radius h..q,star (testRaw c i x)*
   (PsiDrive.psiCoupling c i (Real.exp h*x)-(1/2+PsiDrive.sourceRate c i)*originalGap c i))=
   (∫x:ℝ in radius h..q,star (testRaw c i x)*
    (((Real.exp h*x:ℝ):ℂ)*originalOuterSlope c i (Real.exp h*x)))+
   (1/2+PsiDrive.sourceRate c i)*∫x:ℝ in radius h..q,star (testRaw c i x)*
    (originalOuter c i (Real.exp h*x)-originalGap c i) := by
  calc
   _ =∫x:ℝ in radius h..q,
       (star (testRaw c i x)*(((Real.exp h*x:ℝ):ℂ)*originalOuterSlope c i (Real.exp h*x))+
        (1/2+PsiDrive.sourceRate c i)*(star (testRaw c i x)*
         (originalOuter c i (Real.exp h*x)-originalGap c i))) := by
    apply intervalIntegral.integral_congr_Ioo_of_le bounds
    intro x hx
    have outside:q<Real.exp h*x:=by
     rw [←scaled]
     exact mul_lt_mul_of_pos_left hx.1 (Real.exp_pos h)
    have paid:=outer_coupling c i _ outside
    linear_combination -(star (testRaw c i x))*paid
   _ =_ :=by rw [intervalIntegral.integral_add slopeInt (originalInt.const_mul _),intervalIntegral.integral_const_mul]
 unfold annulusSlope annulusForcing jumpForcing jump
 rw [integrated]
 unfold annulusPair
 ring

private theorem rate_swap (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) :
 (∑i:Fin 2,PsiDrive.sourceRate c i*annulusPair c odd h i)=
 lambda c*∑i:Fin 2,annulusPair c (!odd) h i := by
 simp only [Fin.sum_univ_two]
 cases odd <;> norm_num [PsiDrive.sourceRate,annulusPair,outwardWeight,epsilon,lambda] <;> ring

private theorem price_annulus_read (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (positive:0<h) :
 inner ℂ (power c) (second c odd h)=∑i:Fin 2,annulusPair c odd h i := by
 rw [native_price_read]
 apply Finset.sum_congr rfl
 intro i _
 exact native_driver_pair c odd h i positive

private theorem positive_integral_continuous (f:ℝ→ℝ→ℂ)
 (regular:∀s x,0<x→ContinuousAt (Function.uncurry f) (s,x)) :
 Continuous (fun s=>∫x:ℝ in radius s..q,f s x) := by
 apply continuous_iff_continuousAt.mpr
 intro h
 let a:ℝ:=min (radius h) q/2
 have positive:0<min (radius h) q:=lt_min (radius_positive h) (by norm_num)
 have low:a<min (radius h) q:=half_lt_self positive
 let clip (x:ℝ):ℝ:=max a x
 have clipContinuous:Continuous clip:=continuous_const.max continuous_id
 have clipPositive (x:ℝ):0<clip x:=(half_pos positive).trans_le (le_max_left _ _)
 let g (s x:ℝ):ℂ:=f s (clip x)
 have clipped:Continuous (Function.uncurry g):=continuous_iff_continuousAt.mpr fun v=>
  ContinuousAt.comp (f:=fun u:ℝ×ℝ=>(u.1,clip u.2)) (g:=Function.uncurry f)
   (regular v.1 (clip v.2) (clipPositive _))
   (continuous_fst.prodMk (clipContinuous.comp continuous_snd)).continuousAt
 have primitive:=intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  (μ:=volume) (a₀:=q) clipped radius_continuous
 have whole:Continuous (fun s=>∫x:ℝ in radius s..q,g s x) := by
  convert! primitive.neg using 1
  funext s
  exact intervalIntegral.integral_symm q (radius s)
 have near:∀ᶠs in 𝓝 h,a<radius s:=radius_continuous.continuousAt.eventually
  (lt_mem_nhds (low.trans_le (min_le_left _ _)))
 apply whole.continuousAt.congr_of_eventuallyEq
 filter_upwards [near] with s hs
 apply intervalIntegral.integral_congr
 intro x hx
 change min (radius s) q≤x ∧ x≤max (radius s) q at hx
 dsimp only [g,clip]
 rw [max_eq_right ((le_min hs.le (low.trans_le (min_le_right _ _)).le).trans hx.1)]

private theorem annulus_continuous (c:BurnolCompletedMellinCoordinate) (odd:Bool) (i:Fin 2):
 Continuous (fun s=>annulusPair c odd s i):=
 continuous_iff_continuousAt.mpr fun h=>(annulus_derivative c odd i h).continuousAt

private theorem annulusSlope_continuous (c:BurnolCompletedMellinCoordinate) (odd:Bool) (i:Fin 2):
 Continuous (fun s=>annulusSlope c odd s i) := by
 have sourceIntegral:Continuous (fun s=>∫x:ℝ in radius s..q,star (testRaw c i x)*
   (((Real.exp s*x:ℝ):ℂ)*originalOuterSlope c i (Real.exp s*x))) := by
  apply positive_integral_continuous
  intro s x positive
  have scale:ContinuousAt (fun v:ℝ×ℝ=>Real.exp v.1*v.2) (s,x):=
   ((Real.continuous_exp.comp continuous_fst).mul continuous_snd).continuousAt
  have testAt:ContinuousAt (fun v:ℝ×ℝ=>testRaw c i v.2) (s,x):=
   ContinuousAt.comp (f:=fun v:ℝ×ℝ=>v.2) (g:=testRaw c i)
    (test_continuousAt c i x positive) continuous_snd.continuousAt
  exact testAt.star.mul ((Complex.continuous_ofReal.continuousAt.comp scale).mul
   (ContinuousAt.comp (f:=fun v:ℝ×ℝ=>Real.exp v.1*v.2) (g:=originalOuterSlope c i)
    (original_outer_slope_continuousAt c i _ (mul_pos (Real.exp_pos s) positive)) scale))
 have traceContinuous:Continuous (fun s=>testRaw c i (radius s)):=
  continuous_iff_continuousAt.mpr fun h=>(test_continuousAt c i _ (radius_positive h)).comp radius_continuous.continuousAt
 have weight:Continuous (outwardWeight odd i):=
  continuous_iff_continuousAt.mpr fun h=>(outward_derivative odd i h).continuousAt
 unfold annulusSlope
 exact (continuous_const.mul (annulus_continuous c odd i)).add
  ((continuous_const.mul weight).mul
   (sourceIntegral.add (((Complex.continuous_ofReal.comp radius_continuous).mul traceContinuous.star).mul continuous_const)))

private theorem price_annulus_nonnegative (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (nonnegative:0≤h) :
 inner ℂ (power c) (second c odd h)=∑i:Fin 2,annulusPair c odd h i := by
 rcases eq_or_lt_of_le nonnegative with zero|positive
 · subst h
   rw [(native_zero_columns c odd).2,inner_zero_right]
   simp only [annulusPair,radius,neg_zero,Real.exp_zero,mul_one,intervalIntegral.integral_same,mul_zero,Finset.sum_const_zero]
 · exact price_annulus_read c odd h positive

private theorem native_charge_continuous (c:BurnolCompletedMellinCoordinate) (odd:Bool):
 ContinuousOn (nativeCharge c odd) (Icc 0 junctionShift) := by
 have source:Continuous (fun s=>(-2*sigma c)*∑i:Fin 2,annulusPair c odd s i):=
  continuous_const.mul (continuous_finsetSum _ fun i _=>annulus_continuous c odd i)
 apply source.continuousOn.congr
 intro h hh
 rw [nativeCharge,price_annulus_nonnegative c odd h hh.1]

private theorem forcing_continuous (c:BurnolCompletedMellinCoordinate) (odd:Bool):
 ContinuousOn (forcing c odd) (Icc 0 junctionShift) := by
 have source:Continuous (fun s=>(-2*sigma c)*∑i:Fin 2,
   (annulusSlope c odd s i+PsiDrive.sourceRate c i*annulusPair c odd s i)):=
  continuous_const.mul (continuous_finsetSum _ fun i _=>
   (annulusSlope_continuous c odd i).add (continuous_const.mul (annulus_continuous c odd i)))
 apply source.continuousOn.congr
 intro h hh
 unfold forcing
 congr 1
 apply Finset.sum_congr rfl
 intro i _
 have paid:=annulus_forcing c odd h i hh.1
 linear_combination -paid

/-- Source rates are the already-paid opposite Euler rates; the new obligation is the moving interface. -/
theorem native_weak_system (c:BurnolCompletedMellinCoordinate) : WeakSystem c := by
 intro h hh odd
 have sumDerivative:HasDerivAt (fun s=>∑i:Fin 2,annulusPair c odd s i)
   (∑i:Fin 2,annulusSlope c odd h i) h:=
  HasDerivAt.fun_sum (fun i _=>annulus_derivative c odd i h)
 have sameFunction:(fun s=>inner ℂ (power c) (second c odd s))=ᶠ[𝓝 h]
   (fun s=>∑i:Fin 2,annulusPair c odd s i) := by
  filter_upwards [Ioo_mem_nhds hh.1 hh.2] with s hs
  exact price_annulus_read c odd s hs.1
 have scalar:=sumDerivative.congr_of_eventuallyEq sameFunction
 have scalarRhs:(∑i:Fin 2,annulusSlope c odd h i)=
   -lambda c*inner ℂ (power c) (second c (!odd) h)+
    ∑i:Fin 2,(annulusForcing c odd h i+jumpForcing c odd h i) := by
  simp_rw [annulus_forcing c odd h _ hh.1.le]
  rw [price_annulus_read c (!odd) h hh.1]
  simp only [Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib]
  rw [rate_swap]
  ring
 have paid:=(scalar.congr_deriv scalarRhs).const_mul (-2*sigma c)
 change HasDerivAt (fun s=>(-2*sigma c)*inner ℂ (power c) (second c odd s)) _ h
 apply paid.congr_deriv
 unfold nativeCharge forcing
 ring

private theorem charge_duhamel (f F:ℝ→ℂ) (a:ℂ) (h:ℝ) (nonnegative:0≤h)
 (state:ContinuousOn f (Icc 0 h)) (source:ContinuousOn F (Icc 0 h))
 (velocity:∀s∈Ioo 0 h,HasDerivAt f (a*f s+F s) s) (initial:f 0=0) :
 (∫s:ℝ in 0..h,Complex.exp (a*((h-s:ℝ):ℂ))*F s)=f h := by
 let weight (s:ℝ):ℂ:=Complex.exp (-a*(s:ℂ))
 have regular:Continuous weight:=by fun_prop
 have primitive:ContinuousOn (fun s=>weight s*f s) (Icc 0 h):=regular.continuousOn.mul state
 have derivative (s:ℝ) (inside:s∈Ioo 0 h):
  HasDerivAt (fun t=>weight t*f t) (weight s*F s) s := by
  have cast:HasDerivAt (fun t:ℝ=>(t:ℂ)) 1 s:=Complex.ofRealCLM.hasDerivAt
  have generated:=((cast.const_mul (-a)).cexp).mul (velocity s inside)
  apply generated.congr_deriv
  dsimp only [weight]
  ring
 have integrable:IntervalIntegrable (fun s=>weight s*F s) volume 0 h:=by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le nonnegative] using! regular.continuousOn.mul source
 have paid:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le nonnegative primitive derivative integrable
 simp only [weight,Complex.ofReal_zero,mul_zero,Complex.exp_zero,initial,sub_zero] at paid
 calc
  _ =Complex.exp (a*(h:ℂ))*(∫s:ℝ in 0..h,weight s*F s) := by
   rw [←intervalIntegral.integral_const_mul]
   apply intervalIntegral.integral_congr
   intro s _
   dsimp only [weight]
   rw [←mul_assoc,←Complex.exp_add]
   congr 2
   push_cast
   ring
  _ =_ :=by
   rw [paid,←mul_assoc,←Complex.exp_add]
   simp only [show a*(h:ℂ)+ -a*(h:ℂ)=0 by ring,Complex.exp_zero,one_mul]

/-- The explicit source bills are read back by the actual B charge on the original half-window. -/
theorem source_charge_read (c:BurnolCompletedMellinCoordinate) (odd:Bool)
 (h:ℝ) (inside:h∈Icc 0 junctionShift) :sourceCharge c odd h=nativeCharge c odd h := by
 let plus (s:ℝ):ℂ:=nativeCharge c false s+nativeCharge c true s
 let minus (s:ℝ):ℂ:=nativeCharge c false s-nativeCharge c true s
 let plusSource (s:ℝ):ℂ:=forcing c false s+forcing c true s
 let minusSource (s:ℝ):ℂ:=forcing c false s-forcing c true s
 have subset:Icc 0 h⊆Icc 0 junctionShift:=Icc_subset_Icc le_rfl inside.2
 have statePlus:ContinuousOn plus (Icc 0 h):=
  ((native_charge_continuous c false).add (native_charge_continuous c true)).mono subset
 have stateMinus:ContinuousOn minus (Icc 0 h):=
  ((native_charge_continuous c false).sub (native_charge_continuous c true)).mono subset
 have sourcePlus:ContinuousOn plusSource (Icc 0 h):=
  ((forcing_continuous c false).add (forcing_continuous c true)).mono subset
 have sourceMinus:ContinuousOn minusSource (Icc 0 h):=
  ((forcing_continuous c false).sub (forcing_continuous c true)).mono subset
 have velocities (s:ℝ) (hs:s∈Ioo 0 h):
  HasDerivAt plus (-lambda c*plus s+plusSource s) s ∧
  HasDerivAt minus (lambda c*minus s+minusSource s) s := by
  have lo:=native_weak_system c s ⟨hs.1,hs.2.trans_le inside.2⟩ false
  have hi:=native_weak_system c s ⟨hs.1,hs.2.trans_le inside.2⟩ true
  change HasDerivAt (nativeCharge c false) (-lambda c*nativeCharge c true s+forcing c false s) s at lo
  change HasDerivAt (nativeCharge c true) (-lambda c*nativeCharge c false s+forcing c true s) s at hi
  constructor
  · apply (lo.add hi).congr_deriv
    dsimp only [plus,plusSource]
    ring
  · apply (lo.sub hi).congr_deriv
    dsimp only [minus,minusSource]
    ring
 have initialPlus:plus 0=0:=by simp only [plus,native_zero_charge,add_zero]
 have initialMinus:minus 0=0:=by simp only [minus,native_zero_charge,sub_zero]
 have first:=charge_duhamel plus plusSource (-lambda c) h inside.1 statePlus sourcePlus
  (fun s hs=>(velocities s hs).1) initialPlus
 have second:=charge_duhamel minus minusSource (lambda c) h inside.1 stateMinus sourceMinus
  (fun s hs=>(velocities s hs).2) initialMinus
 have firstRead:eigenBill c false h=plus h:=by
  simpa only [eigenBill,Bool.false_eq_true,if_false,one_mul,Complex.ofReal_sub,plusSource] using first
 have secondRead:eigenBill c true h=minus h:=by
  simpa only [eigenBill,if_true,neg_one_mul,Complex.ofReal_sub,sub_eq_add_neg,Complex.ofReal_add,Complex.ofReal_neg,minusSource] using second
 rw [sourceCharge,firstRead,secondRead]
 cases odd <;> norm_num [epsilon,plus,minus] <;> ring

namespace Actual
namespace C
export BurnolPhysicalState.CountedPaInitial.CompletedSourceRCalculation
 (sourceFace prefixCode environment actual_completed_original_R same_original_child same_original_next)
end C
namespace Terminal
export OriginalBoundaryGammaTerminalConsumer
 (currentPrefix targetGamma target_gamma_source actual_terminal_price originalWholeNext target_canonical_next)
end Terminal
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (N:Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

def sourceGamma : ℂ := sourceCharge c false junctionShift

theorem actual_Gamma : sourceGamma observation half=
 Terminal.targetGamma observation nontrivial half depth ordinal t N := by
 rw [sourceGamma,source_charge_read c false junctionShift ⟨junctionShift_pos.le,le_rfl⟩,original_even_charge]
 exact (Terminal.target_gamma_source observation nontrivial half depth ordinal t N).symm

include ordinal t N in
theorem actual_receiver :
 inner ℂ (OriginalWholeDebtRAdjointContactSource.sourceEffect c c)
  ((C.prefixCode observation nontrivial half).eval (C.environment observation nontrivial half depth))=
 star (sourceGamma observation half)*OriginalWholeDebtRJointMobiusReturnJordanSource.feedback observation nontrivial half*
  burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation := by
 have sameCurrent:= (C.same_original_child observation nontrivial half depth ordinal t N).trans
  (OriginalBoundaryGammaTerminalConsumer.current_prefix_read observation nontrivial half depth ordinal t N)
 have inputRead:=congrArg (fun value:BurnolL2=>inner ℂ
  (OriginalWholeDebtRAdjointContactSource.sourceEffect c c) value) sameCurrent
 have outputRead:=congrArg (fun value:ℂ=>star value*
  OriginalWholeDebtRJointMobiusReturnJordanSource.feedback observation nontrivial half*
  burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation)
  (actual_Gamma observation nontrivial half depth ordinal t N).symm
 exact inputRead.trans ((Terminal.actual_terminal_price observation nontrivial half depth ordinal t N).trans outputRead)

def actual_weak_ward_source_consumer :=
 PProd.mk (C.sourceFace observation nontrivial half depth ordinal).rootRead <|
 PProd.mk (calculation c false junctionShift) <|
 PProd.mk (fun i:Fin 2=>column_native_read c false junctionShift i junctionShift_pos.le) <|
 PProd.mk (fun i:Fin 2=>column_source_jump c false junctionShift i) <|
 PProd.mk (fun i:Fin 2=>column_outer_trace c false junctionShift i) <|
 PProd.mk (calculation c true junctionShift) <|
 PProd.mk (fun i:Fin 2=>column_native_read c true junctionShift i junctionShift_pos.le) <|
 PProd.mk (fun i:Fin 2=>column_source_jump c true junctionShift i) <|
 PProd.mk (fun i:Fin 2=>column_outer_trace c true junctionShift i) <|
 PProd.mk (native_zero_charge c false) <|
 PProd.mk (native_zero_charge c true) <|
 PProd.mk (native_zero_B0_retained c false) <|
 PProd.mk (native_zero_B0_retained c true) <|
 PProd.mk (native_weak_system c) <|
 PProd.mk (actual_Gamma observation nontrivial half depth ordinal t N) <|
 PProd.mk (actual_receiver observation nontrivial half depth ordinal t N) <|
 PProd.mk (OriginalBoundaryGammaConsumer.sourceBoundaryB0 observation nontrivial half depth ordinal t N) <|
 PProd.mk (C.actual_completed_original_R observation nontrivial half depth ordinal t N)
 (Terminal.target_canonical_next observation nontrivial half depth ordinal t N)
end Actual
end OriginalKPairedWeakWardSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
