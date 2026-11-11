import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRReciprocalCotestActionSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFiniteColumns
open OriginalKSourceResolventReconstruction
open OriginalWholeDebtRPowerWaveDilationSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "h" => OriginalKPairedBEulerJunctionSource.junctionShift
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "DT" => TemperedDistribution ℝ ℂ
local notation "F" => fourierL2
local notation "U" => burnolMultiplicativeDilation
local notation "Tate" => burnolTateReciprocalL2
local notation "Eq" => burnolQuarterZeroExtension
local notation "cut" => OriginalPaPhysicalGreen.originalPhysicalCutoff
local notation "step" => OriginalWholeDebtRAdjointContactSource.step
open private primitiveInputRaw nativeRaw thetaRaw thetaSlope amplitude innerLower primitiveInput primitive_input_even input_read native_raw_continuous theta_derivative reciprocalRaw forcingRaw reciprocalSlope bandRaw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestSource
open private theta_q from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestSource
open private even_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRContactSource

private theorem cutoff_even (radius : ℝ) (value : BurnolL2) (even : reflectL2 value=value) :
    reflectL2 (cut radius value)=cut radius value := by
  have restricted:=restrictToInterval_reflectL2 radius value
  change burnolRadiusRestriction radius (reflectL2 value)=
    reflectRestricted radius (burnolRadiusRestriction radius value) at restricted
  rw [even] at restricted
  change reflectL2 (burnolRadiusZeroExtension radius (burnolRadiusRestriction radius value))=_
  rw [burnolRadiusZeroExtension_reflect,←restricted]
  rfl

private theorem reciprocal_derivative (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0 < x) : HasDerivAt (reciprocalRaw c) (reciprocalSlope c x) x := by
  have moved : HasDerivAt (fun t : ℝ => Real.exp (-h)/t)
      (-Real.exp (-h)/x^2) x := by
    convert! (hasDerivAt_const x (Real.exp (-h))).div (hasDerivAt_id x) positive.ne' using 1
    simp
  have inverted : HasDerivAt (fun t : ℝ => (t : ℂ)⁻¹) (-1/(x : ℂ)^2) x :=
    Complex.ofRealCLM.hasDerivAt.inv (Complex.ofReal_ne_zero.mpr positive.ne')
  have generated:=((inverted.const_mul amplitude).mul
    ((theta_derivative c (div_pos (Real.exp_pos _) positive)).scomp x moved))
  have same : reciprocalRaw c=(fun t : ℝ => amplitude*(t : ℂ)⁻¹)*
      (thetaRaw c ∘ fun t : ℝ => Real.exp (-h)/t) := by
    funext t
    simp only [reciprocalRaw,div_eq_mul_inv,Pi.mul_apply,Function.comp_def]
  rw [←same] at generated
  have slope : reciprocalSlope c x=
      amplitude*(-1/(x : ℂ)^2)*thetaRaw c (Real.exp (-h)/x)+
        amplitude*(x : ℂ)⁻¹*((-Real.exp (-h)/x^2) • thetaSlope c (Real.exp (-h)/x)) := by
    unfold reciprocalSlope reciprocalRaw forcingRaw thetaSlope frequency
    simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_exp]
    have xn : (x : ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
    have en : (Real.exp (-h) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    field_simp [xn,en]
    ring
  change HasDerivAt (reciprocalRaw c) _ x at generated
  simp only [Function.comp_def] at generated
  rw [←slope] at generated
  exact generated

private theorem reciprocal_continuous (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0 < x) : ContinuousAt (reciprocalRaw c) x :=
  (reciprocal_derivative c positive).continuousAt

private theorem reciprocal_slope_continuous (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0 < x) : ContinuousAt (reciprocalSlope c) x := by
  have moved : ContinuousAt (fun t : ℝ => Real.exp (-h)/t) x :=
    continuousAt_const.div continuousAt_id positive.ne'
  have native : ContinuousAt (fun t : ℝ => nativeRaw c (Real.exp (-h)/t)+coupling1 c) x :=
    ((native_raw_continuous c).continuousAt.comp moved).add continuousAt_const
  have coefficient : ContinuousAt (fun t : ℝ => amplitude/(t : ℂ)) x :=
    continuousAt_const.div Complex.continuous_ofReal.continuousAt
    (Complex.ofReal_ne_zero.mpr positive.ne')
  have source : ContinuousAt (forcingRaw c) x := coefficient.mul native
  exact (((continuousAt_const.mul (reciprocal_continuous c positive)).sub source).sub
    (continuousAt_const.mul (reciprocal_continuous c positive))).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr positive.ne')

private theorem forcing_input_read (c : BurnolCompletedMellinCoordinate) :
    (nativeForcingInput c : ℝ → ℂ)=ᵐ[volume]
      (symmetricInterval q).indicator (fun t => nativeRaw c t+coupling1 c) := by
  filter_upwards [Lp.coeFn_add (nativeInput c) (coupling1 c • Constant.seed),
    Lp.coeFn_smul (coupling1 c) Constant.seed,input_read c,Constant.seed_coeFn]
    with x addition scalar source constant
  change (nativeInput c+coupling1 c • Constant.seed : BurnolL2) x=_
  rw [addition,Pi.add_apply,scalar]
  change nativeInput c x+coupling1 c*Constant.seed x=_
  rw [source,constant]
  by_cases inside : x∈symmetricInterval q
  · simp only [indicator_of_mem inside,Constant.seedRaw,if_pos (abs_le.mpr inside),mul_one]
  · simp only [indicator_of_notMem inside,Constant.seedRaw,
      if_neg (fun hx => inside (abs_le.mp hx)),mul_zero,zero_add]

private theorem actual_forcing_source (c : BurnolCompletedMellinCoordinate) :
    (forcing c : ℝ → ℂ)=ᵐ[volume]
      fun x => if lower < |x| ∧ |x| ≤ 4 then forcingRaw c |x| else 0 := by
  let native : ℝ → ℂ := (symmetricInterval q).indicator (fun t => nativeRaw c t+coupling1 c)
  have input:=forcing_input_read c
  have transformed:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (nativeForcingInput c))
    ((Lp.memLp (nativeForcingInput c)).ae_eq input) input
  have tateRead:=(burnolTateReciprocalL2_coeFn (nativeForcingInput c)).trans transformed
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := Real.exp h) (Real.exp_ne_zero _)
  have nativeEven : reflectL2 (nativeForcingInput c)=nativeForcingInput c := by
    have seedEven : reflectL2 Constant.seed=Constant.seed := by
      change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
      rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
      rfl
    simp only [nativeForcingInput,nativeInput,map_add,map_sub,map_smul,
      Response.wholeU_reflection,Response.wholeV_reflection,seedEven]
  have even : reflectL2 (forcing c)=forcing c := by
    unfold forcing
    rw [map_smul]
    apply congrArg (fun value : BurnolL2 => (1/2 : ℂ) • value)
    apply cutoff_even
    rw [reflectL2_burnolMultiplicativeDilation,←burnolTateReciprocal_reflect,nativeEven]
  apply even_read (forcing c) _ even (by intro x; simp only [abs_neg])
  filter_upwards [Lp.coeFn_smul (1/2 : ℂ) (cut 4 (U h (Tate (nativeForcingInput c)))),
    OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn 4 (U h (Tate (nativeForcingInput c))),
    burnolMultiplicativeDilation_coeFn h (Tate (nativeForcingInput c)),qmp.ae_eq tateRead,
    volume.ae_ne lower] with x scalar cutRead moved source notLower positive
  simp only [Function.comp_def] at source
  change ((1/2 : ℂ) • cut 4 (U h (Tate (nativeForcingInput c))) : BurnolL2) x=_
  rw [scalar]
  change (1/2 : ℂ)*cut 4 (U h (Tate (nativeForcingInput c))) x=_
  rw [cutRead]
  simp only [abs_of_pos positive]
  by_cases bound : x ≤ 4
  · rw [indicator_of_mem (show x∈symmetricInterval 4 from ⟨by linarith,bound⟩),moved]
    unfold burnolL2RawNormalizedDilation
    rw [source]
    unfold burnolTateReciprocalRaw
    have ep : 0 < Real.exp h*x := mul_pos (Real.exp_pos _) positive
    have inverse : (Real.exp h*x)⁻¹=Real.exp (-h)/x := by rw [mul_inv_rev,Real.exp_neg];ring
    have inside : (Real.exp h*x)⁻¹∈symmetricInterval q ↔ lower < x := by
      change (-q ≤ (Real.exp h*x)⁻¹ ∧ (Real.exp h*x)⁻¹ ≤ q) ↔ lower < x
      have ip : 0 < (Real.exp h*x)⁻¹ := inv_pos.mpr ep
      rw [and_iff_right (by linarith : -q ≤ (Real.exp h*x)⁻¹)]
      rw [inv_eq_one_div,div_le_iff₀ ep]
      have cancel : Real.exp h*Real.exp (-h)=1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
      have lowerIdentity : Real.exp h*lower=4 := by
        unfold lower
        calc
          _=4*(Real.exp h*Real.exp (-h)) := by ring
          _=4 := by rw [cancel,mul_one]
      constructor
      · intro hx
        have shifted:=mul_le_mul_of_nonneg_right hx (Real.exp_pos (-h)).le
        have product : q*(Real.exp h*x)*Real.exp (-h)=q*x := by
          calc
            _=q*x*(Real.exp h*Real.exp (-h)) := by ring
            _=_ := by rw [cancel,mul_one]
        rw [one_mul,product] at shifted
        have weak : lower ≤ x := by unfold lower;nlinarith
        exact lt_of_le_of_ne weak notLower.symm
      · intro hx
        have shifted:=mul_lt_mul_of_pos_left hx (Real.exp_pos h)
        rw [lowerIdentity] at shifted
        nlinarith
    simp only [bound,and_true]
    by_cases after : lower < x
    · rw [indicator_of_mem (inside.mpr after),if_pos after,abs_of_pos ep,inverse]
      unfold forcingRaw amplitude
      have density : (Real.exp (h/2) : ℂ)*((Real.exp h*x : ℝ) : ℂ)⁻¹=
          (Real.exp (-h/2) : ℂ)/(x : ℂ) := by
        rw [Complex.ofReal_mul,mul_inv_rev]
        have phase : (Real.exp (h/2) : ℂ)*(Real.exp h : ℂ)⁻¹=(Real.exp (-h/2) : ℂ) := by
          rw [←Complex.ofReal_inv,←Complex.ofReal_mul,←Real.exp_neg,←Real.exp_add]
          congr 1
          ring
        calc
          _=((Real.exp (h/2) : ℂ)*(Real.exp h : ℂ)⁻¹)*(x : ℂ)⁻¹ := by ring
          _=(Real.exp (-h/2) : ℂ)*(x : ℂ)⁻¹ := congrArg (fun z : ℂ => z*(x : ℂ)⁻¹) phase
          _=(Real.exp (-h/2) : ℂ)/(x : ℂ) := (div_eq_mul_inv _ _).symm
      calc
        _=(1/2 : ℂ)*(((Real.exp (h/2) : ℂ)*((Real.exp h*x : ℝ) : ℂ)⁻¹)*
            (nativeRaw c (Real.exp (-h)/x)+coupling1 c)) := by ring
        _=_ := by rw [density];simp only [div_eq_mul_inv];ring
    · rw [indicator_of_notMem (fun hx => after (inside.mp hx)),if_neg after]
      simp only [mul_zero]
  · rw [indicator_of_notMem (show x∉symmetricInterval 4 from fun hx => bound hx.2),
      if_neg (fun hx => bound hx.2),mul_zero]

namespace Piece
export OriginalKPairedBEulerJunctionSource.TwoPieceFourierAction
  (pieceRaw bulkRaw piece_native pieceBulk pieceBulk_read weak_two_piece_euler)
end Piece
private def compression : ℝ := 2*Real.log 4

private theorem compression_scales :
    Real.exp compression=16 ∧ Real.exp (compression/2)=4 := by
  have positive : (0 : ℝ) < 4 := by norm_num
  constructor
  · rw [compression,two_mul,Real.exp_add,Real.exp_log positive]
    norm_num
  · rw [compression,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ)≠0),Real.exp_log positive]

private theorem compressed_read (value : BurnolL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ)=ᵐ[volume] raw) :
    (U compression value : ℝ → ℂ)=ᵐ[volume] fun x => (4 : ℂ)*raw (16*x) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp compression*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := Real.exp compression) (Real.exp_ne_zero _)
  filter_upwards [burnolMultiplicativeDilation_coeFn compression value,qmp.ae_eq read]
    with x moved rawRead
  simp only [Function.comp_def] at rawRead
  rw [moved]
  change (Real.exp (compression/2) : ℂ)*value (Real.exp compression*x)=_
  rw [rawRead,compression_scales.1,compression_scales.2]
  norm_num

private def scaledRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (4 : ℂ)*reciprocalRaw c (16*x)
private def scaledSlope (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (64 : ℂ)*reciprocalSlope c (16*x)
private def scaledForcing (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (4 : ℂ)*forcingRaw c (16*x)

private theorem inner_bounds : 0 < innerLower ∧ innerLower < q :=
  OriginalKPairedBEulerJunctionSource.junctionPoint_bounds

private theorem scaled_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (scaledRaw c) (Icc innerLower q) := by
  intro x inside
  have source:=reciprocal_continuous c (x := 16*x) (by linarith [inner_bounds.1,inside.1])
  have moved : ContinuousAt (fun t : ℝ => 16*t) x := continuousAt_const.mul continuousAt_id
  exact (continuousAt_const.mul (source.comp moved) :
    ContinuousAt (fun t : ℝ => (4 : ℂ)*reciprocalRaw c (16*t)) x).continuousWithinAt

private theorem scaled_slope_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (scaledSlope c) (Icc innerLower q) := by
  intro x inside
  have source:=reciprocal_slope_continuous c (x := 16*x) (by linarith [inner_bounds.1,inside.1])
  have moved : ContinuousAt (fun t : ℝ => 16*t) x := continuousAt_const.mul continuousAt_id
  exact (continuousAt_const.mul (source.comp moved) :
    ContinuousAt (fun t : ℝ => (64 : ℂ)*reciprocalSlope c (16*t)) x).continuousWithinAt

private theorem scaled_derivative (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : x∈Ioo innerLower q) : HasDerivAt (scaledRaw c) (scaledSlope c x) x := by
  have source:=reciprocal_derivative c (x := 16*x) (by linarith [inner_bounds.1,inside.1])
  have generated:=(source.scomp x ((hasDerivAt_id x).const_mul (16 : ℝ))).const_mul (4 : ℂ)
  simp only [mul_one] at generated
  change HasDerivAt (scaledRaw c) ((4 : ℂ)*((16 : ℝ) • reciprocalSlope c (16*x))) x at generated
  have slope : scaledSlope c x=(4 : ℂ)*((16 : ℝ) • reciprocalSlope c (16*x)) := by
    unfold scaledSlope
    rw [Complex.real_smul]
    norm_num
    ring
  rwa [←slope] at generated

private def piece (c : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  (Piece.piece_native innerLower inner_bounds.1 inner_bounds.2 (fun _ => 0) (scaledRaw c)
    continuousOn_const (scaled_continuous c)).toLp
      (Piece.pieceRaw innerLower (fun _ => 0) (scaledRaw c))

private theorem piece_read (c : BurnolCompletedMellinCoordinate) :
    (piece c : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)]
      Piece.pieceRaw innerLower (fun _ => 0) (scaledRaw c) := MemLp.coeFn_toLp _

private theorem piece_realizes_source (c : BurnolCompletedMellinCoordinate) :
    Eq (piece c)=U compression (reciprocalCotest c) := by
  have source:=compressed_read (reciprocalCotest c) (bandRaw c) (actual_reciprocal_source c)
  have read:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (piece_read c)
  apply Lp.ext
  filter_upwards [burnolRadiusZeroExtension_coe (piece c),source,read] with x extended acted localRead
  change burnolRadiusZeroExtension q (piece c) x=_
  rw [extended,acted]
  simp only [bandRaw,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  have lowerScale : lower=16*innerLower := by unfold lower innerLower;ring
  by_cases bound : x∈symmetricInterval q
  · rw [indicator_of_mem bound,localRead bound]
    unfold Piece.pieceRaw scaledRaw
    have small : 16*|x| ≤ 4 := by have:=abs_le.mpr bound;linarith
    by_cases inner : |x| ≤ innerLower
    · rw [if_pos inner,if_neg (fun after => by rw [lowerScale] at after;linarith [after.1])]
      ring
    · rw [if_neg inner,if_pos ⟨by rw [lowerScale];linarith,small⟩]
  · have outside : 4 < 16*|x| := by have:=lt_of_not_ge (fun hx => bound (abs_le.mp hx));linarith
    rw [indicator_of_notMem bound,if_neg (fun inside => outside.not_ge inside.2),mul_zero]

private def bulk (c : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  Piece.pieceBulk innerLower inner_bounds.1 inner_bounds.2
    (fun _ => 0) (fun _ => 0) (scaledRaw c) (scaledSlope c)
    continuousOn_const continuousOn_const (scaled_continuous c) (scaled_slope_continuous c)

private theorem bulk_realizes_source (c : BurnolCompletedMellinCoordinate) :
    Eq (bulk c)=frequency c • U compression (reciprocalCotest c)-U compression (forcing c) := by
  have pieceSource:=piece_realizes_source c
  have raw:=Piece.pieceBulk_read innerLower inner_bounds.1 inner_bounds.2
    (fun _ => 0) (fun _ => 0) (scaledRaw c) (scaledSlope c)
    continuousOn_const continuousOn_const (scaled_continuous c) (scaled_slope_continuous c)
  change (bulk c : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)]
    Piece.bulkRaw innerLower (fun _ => 0) (fun _ => 0) (scaledRaw c) (scaledSlope c) at raw
  have localRead:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp raw
  have first:=compressed_read (reciprocalCotest c) (bandRaw c) (actual_reciprocal_source c)
  have second:=compressed_read (forcing c)
    (fun x => if lower < |x| ∧ |x| ≤ 4 then forcingRaw c |x| else 0) (actual_forcing_source c)
  apply Lp.ext
  filter_upwards [burnolRadiusZeroExtension_coe (bulk c),localRead,first,second,
    Lp.coeFn_sub (frequency c • U compression (reciprocalCotest c)) (U compression (forcing c)),
    Lp.coeFn_smul (frequency c) (U compression (reciprocalCotest c))] with x extended localRead r f difference scalar
  change burnolRadiusZeroExtension q (bulk c) x=_
  rw [extended,difference,Pi.sub_apply,scalar]
  change _=frequency c*U compression (reciprocalCotest c) x-U compression (forcing c) x
  rw [r,f]
  simp only [bandRaw,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  have lowerScale : lower=16*innerLower := by unfold lower innerLower;ring
  by_cases bound : x∈symmetricInterval q
  · rw [indicator_of_mem bound,localRead bound]
    unfold Piece.bulkRaw Piece.pieceRaw
    have small : 16*|x| ≤ 4 := by have:=abs_le.mpr bound;linarith
    by_cases inner : |x| ≤ innerLower
    · have noBand : ¬(lower < 16*|x| ∧ 16*|x| ≤ 4) := by
        intro after
        rw [lowerScale] at after
        linarith [after.1]
      simp only [if_pos inner,if_neg noBand,mul_zero,add_zero,sub_zero]
    · have positive : 0 < |x| := inner_bounds.1.trans (lt_of_not_ge inner)
      have band : lower < 16*|x| ∧ 16*|x| ≤ 4 := ⟨by rw [lowerScale];linarith,small⟩
      rw [if_neg inner]
      simp only [if_pos band]
      unfold scaledRaw scaledSlope reciprocalSlope
      have xn : ((|x| : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
      push_cast
      field_simp [xn]
      ring
  · have outside : 4 < 16*|x| := by have:=lt_of_not_ge (fun hx => bound (abs_le.mp hx));linarith
    have noBand : ¬(lower < 16*|x| ∧ 16*|x| ≤ 4) := fun inside => outside.not_ge inside.2
    rw [indicator_of_notMem bound]
    simp only [if_neg noBand,mul_zero,sub_zero]

private theorem scaled_traces (c : BurnolCompletedMellinCoordinate) :
    scaledRaw c innerLower=(4 : ℂ)*lowerTrace c ∧
      scaledRaw c q=(4 : ℂ)*upperTrace c := by
  have lp : 0 < lower := by unfold lower;positivity
  have lowerScale : 16*innerLower=lower := by unfold innerLower lower;ring
  have reciprocal : Real.exp (-h)/lower=q := by
    unfold lower
    field_simp [Real.exp_ne_zero]
  constructor
  · rw [scaledRaw,lowerScale,reciprocalRaw,reciprocal,theta_q]
    rfl
  · unfold scaledRaw reciprocalRaw upperTrace
    rw [show 16*q=(4 : ℝ) by norm_num,
      show Real.exp (-h)/4=innerLower by unfold innerLower;ring]
    norm_num

private theorem translated_test (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    coPoissonSchwartzEnergyTranslation compression test x=(4 : ℂ)*test (16*x) := by
  change (Real.exp compression : ℂ)^(1/2 : ℂ)*test (Real.exp compression*x)=_
  have half : (Real.exp compression : ℂ)^(1/2 : ℂ)=(4 : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ←Complex.ofReal_log (Real.exp_pos compression).le,Real.log_exp]
    have exponent : (compression : ℂ)*(1/2 : ℂ)=((compression/2 : ℝ) : ℂ) := by push_cast;ring
    rw [exponent,←Complex.ofReal_exp,compression_scales.2]
    norm_num
  rw [half,compression_scales.1]

/-- The actual reciprocal column generates the full band Euler law, including both contacts. -/
theorem actual_reciprocal_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (reciprocalCotest c : DT)-frequency c • (reciprocalCotest c : DT)=
      -(forcing c : DT)+((lower : ℂ)*lowerTrace c) •
        (TemperedDistribution.delta lower+TemperedDistribution.delta (-lower))-
      ((4 : ℂ)*upperTrace c) •
        (TemperedDistribution.delta 4+TemperedDistribution.delta (-4)) := by
  have generated:=Piece.weak_two_piece_euler innerLower inner_bounds.1 inner_bounds.2
    (fun _ => 0) (fun _ => 0) (scaledRaw c) (scaledSlope c)
    continuousOn_const continuousOn_const (scaled_continuous c) (scaled_slope_continuous c)
    (fun x _ => hasDerivAt_const x (0 : ℂ)) (fun x hx => scaled_derivative c hx)
    (piece c) (piece_read c)
  change GapEuler.euler (Eq (piece c) : DT)=(Eq (bulk c) : DT)+
    ((innerLower : ℂ)*(scaledRaw c innerLower-0)) •
      (TemperedDistribution.delta innerLower+TemperedDistribution.delta (-innerLower))-
    ((q : ℂ)*scaledRaw c q) •
      (TemperedDistribution.delta q+TemperedDistribution.delta (-q)) at generated
  rw [piece_realizes_source] at generated
  have bulkDistribution : (Eq (bulk c) : DT)=
      frequency c • (U compression (reciprocalCotest c) : DT)-
        (U compression (forcing c) : DT) := by
    rw [bulk_realizes_source]
    change Lp.toTemperedDistributionCLM ℂ volume 2
      (frequency c • U compression (reciprocalCotest c)-U compression (forcing c))=_
    rw [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistributionCLM_apply]
  rw [bulkDistribution] at generated
  ext test
  have read:=congrArg (fun source : DT => source (coPoissonSchwartzEnergyTranslation compression test)) generated
  simp only [sub_apply,add_apply,neg_apply,smul_apply,TemperedDistribution.delta_apply,smul_eq_mul] at read ⊢
  rw [OriginalRieszFiniteResponse.original_euler_action] at read
  rw [OriginalRieszFiniteResponse.original_read,OriginalRieszFiniteResponse.original_read] at read
  have inverse : coPoissonSchwartzEnergyTranslation (-compression)
      (coPoissonSchwartzEnergyTranslation compression test)=test := by
    have action:=congrArg (fun transform : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ => transform test)
      (coPoissonSchwartzEnergyTranslation_add (-compression) compression)
    simpa only [LinearMap.comp_apply,neg_add_cancel,coPoissonSchwartzEnergyTranslation_zero] using action
  rw [inverse,(scaled_traces c).1,(scaled_traces c).2] at read
  simp only [sub_zero,translated_test] at read
  have lowerScale : 16*innerLower=lower := by unfold innerLower lower;ring
  simp only [mul_neg,lowerScale,show (16 : ℝ)*q=4 by norm_num,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at read
  have lowerComplex : (lower : ℂ)=(16 : ℂ)*(innerLower : ℂ) := by exact_mod_cast lowerScale.symm
  rw [lowerComplex]
  linear_combination read
end OriginalWholeDebtRReciprocalCotestActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
