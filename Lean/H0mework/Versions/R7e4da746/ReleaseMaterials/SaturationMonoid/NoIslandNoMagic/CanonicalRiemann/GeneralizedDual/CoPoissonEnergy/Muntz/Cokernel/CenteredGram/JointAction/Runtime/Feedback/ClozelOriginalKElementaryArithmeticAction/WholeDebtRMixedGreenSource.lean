import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRMixedGreenSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalKPairedBEulerJunctionSource
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
open private source_face_read paired_raw_even original_raw_inner original_raw_outer
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
open private face outwardRaw kernelInner kernel_inner
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRContactSource
open private inputRaw input_read prefixRaw prefix_integrable actedRaw acted_read acted_continuous
  innerRaw fullRaw outsideRaw regularRaw full_read native_continuous
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private physical_fourier_projection
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockAction
open private correction_raw_even source_action_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockEuler
open private position_hasDerivAt
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice
local notation "q" => (1/4 : ℝ)
local notation "p" => junctionPoint
local notation "h" => junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "F" => fourierL2
local notation "C" => BandFullStockEuler.correctionRaw
local notation "mu" => burnolQuarterMeanCoefficient
local notation "T" => burnolTruncatedFourier
local notation "phi" => BandFiniteSourcePrice.sourceColumn

def sourceProfile (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : ℝ → ℂ :=
  ![positionSource c,burnolRieszSingleFourierSourceRaw c] i

/-- The two original means and both Fourier-unit means remain in the actual source charge. -/
def meanCharge (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : ℂ :=
  (((Real.exp (h/2) : ℂ)+(Real.exp (-h/2) : ℂ))/2)*originalGap c i-
    sourceMean c i+mu (T (sourcePartner c i : Hq))

def bandInput (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  meanCharge c i+(Real.exp (h/2) : ℂ)/2*sourceProfile c i (Real.exp h*x)

private def radius (x : ℝ) : ℝ := max (p/2) x
private def weight (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  ![(radius x : ℂ)^(c.value-1)*bandInput c 0 (radius x),
    (radius x : ℂ)^(-c.value)*bandInput c 1 (radius x)] i
private def prefixSeed (c : BurnolCompletedMellinCoordinate) : ℂ :=
  ∫ s : ℝ in 0..p,(s : ℂ)^(c.value-1)*inputRaw c 0 s
private def tailSeed (c : BurnolCompletedMellinCoordinate) : ℂ :=
  ∫ s : ℝ in Ioi p,(s : ℂ)^(-c.value)*(F (C c)) s

/-- This current is built from actual C input and its two source integrals, before R is read. -/
def sourceCurrent (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  ![-2*(x : ℂ)^(-c.value)*(prefixSeed c+∫ s : ℝ in p..x,weight c 0 s),
    -2*(x : ℂ)^(c.value-1)*(tailSeed c-∫ s : ℝ in p..x,weight c 1 s)] i

private theorem source_profile_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    {x : ℝ} (positive : 0<x) : ContinuousAt (sourceProfile c i) x := by
  fin_cases i
  · exact positionSource_continuousAt c positive
  · exact burnolRieszSingleFourierSourceRaw_continuousAt c positive.ne'

private theorem weight_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Continuous (weight c i) := by
  have rp : ∀ x : ℝ,0<radius x := fun x => lt_of_lt_of_le (by linarith [junctionPoint_bounds.1]) (le_max_left _ _)
  have rc : Continuous radius := continuous_const.max continuous_id
  have input (j : Fin 2) : Continuous (fun x : ℝ => bandInput c j (radius x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have moved : ContinuousAt (fun y : ℝ => Real.exp h*radius y) x := continuousAt_const.mul rc.continuousAt
    have rawAt : ContinuousAt (sourceProfile c j) (Real.exp h*radius x) :=
      source_profile_continuous c j (mul_pos (Real.exp_pos h) (rp x))
    have comp : ContinuousAt (fun y : ℝ => sourceProfile c j (Real.exp h*radius y)) x := ContinuousAt.comp (f := fun y : ℝ => Real.exp h*radius y) rawAt moved
    exact continuousAt_const.add (continuousAt_const.mul comp)
  have power (e : ℂ) : Continuous (fun x : ℝ => (radius x : ℂ)^e) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (Complex.continuousAt_ofReal_cpow_const (radius x) e (Or.inr (rp x).ne')).comp rc.continuousAt
  fin_cases i
  · exact (power _).mul (input 0)
  · exact (power _).mul (input 1)

theorem actual_source_current_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (inside : p/2<x) :
    HasDerivAt (sourceCurrent c i)
      (![(-c.value*sourceCurrent c 0 x-2*bandInput c 0 x)/(x : ℂ),
        ((c.value-1)*sourceCurrent c 1 x+2*bandInput c 1 x)/(x : ℂ)] i) x := by
  have positive : 0<x := lt_trans (by linarith [junctionPoint_bounds.1] : (0 : ℝ)<p/2) inside
  have actual (j : Fin 2) := intervalIntegral.integral_hasDerivAt_right
    ((weight_continuous c j).intervalIntegrable p x)
    (weight_continuous c j).stronglyMeasurable.stronglyMeasurableAtFilter
    (weight_continuous c j).continuousAt
  have atRadius : radius x=x := max_eq_right inside.le
  have powerAt (e : ℂ) : HasDerivAt (fun y : ℝ => (y : ℂ)^e) (e*(x : ℂ)^(e-1)) x :=
    (Complex.hasStrictDerivAt_cpow_const (c := e) (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal
  have xn : (x : ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have pn : (x : ℂ)^c.value≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl xn)
  fin_cases i
  · change HasDerivAt (fun y : ℝ => -2*(y : ℂ)^(-c.value)*(prefixSeed c+∫ s : ℝ in p..y,weight c 0 s))
      ((-c.value*sourceCurrent c 0 x-2*bandInput c 0 x)/(x : ℂ)) x
    convert! ((powerAt (-c.value)).const_mul (-2)).mul ((actual 0).const_add (prefixSeed c)) using 1
    dsimp only [sourceCurrent,Matrix.cons_val_zero]
    have wx : weight c 0 x=(x : ℂ)^(c.value-1)*bandInput c 0 x := by
      change (radius x : ℂ)^(c.value-1)*bandInput c 0 (radius x)=_
      rw [atRadius]
    rw [wx]
    simp only [Complex.cpow_sub _ _ xn,Complex.cpow_one,Complex.cpow_neg]
    field_simp [xn,pn]
    ring
  · change HasDerivAt (fun y : ℝ => -2*(y : ℂ)^(c.value-1)*(tailSeed c-∫ s : ℝ in p..y,weight c 1 s))
      (((c.value-1)*sourceCurrent c 1 x+2*bandInput c 1 x)/(x : ℂ)) x
    convert! ((powerAt (c.value-1)).const_mul (-2)).mul ((actual 1).const_sub (tailSeed c)) using 1
    dsimp only [sourceCurrent,Matrix.cons_val_one,Matrix.cons_val_zero]
    have wx : weight c 1 x=(x : ℂ)^(-c.value)*bandInput c 1 x := by
      change (radius x : ℂ)^(-c.value)*bandInput c 1 (radius x)=_
      rw [atRadius]
    rw [wx]
    simp only [Complex.cpow_sub _ _ xn,Complex.cpow_one,Complex.cpow_neg]
    field_simp [xn,pn]

private theorem input_band_read (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (face i (C c) : ℝ → ℂ)=ᵐ[volume.restrict (Ioc p q)] bandInput c i := by
  have raw := burnolRawCorrection_ae_raw (sourceFace c i) (pairedRaw c i) (source_face_read c i)
  have evenRaw := burnolEvenRaw_ae _ _ raw
  have actual : burnolAmbientEvenMeanZeroCorrection (sourceFace c i)=face i (C c) := by
    fin_cases i
    · change burnolAmbientEvenPart (C c)=C c
      unfold burnolAmbientEvenPart
      rw [correction_raw_even]
      module
    · have same := congrArg F (BandFullStockEuler.source_action_projection c)
      rw [map_sub] at same
      have projectionFace := congrArg (fun v : BurnolPaAmbientCarrier => (v : BurnolL2))
        (physical_fourier_projection (sourceAction c))
      change (burnolEvenAmbientProjection (F (sourceAction c)) : BurnolL2)=F (burnolEvenAmbientProjection (sourceAction c) : BurnolL2) at projectionFace
      rw [←projectionFace] at same
      have projection := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (sourceFace c 1)
      unfold burnolAmbientExtendedSonineProjectionFormula at projection
      change _=burnolAmbientEvenPart (F (sourceAction c))-_ at projection
      have even : burnolAmbientEvenPart (F (sourceAction c))=F (sourceAction c) := by
        rw [←fourierL2_burnolAmbientEvenPart]
        congr 1
        unfold burnolAmbientEvenPart
        rw [source_action_even]
        module
      rw [even] at projection
      change (burnolEvenAmbientProjection (F (sourceAction c)) : BurnolL2)=
        F (sourceAction c)-burnolAmbientEvenMeanZeroCorrection (F (sourceAction c)) at projection
      change burnolAmbientEvenMeanZeroCorrection (F (sourceAction c))=F (C c)
      exact sub_right_inj.mp (projection.symm.trans same)
  change ((burnolAmbientEvenMeanZeroCorrection (sourceFace c i) : BurnolL2) : ℝ → ℂ)=ᵐ[volume] _ at evenRaw
  rw [actual] at evenRaw
  filter_upwards [ae_restrict_of_ae evenRaw,ae_restrict_mem measurableSet_Ioc] with x read hx
  rw [read]
  have pos : 0<x := junctionPoint_bounds.1.trans hx.1
  have small : x∈symmetricInterval q := ⟨by linarith,hx.2⟩
  have rev : -x∈symmetricInterval q := ⟨neg_le_neg hx.2,by linarith [pos]⟩
  have outer : q<Real.exp h*x := by
    have inequality := mul_lt_mul_of_pos_left hx.1 (Real.exp_pos h)
    rwa [junction_scaled] at inequality
  have inner : |Real.exp (-h)*x|≤q := by
    rw [abs_of_pos (mul_pos (Real.exp_pos _) pos)]
    have bound := Real.exp_le_one_iff.mpr (by linarith [junctionShift_pos] : -h≤0)
    calc
      Real.exp (-h)*x≤1*x := mul_le_mul_of_nonneg_right bound pos.le
      _=x := one_mul x
      _≤q := hx.2
  have partner : burnolAmbientMeanZeroSecondCorrection (sourceFace c i)=sourcePartner c i := by
    fin_cases i
    · rfl
    · exact (OriginalKFiniteOrderRelease.GenericSourceStepBAction.B_fourier (sourceAction c)).2
  dsimp only [burnolEvenRaw,burnolRawCorrectionRaw]
  rw [indicator_of_mem small,indicator_of_mem rev]
  change (1/2 : ℂ)*((burnolEvenRaw (pairedRaw c i) x-sourceMean c i-
      burnolMeanZeroFourierRaw (burnolAmbientMeanZeroSecondCorrection (sourceFace c i)) x+
        burnolRadiusTruncatedFourierRaw q (burnolAmbientMeanZeroSecondCorrection (sourceFace c i) : Hq) x)+
    (burnolEvenRaw (pairedRaw c i) (-x)-sourceMean c i-
      burnolMeanZeroFourierRaw (burnolAmbientMeanZeroSecondCorrection (sourceFace c i)) (-x)+
        burnolRadiusTruncatedFourierRaw q (burnolAmbientMeanZeroSecondCorrection (sourceFace c i) : Hq) (-x)))=_
  rw [partner]
  unfold burnolMeanZeroFourierRaw burnolEvenRaw
  simp only [paired_raw_even,neg_neg]
  unfold bandInput meanCharge pairedRaw
  rw [original_raw_outer c i _ outer,original_raw_inner c i _ inner]
  have split : originalOuter c i (Real.exp h*x)=sourceProfile c i (Real.exp h*x)+originalGap c i := by
    fin_cases i
    · change burnolRieszStatePositiveOuterRaw c (Real.exp h*x)=
        positionSource c (Real.exp h*x)+positionMean c
      exact sub_eq_iff_eq_add.mp (positionSource_eq_outer_sub_mean c (Real.exp h*x)).symm
    · rfl
  rw [split]
  ring

/-- The source current is the two actual R faces on the whole original finite band. -/
theorem actual_R_current (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (member : x∈Icc p q) : sourceCurrent c i x=actedRaw c i x := by
  have pos : 0<x := junctionPoint_bounds.1.trans_le member.1
  have weights (j : Fin 2) : ∀ᵐ s : ℝ ∂volume.restrict (Ioc p x),
      (![fun t : ℝ => (t : ℂ)^(c.value-1)*inputRaw c 0 t,
        fun t : ℝ => (t : ℂ)^(-c.value)*(F (C c)) t] j) s=weight c j s := by
    have read := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right member.2) (input_band_read c j)
    filter_upwards [read,ae_restrict_of_ae (input_read c j),ae_restrict_mem measurableSet_Ioc] with s band raw hs
    have larger : radius s=s := max_eq_right (by linarith [hs.1,junctionPoint_bounds.1])
    fin_cases j
    · simp only [Fin.mk_zero] at raw band
      change (s : ℂ)^(c.value-1)*inputRaw c 0 s=weight c 0 s
      rw [←raw,band]
      simp only [weight,Matrix.cons_val_zero,larger]
    · simp only [Fin.mk_one] at raw band
      change (s : ℂ)^(-c.value)*(F (C c)) s=weight c 1 s
      change (F (C c)) s=bandInput c 1 s at band
      rw [band]
      simp only [weight,Matrix.cons_val_one,Matrix.cons_val_zero,larger]
  fin_cases i
  · have paid := prefix_integrable c _ ((memLp_congr_ae (input_read c 0)).mp (Lp.memLp _)) q le_rfl
    have split := intervalIntegral.integral_add_adjacent_intervals
      (paid.mono_set (by rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)];exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le))
      (paid.mono_set (by rw [uIcc_of_le member.1,uIcc_of_le (by norm_num : (0 : ℝ)≤q)];exact Icc_subset_Icc junctionPoint_bounds.1.le member.2))
    have eqWeights : (fun s : ℝ => (s : ℂ)^(c.value-1)*inputRaw c 0 s)=ᵐ[volume.restrict (uIoc p x)] weight c 0 := by
      rw [uIoc_of_le member.1]
      exact weights 0
    have same := intervalIntegral.integral_congr_ae_restrict eqWeights
    change -2*(x : ℂ)^(-c.value)*(prefixSeed c+∫ s : ℝ in p..x,weight c 0 s)=prefixRaw c (inputRaw c 0) x
    unfold prefixRaw prefixSeed
    rw [abs_of_pos pos,←split,same]
  · have paid := burnolRadiusMellinWeight_integrableOn_tail p junctionPoint_bounds.1 c.value c.rightHalf (F (C c))
    have split := intervalIntegral.integral_Ioi_sub_Ioi paid member.1
    have eqWeights : (fun s : ℝ => (s : ℂ)^(-c.value)*(F (C c)) s)=ᵐ[volume.restrict (uIoc p x)] weight c 1 := by
      rw [uIoc_of_le member.1]
      exact weights 1
    have same := intervalIntegral.integral_congr_ae_restrict eqWeights
    change -2*(x : ℂ)^(c.value-1)*(tailSeed c-∫ s : ℝ in p..x,weight c 1 s)=outwardRaw c (F (C c)) x
    unfold outwardRaw tailSeed
    rw [abs_of_pos pos,←same,←split]
    ring

open OriginalWholeDebtRCorrectionActionSource
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- Its q value is constructed from the already-generated native endpoint and the original mean carrier. -/
def qCurrent (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : ℂ :=
  (-2*nativeAlpha c)*kernelInner (barC c) i+
    ![2*nativeAlpha c*Kernel.A (barC c),-2*nativeAlpha c*Kernel.beta (barC c)] i+
      regularRaw c i q

theorem actual_q_current (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    sourceCurrent c i q=qCurrent c i := by
  have leftRead : actedRaw c i=ᵐ[volume.restrict (Icc (p/2) q)] innerRaw c i := by
    filter_upwards [ae_restrict_of_ae (full_read c i),ae_restrict_of_ae (volume.ae_ne q),
      ae_restrict_mem measurableSet_Icc] with x source nz hx
    rw [source]
    have pos : 0<x := lt_of_lt_of_le (by linarith [junctionPoint_bounds.1]) hx.1
    have small : x<q := lt_of_le_of_ne hx.2 nz
    dsimp only [fullRaw,innerRaw,outsideRaw,regularRaw,burnolEvenRaw]
    have first : x∈symmetricInterval q := ⟨by linarith,small.le⟩
    have reverse : -x∈symmetricInterval q := ⟨by linarith,by linarith⟩
    rw [kernel_inner (barC c) i pos small.le,indicator_of_mem first,indicator_of_mem reverse]
    ring
  have rawC : ContinuousOn (actedRaw c i) (Icc (p/2) q) := fun x hx =>
    (acted_continuous c i (ne_of_gt (lt_of_lt_of_le (by linarith [junctionPoint_bounds.1]) hx.1))).continuousWithinAt
  have innerC : ContinuousOn (innerRaw c i) (Icc (p/2) q) := by
    intro x hx
    have pos : 0<x := lt_of_lt_of_le (by linarith [junctionPoint_bounds.1]) hx.1
    have even : ContinuousAt (burnolEvenRaw (nativeRaw c i)) x :=
      continuousAt_const.mul ((native_continuous c i pos.ne').add
        ((native_continuous c i (neg_ne_zero.mpr pos.ne')).comp continuousAt_neg))
    have regular : Continuous (regularRaw c i) := by
      have paid := burnolRadiusTruncatedFourierRaw_continuous (nativeFoot c (![1,0] i) : Hq)
      exact continuous_const.mul (paid.add (paid.comp continuous_neg))
    exact ((continuousAt_const.add even).add regular.continuousAt).continuousWithinAt
  have value := Measure.eqOn_Icc_of_ae_eq volume (by linarith [junctionPoint_bounds.2] : p/2≠q) leftRead rawC innerC
  rw [actual_R_current c i q ⟨junctionPoint_bounds.2.le,le_rfl⟩,value (x := q) (by constructor <;> linarith [junctionPoint_bounds.2,junctionPoint_bounds.1])]
  change (-2*nativeAlpha c)*kernelInner (barC c) i+nativeEndpoint c i+regularRaw c i q=_
  rw [actual_native_endpoints]
  rfl

def mixedCurrent (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x : ℂ)*(star (sourceProfile c 0 x)*sourceCurrent c 0 x-
    star (sourceProfile c 1 x)*sourceCurrent c 1 x)

def mixedMass (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (sourceProfile c 0 x)*sourceCurrent c 0 x+star (sourceProfile c 1 x)*sourceCurrent c 1 x

def mixedForcing (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (Kernel.A c)*(star (phi 0 x)*sourceCurrent c 0 x+star (phi 1 x)*sourceCurrent c 1 x)+
  star (Kernel.beta c)*(star (phi 1 x)*sourceCurrent c 0 x+star (phi 0 x)*sourceCurrent c 1 x)

def qFlux (c : BurnolCompletedMellinCoordinate) : ℂ :=
  (q : ℂ)*(-star (Kernel.A c)*qCurrent c 0-star (Kernel.beta c)*qCurrent c 1)

private theorem actual_q_flux (c : BurnolCompletedMellinCoordinate) : mixedCurrent c q=qFlux c := by
  unfold mixedCurrent
  rw [actual_q_current c 0,actual_q_current c 1]
  change (q : ℂ)*(star (positionSource c q)*qCurrent c 0-star (burnolRieszSingleFourierSourceRaw c q)*qCurrent c 1)=_
  rw [BandFiniteSourcePrice.position_source_trace]
  rfl

private theorem mixed_derivative (c : BurnolCompletedMellinCoordinate) (x : ℝ) (inside : p/2<x) :
    HasDerivAt (mixedCurrent c)
      (mixedForcing c x-(2*c.value-1)*mixedMass c x-
        2*(star (sourceProfile c 0 x)*bandInput c 0 x+star (sourceProfile c 1 x)*bandInput c 1 x)) x := by
  have pos : 0<x := lt_trans (by linarith [junctionPoint_bounds.1] : (0 : ℝ)<p/2) inside
  have fp := position_hasDerivAt c x pos
  have gp := sourceRaw_hasDerivAt c x pos.ne'
  have first := actual_source_current_derivative c 0 x inside
  have second := actual_source_current_derivative c 1 x inside
  have cast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using! Complex.ofRealCLM.hasDerivAt (x := x)
  convert! cast.mul ((fp.star.mul first).sub (gp.star.mul second)) using 1
  have fs := congrArg star (BandFiniteSourcePrice.position_source_euler c x pos)
  have gs := congrArg star (BandFiniteSourcePrice.fourier_source_euler c x pos.ne')
  simp only [star_add,star_mul,star_sub,star_star,star_div₀,star_ofNat,star_one,star_neg] at fs gs
  have realStar : star (x : ℂ)=(x : ℂ) := Complex.conj_ofReal x
  rw [realStar] at fs gs
  dsimp only [mixedCurrent,mixedForcing,mixedMass,sourceProfile,Matrix.cons_val_zero,Matrix.cons_val_one,
    Pi.sub_apply,Pi.mul_apply] at *
  field_simp [Complex.ofReal_ne_zero.mpr pos.ne']
  linear_combination -(sourceCurrent c 0 x)*fs+(sourceCurrent c 1 x)*gs

/-- The original complete forcing plus boundary price is consumed by the actual C/R mixed Green action. -/
theorem actual_finite_price_mixed_green (c : BurnolCompletedMellinCoordinate) :
    BandFiniteSourcePrice.finiteSourcePrice c h=
      2*(mixedCurrent c p-qFlux c+
        (∫ x : ℝ in p..q,mixedForcing c x)-(2*c.value-1)*(∫ x : ℝ in p..q,mixedMass c x))-
      4*(meanCharge c 0*(∫ x : ℝ in p..q,star (sourceProfile c 0 x))+
        meanCharge c 1*(∫ x : ℝ in p..q,star (sourceProfile c 1 x))) := by
  have regular (i : Fin 2) : ContinuousOn (sourceCurrent c i) (Icc p q) := by
    intro x member
    exact (actual_source_current_derivative c i x (by linarith [member.1,junctionPoint_bounds.1])).continuousAt.continuousWithinAt
  have profile (i : Fin 2) : ContinuousOn (sourceProfile c i) (Icc p q) :=
    fun x member => (source_profile_continuous c i (junctionPoint_bounds.1.trans_le member.1)).continuousWithinAt
  have dc : ContinuousOn (mixedCurrent c) (Icc p q) :=
    (Complex.continuous_ofReal.continuousOn.mul (((profile 0).star.mul (regular 0)).sub ((profile 1).star.mul (regular 1))))
  have force : ContinuousOn (mixedForcing c) (Icc p q) := by
    have p0 : ContinuousOn (phi 0) (Icc p q) := (BandFiniteSourcePrice.source_column_continuous 0).continuousOn
    have p1 : ContinuousOn (phi 1) (Icc p q) := (BandFiniteSourcePrice.source_column_continuous 1).continuousOn
    have first := ((p0.star.mul (regular 0)).add (p1.star.mul (regular 1))).const_mul (star (Kernel.A c))
    have second := ((p1.star.mul (regular 0)).add (p0.star.mul (regular 1))).const_mul (star (Kernel.beta c))
    exact first.add second
  have mass : ContinuousOn (mixedMass c) (Icc p q) := ((profile 0).star.mul (regular 0)).add ((profile 1).star.mul (regular 1))
  have input (i : Fin 2) : ContinuousOn (bandInput c i) (Icc p q) := by
    intro x member
    have rawAt : ContinuousAt (sourceProfile c i) (Real.exp h*x) :=
      source_profile_continuous c i (mul_pos (Real.exp_pos h) (junctionPoint_bounds.1.trans_le member.1))
    have scale : ContinuousAt (fun y : ℝ => Real.exp h*y) x := continuousAt_const.mul continuousAt_id
    have moved : ContinuousAt (fun y : ℝ => sourceProfile c i (Real.exp h*y)) x :=
      ContinuousAt.comp (f := fun y : ℝ => Real.exp h*y) rawAt scale
    exact (continuousAt_const.add (continuousAt_const.mul moved)).continuousWithinAt
  have products := ((profile 0).star.mul (input 0)).add ((profile 1).star.mul (input 1))
  have fint : IntervalIntegrable (mixedForcing c) volume p q := ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le junctionPoint_bounds.2.le] using force)
  have mint : IntervalIntegrable (mixedMass c) volume p q := ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le junctionPoint_bounds.2.le] using mass)
  have pint : IntervalIntegrable (fun x : ℝ => star (sourceProfile c 0 x)*bandInput c 0 x+star (sourceProfile c 1 x)*bandInput c 1 x) volume p q := ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le junctionPoint_bounds.2.le] using! products)
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le junctionPoint_bounds.2.le dc
    (fun x member => mixed_derivative c x (by linarith [member.1,junctionPoint_bounds.1]))
    ((fint.sub (mint.const_mul _)).sub (pint.const_mul 2))
  rw [intervalIntegral.integral_sub (fint.sub (mint.const_mul _)) (pint.const_mul _),
    intervalIntegral.integral_sub fint (mint.const_mul _),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at generated
  rw [actual_q_flux] at generated
  have same : (fun x : ℝ => star (sourceProfile c 0 x)*bandInput c 0 x+
      star (sourceProfile c 1 x)*bandInput c 1 x)=fun x =>
      (Real.exp (h/2) : ℂ)/2*sourceProduct c h x+
        meanCharge c 0*star (sourceProfile c 0 x)+meanCharge c 1*star (sourceProfile c 1 x) := by
    funext x
    unfold bandInput sourceProduct sourceProfile
    dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  have sourceInt : IntervalIntegrable (sourceProduct c h) volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le junctionPoint_bounds.2.le]
    exact fun x hx => (sourceProduct_continuousAt c h (junctionPoint_bounds.1.trans_le hx.1)).continuousWithinAt
  have profilesInt (i : Fin 2) : IntervalIntegrable (fun x : ℝ => star (sourceProfile c i x)) volume p q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le junctionPoint_bounds.2.le] using (profile i).star
  rw [same,intervalIntegral.integral_add ((sourceInt.const_mul _).add ((profilesInt 0).const_mul _)) ((profilesInt 1).const_mul _),
    intervalIntegral.integral_add (sourceInt.const_mul _) ((profilesInt 0).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at generated
  rw [←BandFiniteSourcePrice.source_pair_finite_price c h junctionShift_pos.le]
  change (2 : ℂ)*(Real.exp (h/2) : ℂ)*(∫ x : ℝ in p..q,sourceProduct c h x)=_
  linear_combination -2*generated

end OriginalWholeDebtRMixedGreenSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
