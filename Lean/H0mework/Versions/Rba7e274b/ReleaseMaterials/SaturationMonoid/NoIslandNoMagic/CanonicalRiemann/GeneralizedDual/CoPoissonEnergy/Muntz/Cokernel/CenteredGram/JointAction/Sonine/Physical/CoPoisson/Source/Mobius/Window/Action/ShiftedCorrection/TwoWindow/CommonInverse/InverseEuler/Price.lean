import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Green
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex Filter FourierTransform MeasureTheory Set OriginalRieszSource
open scoped ENNReal InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "b" => burnolRieszSingleFourierSource

private theorem scalar_left (left right : BurnolQuarterMeanZeroCarrier) (scalar : ℂ) :
    inner ℂ (scalar • left) right=star scalar*inner ℂ left right :=
  inner_smul_left left right scalar
private theorem scalar_right (left right : BurnolQuarterMeanZeroCarrier) (scalar : ℂ) :
    inner ℂ left (scalar • right)=scalar*inner ℂ left right :=
  inner_smul_right left right scalar
private theorem quarter_scalar_left (left right : BurnolQuarterIntervalL2) (scalar : ℂ) :
    inner ℂ (scalar • left) right=star scalar*inner ℂ left right :=
  inner_smul_left left right scalar

private theorem phase_inner (frequency : ℝ) (state : BurnolQuarterIntervalL2) :
    inner ℂ (Constructor.compact (Constructor.phase frequency) (Constructor.phaseContinuous frequency)) state=
      Constructor.fourierRaw state (-frequency) := by
  rw [L2.inner_def]
  unfold Constructor.fourierRaw VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards [Constructor.compact_read (Constructor.phase frequency) (Constructor.phaseContinuous frequency)]
    with x read
  rw [read]
  simp [Constructor.phase,RCLike.inner_apply,innerₗ_apply_apply,Circle.smul_def,mul_comm]
private theorem constant_inner (state : BurnolQuarterIntervalL2) :
    inner ℂ (intervalConstant q) state=(1/2:ℂ)*burnolQuarterMeanCoefficient state := by
  unfold burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)]
  norm_num
  ring
private theorem fourier_constant_inner (state : BurnolQuarterIntervalL2) :
    inner ℂ (burnolTruncatedFourier (intervalConstant q)) state=
      (1/2:ℂ)*burnolQuarterMeanCoefficient (burnolTruncatedFourier state) := by
  have source:=congrArg (starRingEnd ℂ)
    (OriginalRieszSourceGreen.quarter_fourier_pairing_of_reflection state (intervalConstant q)
      (reflectRestricted_intervalConstant q))
  simp only [inner_conj_symm] at source
  rw [← source,constant_inner]

theorem endpointColumn_inner (endpoint : ℝ) (state : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (Constructor.endpointColumn endpoint) state=
      (q:ℂ)*burnolMeanZeroFourierRaw state (-endpoint) := by
  unfold Constructor.endpointColumn Constructor.zeroMean
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,inner_sub_left,quarter_scalar_left]
  rw [phase_inner,fourier_constant_inner]
  unfold burnolMeanZeroFourierRaw
  change _=(q:ℂ)*(Constructor.fourierRaw (state:BurnolQuarterIntervalL2) (-endpoint)-
    burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:BurnolQuarterIntervalL2)))
  norm_num [Complex.star_def]
  ring

theorem eta_endpoint_read (state : BurnolQuarterMeanZeroCarrier) :
    inner ℂ Response.eta state=(q:ℂ)*
      (burnolMeanZeroFourierRaw state q+burnolMeanZeroFourierRaw state (-q)) := by
  unfold Response.eta
  rw [inner_add_left,endpointColumn_inner,endpointColumn_inner,neg_neg]
  ring

theorem b_endpointReaction_read (coordinate : BurnolCompletedMellinCoordinate) (raw : ℝ→ℂ) :
    inner ℂ (b coordinate) (endpointReaction raw)=
      (q:ℂ)*star (burnolRieszReturnRaw coordinate q)*(raw q+raw (-q)) := by
  have plus : inner ℂ (b coordinate) (Constructor.endpointColumn q)=
      (q:ℂ)*star (burnolRieszReturnRaw coordinate q) := by
    rw [← inner_conj_symm,endpointColumn_inner]
    change star ((q:ℂ)*burnolRieszReturnRaw coordinate (-q))=_
    have endpoints : burnolRieszReturnRaw coordinate (-q)=burnolRieszReturnRaw coordinate q :=
      burnolRieszSingleFourierReturnRaw_endpoints coordinate
    rw [star_mul,endpoints]
    simp only [Complex.star_def,Complex.conj_ofReal]
    ring
  have minus : inner ℂ (b coordinate) (Constructor.endpointColumn (-q))=
      (q:ℂ)*star (burnolRieszReturnRaw coordinate q) := by
    rw [← inner_conj_symm,endpointColumn_inner,neg_neg]
    change star ((q:ℂ)*burnolRieszReturnRaw coordinate q)=_
    rw [star_mul]
    simp only [Complex.star_def,Complex.conj_ofReal]
    ring
  unfold endpointReaction
  rw [inner_add_right,scalar_right,scalar_right,plus,minus]
  ring

private theorem qualified_S_pairing_left (state field : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state:BurnolQuarterIntervalL2)=state) :
    inner ℂ state (S field)=inner ℂ (S state) field := by
  have paired:=congrArg (starRingEnd ℂ)
    (OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection field state even)
  simpa only [inner_conj_symm] using paired

private theorem paired_green_contact (coordinate : BurnolCompletedMellinCoordinate)
    (X Y Cb Cp EX EY ECp : BurnolQuarterMeanZeroCarrier) (rawX rawY : ℝ→ℂ)
    (first : X-S Y=Cb) (second : Y-S X=-Cp)
    (eulerSecond : EY+S EX=endpointReaction rawX-ECp)
    (bGreen : inner ℂ (Euler.sourceEuler coordinate) Y+inner ℂ (b coordinate) EY=
      (q:ℂ)*star (Kernel.beta coordinate)*(rawY q+rawY (-q)))
    (rGreen : inner ℂ (Constructor.returnEuler coordinate) X+inner ℂ (Constructor.returnState coordinate) EX=
      (q:ℂ)*star (burnolRieszReturnRaw coordinate q)*(rawX q+rawX (-q))) :
    (q:ℂ)*star (Kernel.beta coordinate)*(rawY q+rawY (-q))=
      -star (lambda coordinate)*inner ℂ (b coordinate) Cp-
      star (Kernel.A coordinate)*inner ℂ Response.u Cp+
      star (Kernel.beta coordinate)*inner ℂ Response.u Cb-inner ℂ (b coordinate) ECp := by
  have pairB:=qualified_S_pairing_left (b coordinate) X
    (burnolRieszSingleFourierSource_reflection_fixed coordinate)
  have pairEX:=qualified_S_pairing_left (b coordinate) EX
    (burnolRieszSingleFourierSource_reflection_fixed coordinate)
  have pairUX:=qualified_S_pairing_left Response.u X Response.u_reflection
  have pairUY:=qualified_S_pairing_left Response.u Y Response.u_reflection
  have bSecond:=congrArg (fun z:BurnolQuarterMeanZeroCarrier=>inner ℂ (b coordinate) z) second
  rw [inner_sub_right,inner_neg_right,pairB] at bSecond
  change inner ℂ (b coordinate) Y-inner ℂ (Constructor.returnState coordinate) X=
    -inner ℂ (b coordinate) Cp at bSecond
  have uSecond:=congrArg (fun z:BurnolQuarterMeanZeroCarrier=>inner ℂ Response.u z) second
  rw [inner_sub_right,inner_neg_right,pairUX] at uSecond
  change inner ℂ Response.u Y-inner ℂ Response.v X=-inner ℂ Response.u Cp at uSecond
  have uFirst:=congrArg (fun z:BurnolQuarterMeanZeroCarrier=>inner ℂ Response.u z) first
  rw [inner_sub_right,pairUY] at uFirst
  change inner ℂ Response.u X-inner ℂ Response.v Y=inner ℂ Response.u Cb at uFirst
  have responseCross : inner ℂ Response.v Y-inner ℂ Response.u X=-inner ℂ Response.u Cb := by
    linear_combination -uFirst
  have eSource:=congrArg (fun z:BurnolQuarterMeanZeroCarrier=>inner ℂ (b coordinate) z) eulerSecond
  rw [inner_add_right,inner_sub_right,pairEX,b_endpointReaction_read] at eSource
  change inner ℂ (b coordinate) EY+inner ℂ (Constructor.returnState coordinate) EX=
    (q:ℂ)*star (burnolRieszReturnRaw coordinate q)*(rawX q+rawX (-q))-inner ℂ (b coordinate) ECp at eSource
  have bEuler : Euler.sourceEuler coordinate=lambda coordinate • b coordinate+
      Kernel.A coordinate • Response.u-Kernel.beta coordinate • Response.v := Euler.sourceEuler_eq coordinate
  have rEuler : Constructor.returnEuler coordinate=(-lambda coordinate) • Constructor.returnState coordinate-
      Kernel.A coordinate • Response.v+Kernel.beta coordinate • Response.u := Euler.returnEuler_eq coordinate
  rw [bEuler] at bGreen
  rw [rEuler] at rGreen
  simp only [inner_add_left,inner_sub_left,scalar_left,star_neg] at bGreen rGreen
  have total : star (lambda coordinate)*
        (inner ℂ (b coordinate) Y-inner ℂ (Constructor.returnState coordinate) X)+
      star (Kernel.A coordinate)*(inner ℂ Response.u Y-inner ℂ Response.v X)-
      star (Kernel.beta coordinate)*(inner ℂ Response.v Y-inner ℂ Response.u X)+
      (inner ℂ (b coordinate) EY+inner ℂ (Constructor.returnState coordinate) EX)=
      (q:ℂ)*star (Kernel.beta coordinate)*(rawY q+rawY (-q))+
      (q:ℂ)*star (burnolRieszReturnRaw coordinate q)*(rawX q+rawX (-q)) := by
    linear_combination bGreen+rGreen
  rw [bSecond,uSecond,responseCross,eSource] at total
  linear_combination -total

def betaForcingPrice (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) : ℂ :=
  -coupling coordinate*inner ℂ (b coordinate) (cotestColumn scale (pBand coordinate h leg))-
  star (Kernel.A coordinate)*inner ℂ Response.u (cotestColumn scale (pBand coordinate h leg))+
  star (Kernel.beta coordinate)*inner ℂ Response.u (cotestColumn scale (bBand coordinate h leg))-
  inner ℂ (b coordinate) (bandEndpoint h scale (pLeg coordinate leg))+
  inner ℂ (b coordinate) (forcePColumn coordinate h scale leg)+
  star (Kernel.beta coordinate)*(q:ℂ)*
    (pCotestRaw coordinate h scale leg q+pCotestRaw coordinate h scale leg (-q))

private theorem beta_price_from_contact (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) (nonnegative : 0≤h)
    (X ECp : BurnolQuarterMeanZeroCarrier) (rawY : ℝ→ℂ)
    (profile : ∀ x:ℝ,rawY x=burnolMeanZeroFourierRaw X x-pCotestRaw coordinate h scale leg x)
    (sameEuler : ECp=pCotestEuler coordinate h scale leg)
    (contact : (q:ℂ)*star (Kernel.beta coordinate)*(rawY q+rawY (-q))=
      -star (lambda coordinate)*inner ℂ (b coordinate) (cotestColumn scale (pBand coordinate h leg))-
      star (Kernel.A coordinate)*inner ℂ Response.u (cotestColumn scale (pBand coordinate h leg))+
      star (Kernel.beta coordinate)*inner ℂ Response.u (cotestColumn scale (bBand coordinate h leg))-
      inner ℂ (b coordinate) ECp) :
    star (Kernel.beta coordinate)*inner ℂ Response.eta X=betaForcingPrice coordinate h scale leg := by
  have eta:=eta_endpoint_read X
  have qprofile:=profile q
  have minusProfile:=profile (-q)
  have etaValue : inner ℂ Response.eta X=(q:ℂ)*
      (rawY q+rawY (-q)+pCotestRaw coordinate h scale leg q+pCotestRaw coordinate h scale leg (-q)) := by
    linear_combination eta-(q:ℂ)*qprofile-(q:ℂ)*minusProfile
  have sourceP:=congrArg (fun z:BurnolQuarterMeanZeroCarrier=>inner ℂ (b coordinate) z)
    (source_p_cotest_action coordinate h scale leg nonnegative)
  simp only [inner_add_right,inner_sub_right,scalar_right,neg_mul] at sourceP
  rw [sameEuler] at contact
  have sourceCoupling : star (lambda coordinate)+lambda coordinate=coupling coordinate := by
    unfold lambda coupling
    simp only [star_sub,star_star,star_div₀,star_one,star_ofNat]
    ring
  unfold betaForcingPrice
  rw [← sourceCoupling]
  linear_combination star (Kernel.beta coordinate)*etaValue+contact-sourceP

theorem actual_beta_forcing_read (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    star (Kernel.beta coordinate)*inner ℂ Response.eta (inverseCotest coordinate h).1=
      betaForcingPrice coordinate h (-h/2) (h/2) ∧
    star (Kernel.beta coordinate)*inner ℂ Response.eta (inverseCotest coordinate h).2=
      betaForcingPrice coordinate h (h/2) (-h/2) := by
  obtain ⟨lowerX,lowerY,upperX,upperY⟩:=actual_inverse_profiles coordinate h nonnegative
  obtain ⟨lowerB,lowerP,upperB,upperP⟩:=actual_inverse_pair coordinate h
  obtain ⟨_,lowerE,_,upperE⟩:=actual_two_euler_actions coordinate h nonnegative
  have lowerBG:=source_interval_cotest_green coordinate _ _ _ (yProfile_continuous coordinate h).1
    (actual_derivatives_continuous coordinate h).2.1 (fun x=>(yProfile_hasDerivAt coordinate h x).1) lowerY
  have lowerRG:=return_interval_cotest_green coordinate _ _ _ (xProfile_continuous coordinate h).1
    (actual_derivatives_continuous coordinate h).1 (fun x=>(xProfile_hasDerivAt coordinate h x).1) lowerX
  have upperBG:=source_interval_cotest_green coordinate _ _ _ (yProfile_continuous coordinate h).2
    (actual_derivatives_continuous coordinate h).2.2.2 (fun x=>(yProfile_hasDerivAt coordinate h x).2) upperY
  have upperRG:=return_interval_cotest_green coordinate _ _ _ (xProfile_continuous coordinate h).2
    (actual_derivatives_continuous coordinate h).2.2.1 (fun x=>(xProfile_hasDerivAt coordinate h x).2) upperX
  have lower:=paired_green_contact coordinate _ _ _ _ _ _ _ _ _ lowerB lowerP lowerE lowerBG lowerRG
  have upper:=paired_green_contact coordinate _ _ _ _ _ _ _ _ _ upperB upperP upperE upperBG upperRG
  constructor
  · exact beta_price_from_contact coordinate h (-h/2) (h/2) nonnegative _ _ _ (fun _=>rfl) rfl lower
  · exact beta_price_from_contact coordinate h (h/2) (-h/2) nonnegative _ _ _ (fun _=>rfl) rfl upper

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
