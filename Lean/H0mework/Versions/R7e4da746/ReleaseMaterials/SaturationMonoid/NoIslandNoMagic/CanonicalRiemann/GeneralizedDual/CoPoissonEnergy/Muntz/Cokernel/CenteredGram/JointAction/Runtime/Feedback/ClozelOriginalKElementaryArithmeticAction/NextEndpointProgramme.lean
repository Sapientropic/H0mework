import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPriceConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.EtaNextSourcePrice
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalNextEndpointProgramme
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKElementaryArithmeticAction OriginalKExteriorCoPoissonAction
open OriginalKFiniteOrderRelease OriginalFullLossRAction OriginalReverseCoreJumpMean
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "F" => fourierL2
local notation "T" => burnolTateReciprocalL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

open private gamma conjugate_zero unitCurrent FT boxProgram unitTailProgram
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope SB_regular
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private pair_raw box_price tail_price dilation_raw unitCurrent_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
open private response_prices extension_price fourier_extension_price
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPrice
open private core_reverse_even coefficient
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPriceConsumer
open private extension_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

private def other : Fin 2→Fin 2 := ![1,0]
private def endpointColumn : Fin 2→BurnolL2 :=
  ![F (E (Response.u:Hq))-E (Response.v:Hq),E (Response.u:Hq)-F (E (Response.v:Hq))]

def endpointRaw (i:Fin 2) (x:ℝ) : ℂ :=
  ![Constructor.fourierRaw (Response.u:Hq) x-(symmetricInterval q).indicator (Response.v:Hq) x,
    (symmetricInterval q).indicator (Response.u:Hq) x-Constructor.fourierRaw (Response.v:Hq) x] i

def reciprocalEndpointRaw (i:Fin 2) : ℝ→ℂ := burnolTateReciprocalRaw (endpointRaw (other i))

private theorem endpoint_raw (i:Fin 2) :
    (endpointColumn i:ℝ→ℂ)=ᵐ[volume] endpointRaw i := by
  have fu:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw (Response.u:Hq)
  have fv:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw (Response.v:Hq)
  change (F (E (Response.u:Hq)):ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw (Response.u:Hq) at fu
  change (F (E (Response.v:Hq)):ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw (Response.v:Hq) at fv
  fin_cases i
  · filter_upwards [Lp.coeFn_sub (F (E (Response.u:Hq))) (E (Response.v:Hq)),fu,
      burnolQuarterZeroExtension_coe (Response.v:Hq)] with x difference left right
    change (F (E (Response.u:Hq))-E (Response.v:Hq):BurnolL2) x=_
    rw [difference,Pi.sub_apply,left,right]
    rfl
  · filter_upwards [Lp.coeFn_sub (E (Response.u:Hq)) (F (E (Response.v:Hq))),
      burnolQuarterZeroExtension_coe (Response.u:Hq),fv] with x difference left right
    change (E (Response.u:Hq)-F (E (Response.v:Hq)):BurnolL2) x=_
    rw [difference,Pi.sub_apply,left,right]
    rfl

private theorem endpoint_fourier (i:Fin 2) : F (endpointColumn i)=endpointColumn (other i) := by
  have u:=extension_even (Response.u:Hq) Response.u_reflection
  have v:=extension_even (Response.v:Hq) Response.v_reflection
  fin_cases i
  · change F (F (E (Response.u:Hq))-E (Response.v:Hq))=E (Response.u:Hq)-F (E (Response.v:Hq))
    rw [map_sub,fourierL2_fourierL2,u]
  · change F (E (Response.u:Hq)-F (E (Response.v:Hq)))=F (E (Response.u:Hq))-E (Response.v:Hq)
    rw [map_sub,fourierL2_fourierL2,v]

private theorem reciprocal_endpoint_raw (i:Fin 2) :
    (T (F (endpointColumn i)):ℝ→ℂ)=ᵐ[volume] reciprocalEndpointRaw i := by
  have raw:((F (endpointColumn i)):ℝ→ℂ)=ᵐ[volume] endpointRaw (other i) := by
    rw [endpoint_fourier]
    exact endpoint_raw _
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (F (endpointColumn i)))
    ((Lp.memLp (F (endpointColumn i))).ae_eq raw) raw
  exact (burnolTateReciprocalL2_coeFn (F (endpointColumn i))).trans pulled

private theorem FT_price (i:Fin 2) (value:BurnolL2) :
    inner ℂ (endpointColumn i) (FT value)=inner ℂ (T (F (endpointColumn i))) value := by
  have twice:F (F (endpointColumn i))=endpointColumn i := by
    rw [endpoint_fourier,endpoint_fourier]
    fin_cases i <;> rfl
  have actual:=fourierL2.inner_map_map (F (endpointColumn i)) (T value)
  rw [twice] at actual
  exact actual.trans (OriginalRieszFiniteSynthesis.tate_pairing _ _).symm

def boundaryPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) (raw:ℝ→ℂ) : ℂ :=
  pairedMellinTranslationCharacter c.value h*rawPair (endpointRaw i) raw-
    (1/2:ℂ)*(rawPair (endpointRaw i) (dilationProfile h raw)+
      rawPair (endpointRaw i) (dilationProfile (-h) raw))

def lossPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) (raw:ℝ→ℂ) : ℂ :=
  boxPrice (endpointRaw i) q (q*Real.exp h) (SBWeight c h) (SBSlope c h) raw+
    centeringMean c h 1*rawPair (endpointRaw i) raw-
    (boxPrice (reciprocalEndpointRaw i) (bandLower h) 4 (positiveWeight c h 0)
        (deriv (positiveWeight c h 0)) raw+
      centeringMean c h 0*tailPrice (reciprocalEndpointRaw i) raw)

/-- Both endpoint source prices execute the original complete finite and infinite R-core programme. -/
def currentPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) : ℂ :=
  (2*gamma c)*boundaryPrice c h i (elementaryReverseRaw (barC c))-
    (2*gamma (barC c))*boundaryPrice c h i (elementaryReverseRaw c)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ))*lossPrice c h i (unitCurrentProfile c)

/-- The complete original price now reads only its actual scalar source programmes. -/
def programmePrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  let a:=coefficient c
  let mean0:=OriginalCoreUnitProgramme.currentUnitPrice c h 0
  let mean1:=OriginalCoreUnitProgramme.currentUnitPrice c h 1
  let meanCore:=OriginalCoreUnitProgramme.coreUnitPrice c h 0
  (-star (Kernel.A c)*(currentPrice c h 0+(1-c.value)*mean0)-
    star (Kernel.beta c)*(currentPrice c h 1+c.value*mean1)+
    (c.value*star (gamma c)*mean0+2*a*star (gamma c)*meanCore-
      2*a*OriginalEtaNextSource.primitiveInputPrice c h-
      (2*c.value-1)*OriginalEtaNextSource.correctionCurrentPrice c h)-
    2*a*coreJumpPrice c h-(2*c.value-1)*currentJumpPrice c h+
    2*a*OriginalEtaNextSource.countedDifferencePrice c h)/(2*a)

private theorem boundary_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2)
    (value:BurnolL2) (raw:ℝ→ℂ) (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ (endpointColumn i) (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h value)=
      boundaryPrice c h i raw := by
  unfold OriginalKFixedBoundarySourceFibre.finiteBoundaryAction boundaryPrice
  rw [inner_sub_right,inner_smul_right,inner_smul_right,inner_add_right]
  rw [pair_raw _ _ _ _ (endpoint_raw i) actual,
    pair_raw _ _ _ _ (endpoint_raw i) (dilation_raw h value raw actual),
    pair_raw _ _ _ _ (endpoint_raw i) (dilation_raw (-h) value raw actual)]

private theorem loss_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2)
    (value:BurnolL2) (raw:ℝ→ℂ) (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ (endpointColumn i) (boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) value+
      centeringMean c h 1 • value-FT (boxProgram (bandLower h) 4 (positiveWeight c h 0)
        (deriv (positiveWeight c h 0)) value+centeringMean c h 0 • unitTailProgram value))=
      lossPrice c h i raw := by
  have regular:ContinuousOn (deriv (positiveWeight c h 0)) (Icc (bandLower h) 4) :=
    (positiveWeight_deriv_continuousOn c h 0).mono (fun _ inside=>(bandLower_pos h).trans_le inside.1)
  unfold lossPrice
  rw [inner_sub_right,inner_add_right,inner_smul_right,FT_price,inner_add_right,inner_smul_right]
  rw [box_price _ value _ raw (endpoint_raw i) actual _ _ _ _ (by norm_num) (SB_regular c h).continuousOn,
    pair_raw _ value _ raw (endpoint_raw i) actual,
    box_price _ value _ raw (reciprocal_endpoint_raw i) actual _ _ _ _ (bandLower_pos h) regular,
    tail_price _ value _ raw (reciprocal_endpoint_raw i) actual]

private theorem current_endpoint_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (i:Fin 2) :
    inner ℂ (endpointColumn i) (completeCoreRCurrent c zero h)=currentPrice c h i := by
  unfold completeCoreRCurrent currentPrice
  rw [inner_sub_right,inner_sub_right,inner_smul_right,inner_smul_right,inner_smul_right,
    boundary_price c h i _ _ (elementary_reverse_raw (barC c) (conjugate_zero c zero)),
    boundary_price c h i _ _ (elementary_reverse_raw c zero),loss_price c h i _ _ (unitCurrent_raw c zero)]

private theorem endpoint_pair (value:BurnolL2) :
    inner ℂ (endpointColumn 0) value=inner ℂ Response.eta (burnolAmbientMeanZeroSecondCorrection value) ∧
    inner ℂ (endpointColumn 1) value=inner ℂ Response.eta (burnolAmbientMeanZeroFirstCorrection value) := by
  simp only [endpointColumn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,inner_sub_left]
  rw [fourier_extension_price _ Response.u_reflection,extension_price _ Response.v_reflection,
    extension_price _ Response.u_reflection,fourier_extension_price _ Response.v_reflection]
  exact response_prices value

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h0" => Real.log stageZeroSonineQ
local notation "a" => coefficient c
local notation "v" => coreReverseSource c observation.mathlibZero h0
local notation "first" => GenericSourceStepBAction.firstNext (barC c) (F v)
local notation "second" => GenericSourceStepBAction.secondNext (barC c) (F v)

/-- The same actual original R update pays both B endpoints without dividing its source weight. -/
theorem original_next_endpoint_source :
    a*(q:ℂ)*(burnolMeanZeroFourierRaw first q+burnolMeanZeroFourierRaw first (-q))=currentPrice c h0 0 ∧
    a*(q:ℂ)*(burnolMeanZeroFourierRaw second q+burnolMeanZeroFourierRaw second (-q))=currentPrice c h0 1 := by
  have nn:0≤h0:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have update:=GenericSourceStepBAction.actual_forward_R_B c v (core_reverse_even c observation.mathlibZero h0 nn)
  have source:=OriginalFullLossRAction.original_core_R_update observation nontrivial half
  change a • burnolDirectRightResolventCLM c v=completeCoreRCurrent c observation.mathlibZero h0 at source
  have left:=current_endpoint_source c observation.mathlibZero h0 0
  have right:=current_endpoint_source c observation.mathlibZero h0 1
  rw [←source,inner_smul_right,(endpoint_pair _).1,update.2,
    OriginalCommonInverseForcing.InverseEuler.eta_endpoint_read] at left
  rw [←source,inner_smul_right,(endpoint_pair _).2,update.1,
    OriginalCommonInverseForcing.InverseEuler.eta_endpoint_read] at right
  exact ⟨by simpa only [mul_assoc] using left,by simpa only [mul_assoc] using right⟩

/-- Both endpoint calculations rewrite the same original source price at its original c and h. -/
theorem original_source_price :
    OriginalEtaNextSource.sourcePrice c observation.mathlibZero h0=programmePrice c h0 := by
  unfold OriginalEtaNextSource.sourcePrice programmePrice
  dsimp only
  rw [(original_next_endpoint_source observation nontrivial half).1,
    (original_next_endpoint_source observation nontrivial half).2]

theorem original_fixedResidual_programme :
    burnolPaFixedShiftResidual c observation.mathlibZero=programmePrice c h0 :=
  (OriginalEtaNextSource.original_fixedResidual_source_price observation nontrivial half).trans
    (original_source_price observation nontrivial half)

end OriginalNextEndpointProgramme
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
