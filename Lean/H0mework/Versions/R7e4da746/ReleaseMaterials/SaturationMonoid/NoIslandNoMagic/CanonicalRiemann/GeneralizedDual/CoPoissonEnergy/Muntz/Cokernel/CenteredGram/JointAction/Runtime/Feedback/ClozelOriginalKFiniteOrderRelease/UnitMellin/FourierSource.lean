import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitRegularity.GeneratorCounting
import H0mework.Versions.R7e4da746.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Reverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalUnitMellinSource.Fourier
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
local notation "q"=>(1/4:ℝ)
local notation "H"=>burnolUnitCountingPrimitiveL2
local notation "CF"=>ConstantForward.value
local notation "F"=>fourierL2
private theorem sqrtFour : Real.sqrt (4:ℝ)=2:=by
  rw [show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num:(0:ℝ)≤2)]

private theorem resolvent_dilation (z : ℂ) (h : ℝ) (f : BurnolL2) :
    burnolMultiplicativeDilation h (burnolDirectRightResolvent z f)=
      burnolDirectRightResolvent z (burnolMultiplicativeDilation h f) := by
  unfold burnolDirectRightResolvent burnolDirectRightResolventIntegrand
  rw [map_neg]
  have moved:= (LinearIsometry.integral_comp_comm
    (burnolMultiplicativeDilation h).toLinearIsometry
    (fun t : ℝ=>positiveMellinQuarterRightResolventWeight z t •
      burnolMultiplicativeDilation (-t/2) f) (μ:=volume.restrict (Ioi 0))).symm
  change burnolMultiplicativeDilation h
    (∫ t : ℝ in Ioi 0,positiveMellinQuarterRightResolventWeight z t •
      burnolMultiplicativeDilation (-t/2) f)=
      ∫ t : ℝ in Ioi 0,burnolMultiplicativeDilation h
        (positiveMellinQuarterRightResolventWeight z t •
          burnolMultiplicativeDilation (-t/2) f) at moved
  rw [moved]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul,burnolMultiplicativeDilation_add,burnolMultiplicativeDilation_add,add_comm]

private theorem actual_forward_seed :
    CF=F (burnolTateReciprocalL2 ConstantDual.value) := by
  have source:=congrArg F ConstantFourier.original_square
  have even:reflectL2 CF=CF:=by
    apply fourierL2.injective
    have de:reflectL2 ConstantDual.value=ConstantDual.value:=
      burnolReflectL2_eq_of_even_raw _ _ ConstantDual.value_coeFn (fun x=>by simp [ConstantDual.sawtoothRaw,abs_neg])
    rw [fourierL2_reflectL2_commute,ConstantFourier.original_square,←burnolTateReciprocal_reflect,de]
  rw [fourierL2_fourierL2,even] at source
  exact source

private def g : BurnolL2 := (2:ℂ) • burnolMultiplicativeDilation (Real.log 4) H
private def h : BurnolL2 := (4:ℂ) • CF

private theorem actual_independent_seed :
    h=(2:ℂ) • burnolMultiplicativeDilation (Real.log 4) (F H) := by
  rw [h,actual_forward_seed,ConstantFourier.reciprocal_value]
  unfold burnolSourceScalePrimitive
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  rw [map_smul,fourierL2_burnolMultiplicativeDilation]
  have logarithm : -Real.log q=Real.log 4 := by
    rw [show q=(4:ℝ)⁻¹ by norm_num,Real.log_inv,neg_neg]
  rw [logarithm]
  have squareRoot : Real.sqrt q=1/2 := by
    rw [Real.sqrt_div (by norm_num),Real.sqrt_one]
    norm_num [sqrtFour]
  rw [squareRoot,smul_smul]
  congr 1
  norm_num

private theorem actual_complete_poisson_pair :
    g+h=(-1/2:ℂ) • burnolDirectRightResolvent (1/2) h := by
  have original:=congrArg (fun value : BurnolL2=>(2:ℂ) •
    burnolMultiplicativeDilation (Real.log 4) value)
    burnolCountingPrimitiveFourierPair_eq_resolvent
  rw [map_add,map_smul,resolvent_dilation] at original
  unfold g
  rw [actual_independent_seed,burnolDirectRightResolvent_smul]
  simpa only [smul_add,smul_smul,mul_comm] using original

/-- Both original primitive contacts are paid by one complete Poisson source pair. -/
theorem actual_shared_forcing_payment (c : BurnolCompletedMellinCoordinate) :
    h+(c.value/2) • burnolDirectRightResolvent (c.value/2) h=
      -g-((c.value-1)/2) • burnolDirectRightResolvent (c.value/2) g := by
  have positive : 1/4<(c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have identity:=burnolDirectRightResolvent_identity (c.value/2) (1/2)
    positive (by norm_num) h
  let R : BurnolL2→L[ℂ] BurnolL2 := burnolDirectRightResolventCLM c
  have sumRead : burnolDirectRightResolvent (c.value/2) (g+h)=
      burnolDirectRightResolvent (c.value/2) g+
        burnolDirectRightResolvent (c.value/2) h := R.map_add g h
  have second:=congrArg (burnolDirectRightResolvent (c.value/2)) actual_complete_poisson_pair
  rw [sumRead,burnolDirectRightResolvent_smul] at second
  have weighted:=congrArg (fun value : BurnolL2=>((c.value-1)/2) • value) second
  have combined : ((c.value-1)/2) •
      (burnolDirectRightResolvent (c.value/2) g+burnolDirectRightResolvent (c.value/2) h)=
        -(1/2:ℂ) • (burnolDirectRightResolvent (c.value/2) h-
          burnolDirectRightResolvent (1/2) h) := by
    rw [identity]
    rw [smul_smul] at weighted ⊢
    have scalar : ((c.value-1)/2)*(-1/2:ℂ)=
        -(1/2:ℂ)*(c.value/2-1/2) := by ring
    rwa [scalar] at weighted
  rw [smul_add,smul_sub] at combined
  have price:=eq_sub_of_add_eq combined
  calc
    h+(c.value/2) • burnolDirectRightResolvent (c.value/2) h=
      -g+(g+h)+(c.value/2) • burnolDirectRightResolvent (c.value/2) h := by module
    _=-g+(-1/2:ℂ) • burnolDirectRightResolvent (1/2) h+
      (c.value/2) • burnolDirectRightResolvent (c.value/2) h := by
        rw [actual_complete_poisson_pair]
    _=_ := by rw [price];module

private theorem actual_unit_quarter_scale (c : BurnolCompletedMellinCoordinate) :
    burnolUnitTailResponse c q=
      (q:ℂ)^(1-c.value) •
        (-g-((c.value-1)/2) • burnolDirectRightResolvent (c.value/2) g) := by
  have movedRadius : (1:ℝ)*Real.exp (-(Real.log 4))=q := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  have source:=burnolUnitTailResponse_radius_dilation c 1
    (by norm_num) (by norm_num) (Real.log 4) (by rw [movedRadius];norm_num)
  rw [movedRadius,burnolUnitTailResponse_one_eq_fixedResolvent,map_sub,map_neg,map_smul,
    resolvent_dilation] at source
  have coefficient : (q:ℂ)^(1-c.value)*(2:ℂ)*
      fullMellinTranslationCharacter (c.value) (Real.log 4)=1 := by
    unfold fullMellinTranslationCharacter
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (q:ℂ)≠0),
      show Complex.log (q:ℂ)=-(Real.log 4:ℂ) by
        rw [← Complex.ofReal_log (by norm_num : (0:ℝ)≤q),show q=(4:ℝ)⁻¹ by norm_num,Real.log_inv,Complex.ofReal_neg]]
    rw [mul_comm _ (2:ℂ),mul_assoc,← Complex.exp_add]
    have exponent : (-(Real.log 4:ℂ))*(1-c.value)+
        (1/2-c.value)*(Real.log 4:ℂ)=-(Real.log 4:ℂ)/2 := by ring
    have expRead : Complex.exp (-(Real.log 4:ℂ)/2)=(Real.exp (-Real.log 4/2):ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      rfl
    rw [exponent,expRead,show -Real.log 4/2=-(Real.log 4/2) by ring,
      Real.exp_neg,Real.exp_half,Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num [sqrtFour]
  have scaled:=congrArg (fun value : BurnolL2=>((q:ℂ)^(1-c.value)*(2:ℂ)) • value) source
  change ((q:ℂ)^(1-c.value)*(2:ℂ)) •
    (-burnolMultiplicativeDilation (Real.log 4) H-
      ((c.value-1)/2) • burnolDirectRightResolvent (c.value/2)
        (burnolMultiplicativeDilation (Real.log 4) H))=
      _ at scaled
  rw [smul_smul,coefficient,one_smul] at scaled
  change ((q:ℂ)^(1-c.value)*(2:ℂ)) •
    (-burnolMultiplicativeDilation (Real.log 4) H-
      ((c.value-1)/2) • burnolDirectRightResolvent (c.value/2)
        (burnolMultiplicativeDilation (Real.log 4) H))=
      burnolUnitTailResponse c q at scaled
  rw [← scaled]
  simp only [g,burnolDirectRightResolvent_smul,smul_sub,smul_neg,smul_smul]
  module


/-- Both original Poisson sides pay the full Fourier unit; no zero assumption is varied. -/
theorem actual_unit_quarter_fourier (c:BurnolCompletedMellinCoordinate):
    F (burnolUnitTailResponse c q)=
      (q:ℂ)^(-c.value) • burnolTateReciprocalL2
        (ConstantDual.value+(c.value/2) • burnolDirectRightResolvent (c.value/2) ConstantDual.value):=by
  have unit:burnolUnitTailResponse c q=(q:ℂ)^(1-c.value) •
      (h+(c.value/2) • burnolDirectRightResolvent (c.value/2) h):=by
    rw [actual_shared_forcing_payment,actual_unit_quarter_scale]
  have right:1/4<(c.value/2).re:=by rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have ft_h:F h=(4:ℂ) • burnolTateReciprocalL2 ConstantDual.value:=by
    rw [h,map_smul,ConstantFourier.original_square]
  rw [unit,map_smul,map_add,map_smul,FiniteMobiusResolventFlux.fourier_R _ right,
    ft_h,FiniteMobiusResolventFlux.Rplus_tate _ right,map_smul,burnolTateReciprocalL2_involutive,
    burnolDirectRightResolvent_smul,map_smul,map_add,map_smul]
  have factor:(q:ℂ)^(1-c.value)*(4:ℂ)=(q:ℂ)^(-c.value):=by
    have power:=Complex.cpow_add (-c.value) 1 (by norm_num:(q:ℂ)≠0)
    rw [Complex.cpow_one,show -c.value+1=1-c.value by ring] at power
    rw [power]
    norm_num
    ring
  calc
    _=((q:ℂ)^(1-c.value)*(4:ℂ)) •
      (burnolTateReciprocalL2 ConstantDual.value+(c.value/2) •
        burnolTateReciprocalL2 (burnolDirectRightResolvent (c.value/2) ConstantDual.value)):=by module
    _=_:=by rw [factor]

end OriginalUnitMellinSource.Fourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
