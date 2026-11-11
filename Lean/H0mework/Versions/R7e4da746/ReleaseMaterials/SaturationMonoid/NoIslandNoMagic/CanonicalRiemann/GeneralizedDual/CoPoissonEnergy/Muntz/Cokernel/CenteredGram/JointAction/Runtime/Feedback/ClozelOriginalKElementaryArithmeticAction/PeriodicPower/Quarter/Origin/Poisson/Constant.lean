import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Lattice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Fourier
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Tail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Mass OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Lattice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Fourier
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Tail
open scoped Topology FourierTransform
local notation "q"=>(1/4:ℝ)

private theorem denominator_ne (c:BurnolCompletedMellinCoordinate):1-star c.value≠0:=by
  intro same
  have realPart:=congrArg Complex.re same
  simp only [sub_re,one_re,star_def,conj_re,zero_re] at realPart
  linarith [c.belowOne]

private theorem quarter_power (s:ℂ):(q:ℂ)^(-s)=(4:ℂ)^s:=by
  rw [Complex.cpow_def_of_ne_zero (by norm_num:(q:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num:(4:ℂ)≠0)]
  change Complex.exp (Complex.log ((q:ℝ):ℂ)*(-s))=Complex.exp (Complex.log ((4:ℝ):ℂ)*s)
  rw [←Complex.ofReal_log (by norm_num:(0:ℝ)≤q),←Complex.ofReal_log (by norm_num:(0:ℝ)≤4)]
  rw [Real.log_div (by norm_num:(1:ℝ)≠0) (by norm_num:(4:ℝ)≠0),Real.log_one]
  congr 1
  push_cast
  ring

private theorem power_normalization (c:BurnolCompletedMellinCoordinate) (N:ℕ) (pos:0<N):
    (4*N:ℂ)^(star c.value)*(N:ℂ)^(1-star c.value)/(1-star c.value)=
      2*(N:ℂ)*resolvedRaw c 0+(4*N:ℂ)*jumpCoefficient c/2:=by
  have positive:(0:ℝ)<N:=by exact_mod_cast pos
  have power:(4*N:ℂ)^(star c.value)*(N:ℂ)^(1-star c.value)=(q:ℂ)^(-star c.value)*(N:ℂ):=by
    rw [show (4*N:ℂ)=((4:ℝ):ℂ)*((N:ℝ):ℂ) by push_cast;rfl,
      Complex.mul_cpow_ofReal_nonneg (by norm_num:(0:ℝ)≤4) positive.le]
    simp only [Complex.ofReal_natCast,Complex.ofReal_ofNat]
    rw [mul_assoc,←Complex.cpow_add _ _ (show (N:ℂ)≠0 by exact_mod_cast pos.ne'),
      add_sub_cancel,Complex.cpow_one,←quarter_power]
  rw [power,actual_jump_coefficient]
  unfold OriginalKElementaryArithmeticAction.FreeParameter.Riesz.coefficient resolvedRaw
  norm_num only [abs_zero,max_eq_left (by norm_num:(0:ℝ)≤q)]
  field_simp [denominator_ne c]
  linear_combination 4*(N:ℂ)*(mul_inv_cancel₀ (denominator_ne c))

theorem actual_finite_poisson_bill (c:BurnolCompletedMellinCoordinate) (N:ℕ) (pos:0<N):
    aliasRaw c 0=FiniteForcing.coefficient (star c.value) N+(N:ℂ)^(-star c.value)+
      resolvedRaw c 0+jumpCoefficient c/2-(4*N:ℂ)^(-star c.value)*resolvedRaw c 0+
      (4*N:ℂ)^(1-star c.value)*(∑'k:ℤ,scaledAliasTerm c (4*N) k):=by
  let h:=Real.log (4*N:ℝ)
  have positive:(0:ℝ)<4*N:=by positivity
  have nn:0≤h:=Real.log_nonneg (by have n:1≤N:=pos;exact_mod_cast (show 1≤4*N by omega))
  have realExp:Real.exp h=4*N:=Real.exp_log positive
  have complexExp:(Real.exp h:ℂ)=(4*N:ℂ):=by rw [realExp];push_cast;rfl
  have phase:(Real.exp (h/2):ℂ)*waveCharacter c h=(4*N:ℂ)^(star c.value):=by
    rw [actual_normalized_character,complexExp]
  have square:(Real.exp (h/2):ℂ)*(Real.exp (h/2):ℂ)=(4*N:ℂ):=by
    rw [←Complex.ofReal_mul,←Real.exp_add,show h/2+h/2=h by ring,complexExp]
  have source:=congrArg (fun z:ℂ=>(Real.exp (h/2):ℂ)*z) (actual_poisson c h nn)
  rw [actual_normalized_lattice c N pos,actual_fourier_lattice c h nn] at source
  have complete:
      ((2*N+1:ℕ):ℂ)*resolvedRaw c 0-
        (4*N:ℂ)^(star c.value)*(resolvedRaw c 0+∑n∈Finset.Ico 1 (N+1),(n:ℂ)^(-star c.value))=
      -jumpCoefficient c/2*((4*N:ℂ)-(4*N:ℂ)^(star c.value))+
        (4*N:ℂ)*(∑'k:ℤ,scaledAliasTerm c (4*N) k)-
        (4*N:ℂ)^(star c.value)*aliasRaw c 0:=by
    rw [realExp] at source
    calc
      _=(Real.exp (h/2):ℂ)*(-jumpCoefficient c/2*((Real.exp (h/2):ℂ)-waveCharacter c h)+
          (Real.exp (h/2):ℂ)*(∑'k:ℤ,scaledAliasTerm c (4*N) k)-waveCharacter c h*aliasRaw c 0):=source
      _= -jumpCoefficient c/2*((Real.exp (h/2):ℂ)*(Real.exp (h/2):ℂ)-
          (Real.exp (h/2):ℂ)*waveCharacter c h)+
          ((Real.exp (h/2):ℂ)*(Real.exp (h/2):ℂ))*(∑'k:ℤ,scaledAliasTerm c (4*N) k)-
          ((Real.exp (h/2):ℂ)*waveCharacter c h)*aliasRaw c 0:=by ring
      _=_:=by rw [square,phase]
  have nz:(4*N:ℂ)≠0:=by exact_mod_cast positive.ne'
  have inverse:(4*N:ℂ)^(star c.value)*(4*N:ℂ)^(-star c.value)=1:=by
    rw [←Complex.cpow_add _ _ nz,add_neg_cancel,Complex.cpow_zero]
  have returnPower:(4*N:ℂ)^(star c.value)*(4*N:ℂ)^(1-star c.value)=(4*N:ℂ):=by
    rw [←Complex.cpow_add _ _ nz,add_sub_cancel,Complex.cpow_one]
  have normalization:=power_normalization c N pos
  have sum: (∑n∈Finset.Ico 1 (N+1),(n:ℂ)^(-star c.value))=
      (∑n∈Finset.Ico 1 N,(n:ℂ)^(-star c.value))+(N:ℂ)^(-star c.value):=by
    exact Finset.sum_Ico_succ_top (by omega:1≤N) (fun n:ℕ=>(n:ℂ)^(-star c.value))
  apply mul_left_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl nz))
  unfold FiniteForcing.coefficient
  simp only [mul_add,mul_sub]
  rw [←mul_assoc _ ((4*N:ℂ)^(-star c.value)),inverse,one_mul,
    ←mul_assoc _ ((4*N:ℂ)^(1-star c.value)),returnPower]
  rw [sum] at complete
  push_cast at complete
  linear_combination complete+normalization

theorem actual_alias_origin_constant (c:BurnolCompletedMellinCoordinate):
    aliasRaw c 0=resolvedRaw c 0+jumpCoefficient c/2+riemannZeta (star c.value):=by
  have positive:0<(star c.value).re:=by
    simp only [star_def,conj_re]
    linarith [c.rightHalf]
  have notOne:star c.value≠1:=by
    intro same
    exact denominator_ne c (by rw [same];ring)
  have next:Tendsto (fun N:ℕ=>N+1) atTop atTop:=tendsto_add_atTop_nat 1
  have natural:Tendsto (fun N:ℕ=>((N+1:ℕ):ℝ)) atTop atTop:=
    (tendsto_natCast_atTop_atTop (R:=ℝ)).comp next
  have scale:Tendsto (fun N:ℕ=>4*((N+1:ℕ):ℝ)) atTop atTop:=
    Tendsto.const_mul_atTop (by norm_num:(0:ℝ)<4) natural
  have coefficient:=
    (DirichletCoefficient.coefficient_tendsto_riemannZeta (star c.value) positive notOne).comp next
  have small:Tendsto (fun N:ℕ=>((N+1:ℕ):ℂ)^(-star c.value)) atTop (𝓝 0):=by
    simpa only [Function.comp_def,Complex.ofReal_natCast] using (actual_power_decay c).comp natural
  have edge:Tendsto (fun N:ℕ=>(4*(N+1):ℂ)^(-star c.value)*resolvedRaw c 0) atTop (𝓝 0):=by
    simpa only [Function.comp_def,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast,Nat.cast_add,
      Nat.cast_one,zero_mul] using ((actual_power_decay c).comp scale).mul_const (resolvedRaw c 0)
  have tail:Tendsto (fun N:ℕ=>(4*(N+1):ℂ)^(1-star c.value)*
      (∑'k:ℤ,scaledAliasTerm c (4*(N+1)) k)) atTop (𝓝 0):=by
    simpa only [Function.comp_def,scaledReturn,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast,
      Nat.cast_add,Nat.cast_one] using (actual_scaled_return_decay c).comp scale
  have price:=((((coefficient.add small).add_const (resolvedRaw c 0)).add_const
    (jumpCoefficient c/2)).sub edge).add tail
  have paid:Tendsto (fun _:ℕ=>aliasRaw c 0) atTop
      (𝓝 (riemannZeta (star c.value)+0+resolvedRaw c 0+jumpCoefficient c/2-0+0)):=by
    apply price.congr
    intro N
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (actual_finite_poisson_bill c (N+1) (by omega)).symm
  have same:=tendsto_nhds_unique tendsto_const_nhds paid
  calc
    _=riemannZeta (star c.value)+0+resolvedRaw c 0+jumpCoefficient c/2-0+0:=same
    _=_:=by ring

private theorem box_origin:
    burnolRadiusTruncatedFourierRaw q (intervalConstant q) 0=(1/2:ℂ):=by
  unfold burnolRadiusTruncatedFourierRaw VectorFourier.fourierIntegral
  simp only [neg_zero,map_zero,AddChar.map_zero_eq_one,one_smul]
  rw [integral_congr_ae (intervalConstant_coeFn q),integral_const,
    burnolRadiusInterval_measureReal_univ (by norm_num:(0:ℝ)<q)]
  norm_num [smul_eq_mul]

theorem actual_companion_origin (c:BurnolCompletedMellinCoordinate):
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.companionRaw c 0=
      (1-star c.value)*riemannZeta (star c.value):=by
  unfold OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.companionRaw
  rw [actual_alias_origin_constant,box_origin]
  norm_num
  ring

theorem actual_original_companion_origin (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.companionRaw c 0=0:=by
  have selected:riemannZeta (star c.value)=0:=by
    simpa only [star_def,zero,map_zero] using riemannZeta_conj c.value
  rw [actual_companion_origin,selected,mul_zero]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
