import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Read
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Sampling OriginalKElementaryArithmeticAction.PeriodicPower.Lattice
open OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source
open scoped Topology ENNReal InnerProductSpace
local notation "F" => fourierL2
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local notation "CircleL2" => Lp ℂ 2 (AddCircle.haarAddCircle (T:=(1:ℝ)))

private theorem translated_zero (value : BurnolL2) : translated value 0=value := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving value (measurePreserving_add_right volume (0:ℝ))] with x source
  simpa only [translated,Int.cast_zero,add_zero,Function.comp_def] using source

theorem actual_periodization_hasSum (c : BurnolCompletedMellinCoordinate) :
    HasSum (fun k:ℤ=>circleMap (translated (F (resolvedSource c)) k)) (periodizedValue c) := by
  have aliases:HasSum (aliasPiece c) (aliasValue c):=(aliasPiece_summable_norm c).of_norm.hasSum
  have center:HasSum (fun k:ℤ=>if k=0 then circleMap (F (resolvedSource c)) else 0)
      (circleMap (F (resolvedSource c))):=hasSum_ite_eq (0:ℤ) _
  have whole:=center.add aliases
  apply whole.congr_fun
  intro k
  by_cases zero:k=0
  · subst k
    simp [aliasPiece,translated_zero]
  · simp only [aliasPiece,if_neg zero,zero_add]

def coefficientRead (n : ℤ) : CircleL2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _:ℤ=>ℂ) 2 n).comp _root_.fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap

private theorem actual_translated_coefficient (c : BurnolCompletedMellinCoordinate) (k n : ℤ) :
    coefficientRead n (circleMap (translated (F (resolvedSource c)) k))=
      ∫x:ℝ in (-(1/2):ℝ)..(1/2:ℝ),
        _root_.fourier (-n) (x:AddCircle (1:ℝ))*resolvedFourierRaw c (x+k) := by
  change _root_.fourierBasis.repr (circleMap (translated (F (resolvedSource c)) k)) n=_
  rw [_root_.fourierBasis_repr,_root_.fourierCoeff_congr_ae (translated_raw c k)]
  change _root_.fourierCoeff (AddCircle.liftIoc 1 (-(1/2):ℝ) (fun x:ℝ=>resolvedFourierRaw c (x+k))) n=_
  rw [_root_.fourierCoeff_liftIoc_eq,_root_.fourierCoeffOn_eq_integral]
  norm_num only [show (-(1/2):ℝ)+1=1/2 by norm_num,
    show (1/2:ℝ)-(-(1/2))=1 by norm_num,
    show (-(1/2):ℝ)+1-(-(1/2))=1 by norm_num,div_one,one_smul,smul_eq_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [_root_.fourier_coe_apply]
  norm_num

private def phase (n : ℤ) (x : ℝ) : ℂ := _root_.fourier (-n) (x:AddCircle (1:ℝ))

private theorem phase_shift (n k : ℤ) (x : ℝ) : phase n (x+k)=phase n x := by
  have periodic:Function.Periodic (phase n) 1:=
    Function.Periodic.comp (fun t:ℝ=>AddCircle.coe_add_period 1 t) (_root_.fourier (-n))
  simpa only [zsmul_eq_mul,mul_one] using periodic.int_mul k x

private theorem phase_integrable (c : BurnolCompletedMellinCoordinate) (n : ℤ) :
    Integrable (fun x:ℝ=>phase n x*resolvedFourierRaw c x) := by
  have continuousPhase:Continuous (phase n):=(_root_.fourier (-n)).continuous.comp continuous_quotient_mk'
  have source:=(actual_resolved_fourier_integrable c).mul_bdd continuousPhase.aestronglyMeasurable
    (Eventually.of_forall (fun x=>show ‖phase n x‖≤1 from (Circle.norm_coe _).le))
  simpa only [mul_comm] using source

private theorem actual_whole_phase_integral (c : BurnolCompletedMellinCoordinate) (n : ℤ) :
    (∫x:ℝ,phase n x*resolvedFourierRaw c x)=resolvedRaw c n := by
  rw [←actual_resolved_inverse_fourier c n]
  unfold fourierPoint
  apply integral_congr_ae
  filter_upwards [actual_resolved_fourier_raw c] with x source
  rw [source,phase,_root_.fourier_coe_apply]
  congr 2
  push_cast
  ring

/-- All integer translates enter one absolute source programme before Fourier coefficient recovery. -/
theorem actual_periodized_coefficient (c : BurnolCompletedMellinCoordinate) (n : ℤ) :
    coefficientRead n (periodizedValue c)=resolvedRaw c n := by
  have left:=(coefficientRead n).hasSum (actual_periodization_hasSum c)
  have right:=(phase_integrable c n).hasSum_intervalIntegral (-(1/2):ℝ)
  rw [actual_whole_phase_integral] at right
  have same:HasSum (fun k:ℤ=>coefficientRead n (circleMap (translated (F (resolvedSource c)) k)))
      (resolvedRaw c n) := by
    apply right.congr_fun
    intro k
    rw [actual_translated_coefficient]
    have shifted:=intervalIntegral.integral_comp_add_right
      (f:=fun x:ℝ=>phase n x*resolvedFourierRaw c x) (a:=(-(1/2):ℝ)) (b:=1/2) (k:ℝ)
    rw [show (1/2:ℝ)+(k:ℝ)= -(1/2)+(k:ℝ)+1 by ring] at shifted
    rw [←shifted]
    apply intervalIntegral.integral_congr
    intro x _
    change phase n x*resolvedFourierRaw c (x+k)=phase n (x+k)*resolvedFourierRaw c (x+k)
    rw [phase_shift]
  exact left.unique same

private theorem integer_source (c : BurnolCompletedMellinCoordinate) (n : ℤ) :
    resolvedRaw c n=powerCoefficient c n+(if n=0 then resolvedRaw c 0 else 0) := by
  by_cases zero:n=0
  · subst n
    simp [powerCoefficient_zero]
  · rw [if_neg zero,add_zero,powerCoefficient,if_neg zero,resolvedRaw,powerSample]
    have absOne : (1:ℝ)≤|(n:ℝ)|:=by exact_mod_cast Int.one_le_abs zero
    rw [max_eq_right (by linarith:(1/4:ℝ)≤|(n:ℝ)|)]
    have positive:1≤n.natAbs:=by omega
    have cast:(((n.natAbs-1:ℕ):ℂ)+1)=((|((n:ℤ):ℝ)|:ℝ):ℂ) := by
      have successor:(((n.natAbs-1:ℕ):ℂ)+1)=(n.natAbs:ℂ) := by exact_mod_cast Nat.sub_add_cancel positive
      rw [successor]
      norm_cast
      simp
    rw [cast]

/-- The periodized Fourier R source is exactly the existing W, with the original zero mode retained. -/
theorem actual_periodized_source (c : BurnolCompletedMellinCoordinate) :
    periodizedValue c=periodicPower c+resolvedRaw c 0 • (_root_.fourierBasis (T:=(1:ℝ)) 0) := by
  apply _root_.fourierBasis.repr.injective
  ext n
  change coefficientRead n (periodizedValue c)=
    coefficientRead n (periodicPower c+resolvedRaw c 0 • (_root_.fourierBasis (T:=(1:ℝ)) 0))
  rw [actual_periodized_coefficient,map_add,map_smul,smul_eq_mul]
  have power : coefficientRead n (periodicPower c)=powerCoefficient c n := actual_periodic_coefficient c n
  have constant : coefficientRead n (_root_.fourierBasis (T:=(1:ℝ)) 0)=(if n=0 then 1 else 0) := by
    change _root_.fourierBasis.repr (_root_.fourierBasis (T:=(1:ℝ)) 0) n=_
    rw [_root_.fourierBasis.repr_self]
    simp [lp.single_apply,Pi.single_apply]
  rw [power,constant,integer_source]
  split_ifs <;> simp_all

end OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Read
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
