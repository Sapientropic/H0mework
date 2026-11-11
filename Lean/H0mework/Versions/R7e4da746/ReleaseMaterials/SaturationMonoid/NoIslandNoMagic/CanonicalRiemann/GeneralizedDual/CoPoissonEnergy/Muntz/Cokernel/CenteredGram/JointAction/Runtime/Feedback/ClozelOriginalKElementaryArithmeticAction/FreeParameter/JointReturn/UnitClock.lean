import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitJet
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitClock
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitJet
open scoped InnerProductSpace Topology BigOperators
local notation "L" => (Real.log 4:ℂ)
local notation "phase" s => fullMellinTranslationCharacter s (Real.log 16)
open private fourClock from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitJet

def radiusFamily (base:BurnolCompletedMellinCoordinate) (test:BurnolL2) (s:ℂ) : ℂ :=
 (phase base.value)⁻¹*Complex.exp (L*(s-base.value))*inner ℂ test (normalizedUnit base s)

theorem radius_family_analytic (base:BurnolCompletedMellinCoordinate) (test:BurnolL2) :
 AnalyticAt ℂ (radiusFamily base test) base.value := by
 unfold radiusFamily
 exact (analyticAt_const.mul ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp)).mul
  (((innerSL ℂ test).analyticAt _).comp (normalized_unit_analytic base))

private theorem two_clock_source (base probe:BurnolCompletedMellinCoordinate) :
 (phase base.value)⁻¹*Complex.exp (L*(probe.value-base.value))*(fourClock probe/fourClock base)=
  (phase probe.value)⁻¹ := by
 unfold fourClock fullMellinTranslationCharacter
 simp only [div_eq_mul_inv,←Complex.exp_neg]
 have logarithm:Real.log 16=2*Real.log 4:=by
  rw [show (16:ℝ)=4^2 by norm_num,Real.log_pow]
  norm_num
 rw [logarithm]
 simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_neg]
 repeat rw [←Complex.exp_add]
 congr 1
 ring

/-- Both native radius clocks are used before the parameter is differentiated. -/
theorem actual_radius_family_source (base probe:BurnolCompletedMellinCoordinate) (test:BurnolL2) :
 radiusFamily base test probe.value=(phase probe.value)⁻¹*inner ℂ test (burnolUnitTailResponse probe 4) := by
 unfold radiusFamily
 rw [←actual_normalized_unit_source,inner_smul_right,←mul_assoc,two_clock_source]

private theorem scalar_read_jet {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
 (reader:E→L[ℂ]ℂ) {family:ℂ→E} {s:ℂ} (native:AnalyticAt ℂ family s) (j:ℕ) :
 iteratedDeriv j (fun z=>reader (family z)) s=reader (iteratedDeriv j family s) := by
 change (iteratedFDeriv ℂ j (reader ∘ family) s) (fun _=>1)=_
 rw [reader.iteratedFDeriv_comp_left (native.contDiffAt (n:=j)) le_rfl]
 rfl

private theorem exp_clock_jet (b:ℂ) (j:ℕ) :
 iteratedDeriv j (fun s:ℂ=>Complex.exp (L*(s-b))) b=L^j := by
 have source:(fun s:ℂ=>Complex.exp (L*(s-b)))=
   (fun s:ℂ=>Complex.exp (-L*b)*Complex.exp (L*s)):=by
  ext s
  rw [←Complex.exp_add]
  congr 1
  ring
 rw [source,iteratedDeriv_const_mul_field,iteratedDeriv_cexp_const_mul]
 calc
  _=L^j*(Complex.exp (-L*b)*Complex.exp (L*b)):=by ring
  _=_:=by rw [←Complex.exp_add];simp

/-- The radius-normalized original free Unit germ retains every lower resolvent word. -/
theorem actual_radius_family_jet (base:BurnolCompletedMellinCoordinate) (test:BurnolL2) (m:ℕ) :
 iteratedDeriv m (radiusFamily base test) base.value=
  (phase base.value)⁻¹*∑j∈Finset.range (m+1),
   (m.choose j:ℂ)*L^(m-j)*((j.factorial:ℂ)/(2:ℂ)^j)*inner ℂ test (unitJet base j) := by
 have read:AnalyticAt ℂ (fun s:ℂ=>inner ℂ test (normalizedUnit base s)) base.value:=
  ((innerSL ℂ test).analyticAt _).comp (normalized_unit_analytic base)
 have exponential:ContDiffAt ℂ m (fun s:ℂ=>Complex.exp (L*(s-base.value))) base.value:=by fun_prop
 have source:radiusFamily base test=(fun s:ℂ=>(phase base.value)⁻¹*
   (inner ℂ test (normalizedUnit base s)*Complex.exp (L*(s-base.value)))):=by
  ext s
  unfold radiusFamily
  ring
 rw [source,iteratedDeriv_const_mul_field,iteratedDeriv_fun_mul (read.contDiffAt (n:=m)) exponential]
 congr 1
 apply Finset.sum_congr rfl
 intro j _
 have scalar:=scalar_read_jet (innerSL ℂ test) (normalized_unit_analytic base) j
 simp only [innerSL_apply_apply] at scalar
 rw [scalar,normalized_unit_jet,inner_smul_right,exp_clock_jet]
 ring

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
