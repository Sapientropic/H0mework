import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.UnitSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalUnitMellinSource.Power
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalUnitMellinSource.Resolvent OriginalUnitMellinSource.Unit
open private actual_tate_mellin from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.UnitSource
local notation "T"=>burnolTateReciprocalL2
local notation "F"=>fourierL2
local notation "R"=>burnolDirectRightResolventCLM

private theorem actual_TF_R (c:BurnolCompletedMellinCoordinate) (v:BurnolL2):
    T (F (R c v))=R c (T (F v)):=by
  have right:1/4<(c.value/2).re:=by rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  change T (F (burnolDirectRightResolvent (c.value/2) v))=_
  rw [FiniteMobiusResolventFlux.fourier_R _ right,FiniteMobiusResolventFlux.Rplus_tate _ right,
    burnolTateReciprocalL2_involutive]
  rfl

/-- Original whole R word, before any restriction or mean replacement. -/
theorem actual_unit_power_tate_mellin (c:BurnolCompletedMellinCoordinate) (w:ℂ) (j:Nat)
    (positive:0<w.re) (below:w.re<1) (between:w.re<c.value.re):
    HasMellin (T (F (((R c)^j) (burnolUnitTailResponse c 4))):ℝ→ℂ) w
      ((2:ℂ)^j*(4:ℂ)^(w-c.value)*riemannZeta w/(w-c.value)^(j+1)):=by
  induction j with
  | zero=>
    have initial:=actual_unit_four_mellin c w positive below between
    have source:=actual_tate_mellin _ (1-w) _ initial
    change HasMellin (T (F (burnolUnitTailResponse c 4)):ℝ→ℂ) w _
    simpa only [pow_zero,one_mul,Nat.zero_add,pow_one,sub_sub_cancel] using source
  | succ j previous=>
    have acted:=actual_R_mellin c (T (F (((R c)^j) (burnolUnitTailResponse c 4)))) w _ previous between
    have step:((R c)^(j+1)) (burnolUnitTailResponse c 4)=
        R c (((R c)^j) (burnolUnitTailResponse c 4)):=by
      rw [pow_succ',mul_apply_eq_comp]
    rw [step,actual_TF_R]
    change HasMellin (burnolDirectRightResolvent (c.value/2)
      (T (F (((R c)^j) (burnolUnitTailResponse c 4)))):ℝ→ℂ) w _
    convert acted using 1
    have dn:w-c.value≠0:=by
      intro zero
      have realPart:=congrArg Complex.re zero
      simp only [sub_re,zero_re] at realPart
      linarith
    rw [pow_succ (w-c.value),pow_succ (2:ℂ)]
    field_simp [dn]

theorem actual_unit_power_mellin (c:BurnolCompletedMellinCoordinate) (w:ℂ) (j:Nat)
    (positive:0<w.re) (below:w.re<1) (between:w.re<c.value.re):
    HasMellin (F (((R c)^j) (burnolUnitTailResponse c 4)):ℝ→ℂ) (1-w)
      ((2:ℂ)^j*(4:ℂ)^(w-c.value)*riemannZeta w/(w-c.value)^(j+1)):=by
  have source:=actual_tate_mellin _ w _ (actual_unit_power_tate_mellin c w j positive below between)
  rw [burnolTateReciprocalL2_involutive] at source
  exact source

end OriginalUnitMellinSource.Power
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
