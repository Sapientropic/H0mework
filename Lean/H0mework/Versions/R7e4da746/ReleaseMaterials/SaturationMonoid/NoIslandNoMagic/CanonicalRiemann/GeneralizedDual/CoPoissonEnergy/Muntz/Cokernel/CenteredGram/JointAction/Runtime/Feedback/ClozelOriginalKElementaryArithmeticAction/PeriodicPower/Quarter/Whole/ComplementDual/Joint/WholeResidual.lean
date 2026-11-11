import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaContact

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaContact
open scoped Topology InnerProductSpace BigOperators
open private shell_tail from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaContact
local notation "q"=>(1/4:ℝ)
local notation "T"=>burnolTateReciprocalL2
local notation "A"=>sourceAnnulusCut
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R"=>burnolDirectRightResolventCLM

def enrichedPa (c:BurnolCompletedMellinCoordinate) (j:ℕ):BurnolPaAmbientCarrier:=
  actualPa c j+forcingCoefficient c j • volterraPhysicalShell (barC c) 4

theorem actual_enriched_pa_mem (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    enrichedPa c j∈burnolCompactCoPoissonClosedRange:=
  burnolCompactCoPoissonClosedRange.toSubmodule.add_mem (actual_pa_mem c j)
    (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _ (volterraPhysicalShell_mem _ _))

/-- The complete annulus source has its own generated Pa lift, before taking any quotient by Unit. -/
theorem actual_enriched_pa_source (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    T (burnolMobiusSourceL2 (enrichedPa c j))=A (tateSource c (j+1)):=by
  rw [enrichedPa,map_add,map_add,map_smul,map_smul,actual_pa_source_split]
  change A (tateSource c (j+1))-forcingCoefficient c j • shellSource c+
    forcingCoefficient c j • shellSource c=_
  module

def completeUnitCoefficient (c:BurnolCompletedMellinCoordinate) (j:ℕ):ℂ:=
  2*burnolRadiusMellinTailEvaluator q (by norm_num) (barC c).value (barC c).rightHalf
    (A (((sourceVolterraResolvent (barC c))^(j+1)) (nativeReturn c)))

private theorem shell_coefficient (c:BurnolCompletedMellinCoordinate):
    burnolPaResolventSourceCoefficient (barC c) (volterraPhysicalShell (barC c) 4)=
      2*(Real.log 16:ℂ):=by
  rw [←original_source_mass_eq_coefficient _ _ (volterraPhysicalShell_mem _ _)]
  change 2*(burnolRadiusMellinTailEvaluator q _ (barC c).value (barC c).rightHalf (shellSource c)-
    burnolRadiusMellinTailEvaluator 4 _ (barC c).value (barC c).rightHalf (shellSource c))=_
  rw [shell_tail c q (by norm_num),shell_tail c 4 (by norm_num)]
  norm_num

/-- The full shell Unit pays back the resonant logarithm; the surviving Unit is the actual two-end native stock. -/
theorem actual_complete_unit_coefficient (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    burnolPaResolventSourceCoefficient (barC c) (enrichedPa c j)=completeUnitCoefficient c j:=by
  rw [enrichedPa,map_add,map_smul,actual_lower_coefficient,shell_coefficient,
    completeUnitCoefficient,sourceAnnulusCut_apply,map_sub,
    source_tail_cutoff_inside (barC c) q (by norm_num) 4 (by norm_num),
    source_tail_cutoff_outside (barC c) q (by norm_num) q le_rfl,sub_zero,smul_eq_mul,lowerCoefficient]
  ring

/-- This is an equality in the whole original L2 carrier; its Unit debit has not been sent through Mobius. -/
theorem actual_enriched_pa_update (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    (enrichedPa c (j+1):BurnolL2)=
      R (barC c) (enrichedPa c j:BurnolL2)-
        completeUnitCoefficient c j • burnolUnitTailResponse (barC c) 4+
        forcingCoefficient c (j+1) • (volterraPhysicalShell (barC c) 4:BurnolL2):=by
  have next:=congrArg (fun p:BurnolPaAmbientCarrier=>(p:BurnolL2)) (actual_next_pa c j)
  have coefficient:=actual_complete_unit_coefficient c j
  rw [enrichedPa,map_add,map_smul] at coefficient
  rw [shell_coefficient] at coefficient
  change (actualPa c (j+1):BurnolL2)=
    (R (barC c) (actualPa c j:BurnolL2)-
      burnolPaResolventSourceCoefficient (barC c) (actualPa c j) • burnolUnitTailResponse (barC c) 4)+
    forcingCoefficient c j • (R (barC c) (volterraPhysicalShell (barC c) 4:BurnolL2)-
      burnolPaResolventSourceCoefficient (barC c) (volterraPhysicalShell (barC c) 4) •
        burnolUnitTailResponse (barC c) 4) at next
  rw [shell_coefficient] at next
  change (actualPa c (j+1):BurnolL2)+forcingCoefficient c (j+1) • (volterraPhysicalShell (barC c) 4:BurnolL2)=_
  rw [next,enrichedPa]
  simp only [Submodule.coe_add,Submodule.coe_smul,map_add,map_smul]
  rw [←coefficient]
  simp only [smul_eq_mul] at *
  module

def wholeResidual (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ):BurnolL2:=
  directValue c zero h positive (j+1)-(enrichedPa c j:BurnolL2)

/-- The outside source realizes this specified whole residual, with its Unit fixed by the original realizer. -/
theorem actual_whole_residual_realizes (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ) (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (tateSource c (j+1)-A (tateSource c (j+1))) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (fourierL2 (wholeResidual c zero h positive j))) test:=by
  rw [←actual_enriched_pa_source,←burnolRemainderSourceReadCLM_apply,map_sub,
    burnolRemainderSourceReadCLM_apply,burnolRemainderSourceReadCLM_apply]
  rw [show tateSource c (j+1)=T (directSource c (j+1)) by rfl,
    burnolRemainderRealization_fourier _ _ (actual_direct_realizes c zero h positive (j+1)) test,
    original_tate_source_realizes _ (actual_enriched_pa_mem c j) test,
    wholeResidual,map_sub,map_sub]
  rfl

def wholeDebit (c:BurnolCompletedMellinCoordinate) (j:ℕ):BurnolL2:=
  completeUnitCoefficient c j • burnolUnitTailResponse (barC c) 4-
    forcingCoefficient c (j+1) • (volterraPhysicalShell (barC c) 4:BurnolL2)

/-- The two native endpoint banks pay the whole Unit and shell debit together. -/
theorem actual_whole_debit_log_bank (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    wholeDebit c j=(2*((-2:ℂ)^(j+1)/((j+1).factorial:ℂ))) •
      (((∫x:ℝ in Ioi q,(x:ℂ)^(-star c.value)*(Real.log (x/q):ℂ)^(j+1)*nativeReturn c x)-
        (∫x:ℝ in Ioi 4,(x:ℂ)^(-star c.value)*(Real.log (x/4):ℂ)^(j+1)*nativeReturn c x)) •
          burnolUnitTailResponse (barC c) 4+
        (∫x:ℝ in Ioi 4,(x:ℂ)^(-star c.value)*(Real.log (x/4):ℂ)^(j+1)*nativeReturn c x) •
          (volterraPhysicalShell (barC c) 4:BurnolL2)):=by
  rw [wholeDebit,completeUnitCoefficient,
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusContact.actual_native_lower_contact,forcingCoefficient,
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog.actual_native_tail_log_bank]
  module

/-- The native source update lifts to the actual whole field, including the complete original Unit. -/
theorem actual_whole_residual_update (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ):
    wholeResidual c zero h positive (j+1)=
      R (barC c) (wholeResidual c zero h positive j)+wholeDebit c j:=by
  have next:directValue c zero h positive (j+1+1)=R (barC c) (directValue c zero h positive (j+1)):=by
    rw [directValue,pow_succ',mul_apply_eq_comp]
    rfl
  rw [wholeResidual,next,actual_enriched_pa_update,wholeResidual,map_sub,wholeDebit]
  module

theorem actual_whole_residual_iteration (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (n:ℕ):
    wholeResidual c zero h positive n=
      ((R (barC c))^n) (wholeResidual c zero h positive 0)+
        ∑i∈Finset.range n,((R (barC c))^(n-1-i)) (wholeDebit c i):=by
  induction n with
  | zero=>simp
  | succ n previous=>
    rw [actual_whole_residual_update,previous,map_add,map_sum,Finset.sum_range_succ,
      show n+1-1-n=0 by omega,pow_zero,one_apply_eq_self,pow_succ',mul_apply_eq_comp]
    have shifted:∑i∈Finset.range n,R (barC c) (((R (barC c))^(n-1-i)) (wholeDebit c i))=
      ∑i∈Finset.range n,((R (barC c))^(n+1-1-i)) (wholeDebit c i):=by
      apply Finset.sum_congr rfl
      intro i member
      have before:=Finset.mem_range.mp member
      rw [show n+1-1-i=n-1-i+1 by omega,pow_succ',mul_apply_eq_comp]
    rw [shifted]
    module

/-- Every original Unit column remains explicit in the full-carrier iteration. -/
theorem actual_whole_debit_column (c:BurnolCompletedMellinCoordinate) (i k:ℕ):
    ((R (barC c))^k) (wholeDebit c i)=
      completeUnitCoefficient c i • (((R (barC c))^k) (burnolUnitTailResponse (barC c) 4))-
      forcingCoefficient c (i+1) • (((R (barC c))^k) (volterraPhysicalShell (barC c) 4:BurnolL2)):=by
  rw [wholeDebit,map_sub,map_smul,map_smul]

/-- The independent original K consumes the generated Pa lift while retaining all whole-field Unit columns. -/
theorem actual_original_K_whole_consumer (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner c.value
    inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2) (directValue c zero h positive m)=
      inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2)
        ((R (barC c)^(m-1)) (wholeResidual c zero h positive 0)+
          ∑i∈Finset.range (m-1),
            (completeUnitCoefficient c i •
              ((R (barC c)^(m-2-i)) (burnolUnitTailResponse (barC c) 4))-
             forcingCoefficient c (i+1) •
              ((R (barC c)^(m-2-i)) (volterraPhysicalShell (barC c) 4:BurnolL2)))):=by
  dsimp only
  let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner c.value
  have orderPositive:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  have step:m-1+1=m:=by
    change 0<m at orderPositive
    omega
  have orthogonal:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  have paid:inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2) (enrichedPa c (m-1):BurnolL2)=0:=
    inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal _ _).mp orthogonal _ (actual_enriched_pa_mem c (m-1)))
  have whole:=actual_whole_residual_iteration c zero h positive (m-1)
  rw [wholeResidual,step] at whole
  have read:=congrArg (inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2)) whole
  rw [inner_sub_right,paid,sub_zero] at read
  rw [read]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i member
  rw [actual_whole_debit_column,show m-1-1-i=m-2-i by omega]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
