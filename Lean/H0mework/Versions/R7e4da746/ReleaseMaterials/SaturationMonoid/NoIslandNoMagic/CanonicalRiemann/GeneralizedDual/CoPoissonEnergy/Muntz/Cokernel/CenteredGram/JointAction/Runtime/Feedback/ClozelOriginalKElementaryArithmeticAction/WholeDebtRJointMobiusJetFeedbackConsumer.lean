import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusJetFeedbackSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusJetFeedbackConsumer
open Complex MeasureTheory BurnolPhysicalState
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKSourceResolventReconstruction
open OriginalKFiniteOrderRelease
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open OriginalWholeDebtRJointMobiusJetFeedbackSource
open OriginalWholeDebtRJointMobiusContactPsiPriceSource
open scoped InnerProductSpace
open private allPa_fourier_power_zero power_succ_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
open private coordinate_is_division from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnJordanSource
open private current_inventory current_outside actual_outside_price from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusJetFeedbackSource
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem q_normal (test : BurnolPaAmbientCarrier)
    (inside : test∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) (value : BurnolL2) :
    inner ℂ test (OriginalKCombCofinalPaAction.Q value)=inner ℂ (test : BurnolL2) value := by
  have pa:=burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨test,inside⟩ (burnolEvenAmbientProjection value)
  have physical:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    test value
  exact pa.trans physical

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "eta" => OriginalWholeDebtRJointMobiusReturnAction.returnAmplitude observation nontrivial half
local notation "p" => nextPa observation nontrivial half
local notation "b" => nextFeedback observation nontrivial half
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "FK" => F K
local notation "Rpow" => CombSource.Division.rawIterate observation half.down
local notation "effect" => OriginalWholeDebtRAdjointContactSource.sourceEffect c c
local notation "current" => OriginalWholeDebtRJointMobiusReturnJordanSource.jet observation nontrivial half m

/-- The next Pa event supplies its own original m-prefix; no old cofinal input is used. -/
def releaseInput : BurnolPaAmbientCarrier :=
  ⟨Rpow m (p : BurnolL2),CombSource.Division.whole_pa_physical observation nontrivial half.down m le_rfl
    p (nextPa_mem observation nontrivial half)⟩

def releaseNext : BurnolL2:=burnolDirectRightResolventCLM c (releaseInput observation nontrivial half)

theorem actual_Pa_first_release :
    (∀ k : Nat,k<m → inner ℂ effect (Rpow k (p : BurnolL2))=0) ∧
      inner ℂ effect (Rpow m (p : BurnolL2))=
        star (OriginalWholeDebtRAdjointContactSource.sigma c c)*b*
          inner ℂ (OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c)
            (UnitPowerSource.unitPower observation half m) :=
  OriginalWholeDebtRAdjointContactSource.original_Pa_first_release observation nontrivial half p
    (nextPa_mem observation nontrivial half)

theorem actual_exact_order_Fourier :
    inner ℂ FK (releaseInput observation nontrivial half : BurnolL2)=b*e := by
  have positive:=generatedRiemannXiZeroOrder_pos observation nontrivial
  have native:=UnitPowerSource.actual_Pa_power_split observation half p
    (nextPa_mem observation nontrivial half) (m-1)
  rw [←coordinate_is_division observation nontrivial half] at native
  have split:=congrArg (inner ℂ FK) native
  have lower:=allPa_fourier_power_zero observation nontrivial half _
    (burnolPaSourceCorrection_mem c ⟨p,nextPa_mem observation nontrivial half⟩) (m-1) (by omega)
  rw [←coordinate_is_division observation nontrivial half] at lower
  have top:=UnitPowerSource.unitPower_fourier_top observation nontrivial half
  rw [←coordinate_is_division observation nontrivial half] at top
  rw [show m-1+1=m by omega,inner_add_right,inner_smul_right,lower,top,zero_add] at split
  exact split

/-- The original R source consumes the calculated feedback and retains the entire B field. -/
theorem actual_first_outside : O (releaseNext observation nontrivial half)=
    (-2*b*e) • physicalOutsideColumn c := by
  have action:=original_R_physical_outside_source c (releaseInput observation nontrivial half)
  rw [generatedK_eq_original,actual_exact_order_Fourier] at action
  exact action.trans (by congr 1; ring)

theorem actual_first_whole_update : releaseNext observation nontrivial half=
    (burnolEvenAmbientProjection (releaseNext observation nontrivial half) : BurnolL2)+
      (-2*b*e) • physicalOutsideColumn c := by
  have whole : O (releaseNext observation nontrivial half)=releaseNext observation nontrivial half-
      (burnolEvenAmbientProjection (releaseNext observation nontrivial half) : BurnolL2):=
    Submodule.starProjection_orthogonal_val _
  rw [actual_first_outside] at whole
  linear_combination (norm:=module) -whole

theorem actual_literal_forward_prefix : releaseNext observation nontrivial half=Rpow (m+1) (p : BurnolL2) := by
  have step:=power_succ_left observation half m (p : BurnolL2)
  change Rpow (m+1) (p : BurnolL2)=releaseNext observation nontrivial half at step
  exact step.symm

/-- The finite original Psi/contact source acts on this new input at its own actual feedback. -/
theorem actual_Gamma_release : inner ℂ effect (releaseInput observation nontrivial half : BurnolL2)=
    star (nativeGamma c c)*b*e := by
  have projected:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    (releaseInput observation nontrivial half) effect
  change inner ℂ (OriginalWholeDebtRJointMobiusContactClosureSource.closureInput c c : BurnolL2)
    (releaseInput observation nontrivial half : BurnolL2)=_ at projected
  rw [←projected,actual_calculated_input,inner_smul_left,generatedK_eq_original,actual_exact_order_Fourier]
  simp only [starRingEnd_apply]
  ring

/-- A new feedback is not assigned the previous Pa's nonzero receipt. -/
theorem actual_Gamma_release_zero_iff :
    inner ℂ effect (releaseInput observation nontrivial half : BurnolL2)=0 ↔ nativeGamma c c=0 ∨ b=0 := by
  rw [actual_Gamma_release]
  have eNe:=burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial
  simp only [mul_eq_zero,star_eq_zero,or_false, eNe]

private theorem fk_orthogonal : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    (burnolCompletedMellinRieszVector c)∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := by
  let k : BurnolPaOrthogonalCarrier:=⟨burnolCompletedMellinRieszVector c,
    riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero⟩
  exact (burnolCompactCoPoissonActionSquare.orthogonalAction k).property

private theorem current_physical_orthogonal_read (test : BurnolPaAmbientCarrier)
    (inside : test∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) :
    inner ℂ (test : BurnolL2) current=
      inner ℂ (test : BurnolL2) (currentQ observation nontrivial half : BurnolL2) := by
  rw [current_inventory,inner_add_right,inner_add_right]
  have pa:=inner_eq_zero_symm.mp (inside
    (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half m)
      (OriginalWholeDebtRJointMobiusReturnJordanSource.actual_pa_member observation nontrivial half m))
  change inner ℂ (test : BurnolL2)
    (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half m : BurnolL2)=0 at pa
  have stock : currentOutside observation nontrivial half∈
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ := by
    rw [←current_outside]
    exact Submodule.starProjection_apply_mem _ _
  rw [pa,stock test test.property,zero_add,add_zero]

/-- Only current Q's two original physical moments and all current log-B prices are inputs. -/
def nativeQPrice : ℂ :=
  star (nativeGamma c c)*
    (star (sourceForwardRatio c/(sourceDamping c : ℂ))*
        inner ℂ (generatedK (barC c)) (currentQ observation nontrivial half : BurnolL2)-
      star ((sourceDamping c : ℂ)⁻¹)*inner ℂ (F (generatedK c)) (currentQ observation nontrivial half : BurnolL2)-
      star (2*((‖generatedK c‖^2 : ℝ) : ℂ))*eta*outsidePrice observation nontrivial half)

/-- The complete original R(FK) action consumes the new Q value; no next-Q target moment is supplied. -/
theorem actual_Q_Gamma_effect : inner ℂ effect (nextQ observation nontrivial half : BurnolL2)=
    nativeQPrice observation nontrivial half := by
  have projected:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    (nextQ observation nontrivial half) effect
  change inner ℂ (OriginalWholeDebtRJointMobiusContactClosureSource.closureInput c c : BurnolL2)
    (nextQ observation nontrivial half : BurnolL2)=_ at projected
  have qread:=q_normal (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector c))
    (fk_orthogonal observation nontrivial half) (J.sourceStep c current)
  change inner ℂ FK (OriginalKCombCofinalPaAction.Q (J.sourceStep c current) : BurnolL2)=
    inner ℂ FK (J.sourceStep c current) at qread
  rw [actual_next_Q] at qread
  have adjoint : inner ℂ FK (J.sourceStep c current)=inner ℂ (sourceFKAction c) current := by
    rw [←J.sourceStep_actual,ContinuousLinearMap.adjoint_inner_right]
    have source:=original_R_FK_generated c
    rw [generatedK_eq_original] at source
    exact congrArg (fun value : BurnolL2=>inner ℂ value current) source
  have kbar:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal (barC c)
    (show riemannZeta (barC c).value=0 from observation.conjugate_mathlibZero)
  have Kread:=current_physical_orthogonal_read observation nontrivial half
    (burnolCompletedMellinRieszVector (barC c)) kbar
  have Fread:=current_physical_orthogonal_read observation nontrivial half
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector c))
    (fk_orthogonal observation nontrivial half)
  change inner ℂ FK current=inner ℂ FK (currentQ observation nontrivial half : BurnolL2) at Fread
  have Vread : inner ℂ (physicalOutsideColumn c) current=eta*outsidePrice observation nontrivial half := by
    have normal:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨physicalOutsideColumn c,outsideColumn_orthogonal c⟩ current
    change inner ℂ (physicalOutsideColumn c) (O current)=_ at normal
    rw [current_outside,actual_outside_price] at normal
    exact normal.symm
  rw [←projected,actual_calculated_input,inner_smul_left,generatedK_eq_original,qread,adjoint,sourceFKAction,
    inner_sub_left,inner_sub_left,inner_smul_left,inner_smul_left,inner_smul_left,
    generatedK_eq_original,generatedK_eq_original,Kread,Fread,Vread]
  unfold nativeQPrice
  rw [generatedK_eq_original,generatedK_eq_original]
  simp only [starRingEnd_apply]
  ring

end OriginalWholeDebtRJointMobiusJetFeedbackConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
