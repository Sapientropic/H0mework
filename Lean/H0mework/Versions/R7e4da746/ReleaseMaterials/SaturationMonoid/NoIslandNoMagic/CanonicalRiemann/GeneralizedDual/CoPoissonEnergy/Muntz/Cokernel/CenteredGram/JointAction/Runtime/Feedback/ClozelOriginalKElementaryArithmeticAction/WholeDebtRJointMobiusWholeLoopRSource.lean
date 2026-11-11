import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusCoupledCayleySource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusWholeLoopRSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalWholeDebtRJointMobiusCoupledCayleySource
open scoped InnerProductSpace
open private forward_cut from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusProgrammeSource
open private inverseFourier_Rbar_F from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "u" => OriginalWholeDebtRJointMobiusUnitSource.response
local notation "raw" => OriginalWholeDebtRJointMobiusUnitSource.sourceRaw

open OriginalKCenteredMobiusRSource
open private forward_zero_window from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusUnitSource
local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "q" => (1/4 : ℝ)

/-- Both forcing legs are constructed before the same source's U/F actions are executed. -/
def wholeLoop (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  coupling c • F (coupledForcing (barC c))+sourceCayley (barC c) (coupledForcing c)

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : barC (barC c)=c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]

private theorem source_Cayley_F (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceCayley (barC c) (F value)=F (sourceAdjointCayley c value) := by
  have acted:=congrArg F (inverseFourier_Rbar_F c value)
  rw [fourierL2.apply_symm_apply] at acted
  change burnolDirectRightResolvent ((barC c).value/2) (F value)=
    F (OriginalKFullAdjointSource.sourceAdjoint c value) at acted
  rw [sourceCayley_apply,sourceAdjointCayley,map_add,map_smul]
  rw [acted]
  rfl

/-- The two literal coupled updates determine the full vector, before any physical or Pa restriction. -/
theorem actual_whole_loop (c : BurnolCompletedMellinCoordinate) :
    wholeLoop c=u c-(coupling c*coupling (barC c)) • reflectL2 (u c) := by
  have source:=actual_inverse_update c
  rw [coupledInput,map_add,map_smul,source_Cayley_F] at source
  have conjugated:=actual_coupled_update (barC c)
  rw [conjugate_twice] at conjugated
  rw [conjugated,coupledInput,conjugate_twice,map_add,map_smul,fourierL2_fourierL2] at source
  unfold wholeLoop
  linear_combination (norm:=module) source

/-- The same all-axis outside source is retained as actual material, without global L2 qualification. -/
def loopSourceRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (1-coupling c*coupling (barC c))*raw c x

def wholeLoopRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  burnolInnerGapForward (loopSourceRaw c)

private theorem loop_source_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x|≤(1/4 : ℝ)) : loopSourceRaw c x=0 := by
  unfold loopSourceRaw
  rw [OriginalWholeDebtRJointMobiusUnitSource.actual_source_zero_window c (by linarith),mul_zero]

private theorem loop_forward (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    wholeLoopRaw c x=(1-coupling c*coupling (barC c))*burnolInnerGapForward (raw c) x := by
  rw [wholeLoopRaw,forward_cut _ (loop_source_gap c),forward_cut _
    (fun {x} inside => OriginalWholeDebtRJointMobiusUnitSource.actual_source_zero_window c (by linarith)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold loopSourceRaw
  ring

/-- Unlike the finite M-window, this inverse read recovers the entire original outside source. -/
theorem actual_all_axis_inverse (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolCenteredMobiusInverse (wholeLoopRaw c) x=loopSourceRaw c x := by
  simpa only [wholeLoopRaw,sub_zero] using
    burnolCenteredMobiusInverse_forward_innerGap (loopSourceRaw c) (loop_source_gap c) 0 x

/-- The actual full source is advanced by its original inward Euler inverse, not by a supplied next value. -/
def nextSourceRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  -2*((|x| : ℝ) : ℂ)^(-c.value)*
    (∫ v : ℝ in 0..|x|,(v : ℂ)^(c.value-1)*loopSourceRaw c v)

def nextRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ := sourceRRaw c (wholeLoopRaw c)

/-- This update executes original R on the whole U/F source loop. -/
def next (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolDirectRightResolventCLM c (wholeLoop c)

private theorem input_raw_gap4 (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x|≤(4 : ℝ)) : wholeLoopRaw c x=0 := by
  rw [loop_forward]
  change _*OriginalWholeDebtRJointMobiusUnitSource.responseRaw c x=0
  rw [OriginalWholeDebtRJointMobiusUnitSource.actual_response_zero_window c inside,mul_zero]

private theorem input_raw_zero (c : BurnolCompletedMellinCoordinate) : wholeLoopRaw c 0=0 :=
  input_raw_gap4 c (by norm_num)

private theorem input_raw_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x|≤q) : wholeLoopRaw c x=wholeLoopRaw c 0 := by
  rw [input_raw_zero,input_raw_gap4 c (by linarith)]

private theorem next_raw_zero (c : BurnolCompletedMellinCoordinate) : nextRaw c 0=0 := by
  rw [nextRaw,sourceRRaw_zero,input_raw_zero,mul_zero,zero_div]

private theorem next_raw_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x|≤q) : nextRaw c x=nextRaw c 0 := by
  rw [nextRaw,sourceRRaw_gap c _ (input_raw_gap c) inside,sourceRRaw_zero]

private theorem next_raw_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    nextRaw c (-x)=nextRaw c x := by
  simp only [nextRaw,sourceRRaw,abs_neg]

private theorem inverse_even (f : ℝ → ℂ) (even : ∀ x,f (-x)=f x) (x : ℝ) :
    burnolCenteredMobiusInverse f (-x)=burnolCenteredMobiusInverse f x := by
  unfold burnolCenteredMobiusInverse
  apply tsum_congr
  intro n
  simp only [neg_div,even]

/-- No global L2 hypothesis on the inverse source is used in this all-axis production. -/
theorem actual_source_zero_window (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x|≤(4 : ℝ)) : nextSourceRaw c x=0 := by
  have prefixIntegral : (∫ v : ℝ in 0..|x|,(v : ℂ)^(c.value-1)*loopSourceRaw c v)=0 := by
    rw [intervalIntegral.integral_of_le (abs_nonneg x)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v between
    unfold loopSourceRaw
    rw [OriginalWholeDebtRJointMobiusUnitSource.actual_source_zero_window c
      (by rw [abs_of_pos between.1];exact between.2.trans inside),mul_zero,mul_zero]
  rw [nextSourceRaw,prefixIntegral,mul_zero]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualResponse : BurnolPaAmbientCarrier :=
  ⟨u c,OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩

theorem actual_response_even : reflectL2 (u c)=u c :=
  mem_evenL2ClosedFace_iff.mp (OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half).2

/-- The original B/chi/signed/contact/Pa/whole-unit inventory is kept in the actual whole loop. -/
theorem actual_source_loop : wholeLoop c=(1-coupling c*coupling (barC c)) • u c := by
  rw [actual_whole_loop,actual_response_even]
  module


/-- The literal U/F whole loop and the full raw source are two faces of this same update. -/
theorem actual_whole_loop_raw : (wholeLoop c : ℝ → ℂ)=ᵐ[volume] wholeLoopRaw c := by
  rw [actual_source_loop]
  filter_upwards [Lp.coeFn_smul (1-coupling c*coupling (barC c)) (u c),
    OriginalWholeDebtRJointMobiusUnitSource.actual_raw c] with x scalar actual
  rw [scalar]
  change (1-coupling c*coupling (barC c))*u c x=wholeLoopRaw c x
  rw [actual]
  exact (loop_forward c x).symm

/-- The existing physical carrier receives the whole source loop; no Pa admission is constructed. -/
def actualLoop : BurnolPaAmbientCarrier :=
  ⟨wholeLoop c,by
    rw [actual_source_loop]
    exact Submodule.smul_mem _ _ (OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half)⟩

private theorem input_native : MemLp (wholeLoopRaw c) 2 volume :=
  (Lp.memLp (wholeLoop c)).ae_eq (actual_whole_loop_raw observation nontrivial half)

/-- Existing full original R consumes the actual same input and supplies the whole next's L2 realization. -/
theorem actual_next_raw : (next c : ℝ → ℂ)=ᵐ[volume] nextRaw c := by
  exact OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_R_even_read c (wholeLoop c)
    (wholeLoopRaw c) (actual_whole_loop_raw observation nontrivial half) (input_raw_gap c)
    (by rw [actual_source_loop];rw [map_smul,actual_response_even])

theorem actual_next_native : MemLp (nextRaw c) 2 volume :=
  (Lp.memLp (next c)).ae_eq (actual_next_raw observation nontrivial half)

private theorem inverse_positive (t : ℝ) (positive : 0<t) :
    burnolCenteredMobiusInverse (nextRaw c) t=nextSourceRaw c t := by
  have source:=source_inverse_R_action c (wholeLoopRaw c) (input_native observation nontrivial half)
    (input_raw_gap c) t positive
  simp_rw [actual_all_axis_inverse] at source
  rw [nextSourceRaw,abs_of_pos positive]
  exact source

/-- The independent existing untruncated Mobius/R source law identifies every next-source coordinate. -/
theorem actual_next_inverse (x : ℝ) : burnolCenteredMobiusInverse (nextRaw c) x=nextSourceRaw c x := by
  rcases lt_trichotomy x 0 with negative|zero|positive
  · calc
      _=burnolCenteredMobiusInverse (nextRaw c) (-x) := by
        simpa only [neg_neg] using inverse_even (nextRaw c) (next_raw_even c) (-x)
      _=nextSourceRaw c (-x) := inverse_positive observation nontrivial half (-x) (neg_pos.mpr negative)
      _=nextSourceRaw c x := by simp only [nextSourceRaw,abs_neg]
  · subst x
    rw [burnolCenteredMobiusInverse_eq_zero_of_quarterGap _ (next_raw_gap c) (by norm_num),
      actual_source_zero_window c (by norm_num)]
  · exact inverse_positive observation nontrivial half x positive

/-- Complete reconstruction uses the newly produced all-axis source, not its finite window. -/
theorem actual_forward_source (x : ℝ) : nextRaw c x=burnolInnerGapForward (nextSourceRaw c) x := by
  have source:=burnolCenteredMobiusInverse_exactReconstruction (nextRaw c) (next_raw_gap c) x
  simp_rw [actual_next_inverse observation nontrivial half] at source
  rw [next_raw_zero,sub_zero] at source
  exact source.symm

/-- Position gap4 belongs to the literal next before any physical projection. -/
theorem actual_next_zero_window : (next c : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval (4 : ℝ))] fun _=>0 := by
  filter_upwards [ae_restrict_of_ae (actual_next_raw observation nontrivial half),
    ae_restrict_mem (measurableSet_symmetricInterval (4 : ℝ))] with x actual inside
  rw [actual,actual_forward_source]
  exact forward_zero_window _ (actual_source_zero_window c) (abs_le.mpr inside)

def outsideCoefficient : ℂ := -2*inner ℂ (F (burnolCompletedMellinRieszVector c : BurnolL2)) (wholeLoop c)

/-- The same actual R input feeds the independent complete original B producer, retaining its FK leg. -/
theorem actual_B_effect : O (next c)=outsideCoefficient observation nontrivial half •
    OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c := by
  have source:=OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.original_R_physical_outside_source c
    (actualLoop observation nontrivial half)
  rw [OriginalKSourceResolventReconstruction.generatedK_eq_original] at source
  exact source

/-- The whole next retains both its physical read and the original full B column. -/
theorem actual_whole_next : next c=(P (next c) : BurnolL2)+outsideCoefficient observation nontrivial half •
    OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c := by
  have whole : O (next c)=next c-(P (next c) : BurnolL2) := Submodule.starProjection_orthogonal_val _
  rw [actual_B_effect observation nontrivial half] at whole
  linear_combination (norm:=module) -whole

end OriginalWholeDebtRJointMobiusWholeLoopRSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
