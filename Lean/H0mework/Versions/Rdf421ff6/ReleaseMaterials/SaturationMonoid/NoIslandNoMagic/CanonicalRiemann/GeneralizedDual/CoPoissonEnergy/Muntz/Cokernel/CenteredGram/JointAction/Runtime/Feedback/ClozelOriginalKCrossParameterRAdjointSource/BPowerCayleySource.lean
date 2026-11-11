import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource
import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.ZeroPositiveMellinTateOrbit

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.BPowerCayleySource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open scoped InnerProductSpace
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "P" => burnolEvenAmbientProjectionEndomorphism
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "U" => sourceCayley
local notation "K" => burnolCompletedMellinRieszVector
local instance bPowerPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private def kernelMass (c : BurnolCompletedMellinCoordinate) : ℂ := ((‖generatedK c‖^2:ℝ):ℂ)
private def powerMass (c : BurnolCompletedMellinCoordinate) : ℂ := ((‖hPowerPhysicalCorrection c‖^2:ℝ):ℂ)
private theorem damping_ne_zero (c : BurnolCompletedMellinCoordinate) : (sourceDamping c:ℂ)≠0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (sourceDamping_pos c))

-- Exact already paid generic cross blocks; no parent source or proof is rebuilt.
elab "paidPowerBBlock" : term => do
  let head := ("_private.H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
  let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource.source_B_block".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
  return Lean.mkConst full
elab "paidPowerCAdjointBlock" : term => do
  let head := ("_private.H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
  let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource.source_C_adjoint_block".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
  return Lean.mkConst full

private theorem generated_kernel_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) :
    generatedK (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)≠0 := by
  have actual := burnolAnalyticComplementCompletedMellinEvaluator_ne_zero_generated observation nontrivial rightHalf
  intro zero
  rw [generatedK_eq_original] at zero
  change (K (burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf):BurnolL2)=0 at zero
  apply actual
  apply ContinuousLinearMap.ext
  intro v
  change burnolCompletedMellinEvaluator (burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf) v=0
  rw [←burnolCompletedMellinRieszVector_readback]
  change inner ℂ (K (burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf):BurnolL2) (v:BurnolL2)=0
  rw [zero,inner_zero_left]

private theorem conjugate_generated_kernel_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) :
    generatedK (barC (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf))≠0 := by
  let reflected := conjugateZeroObservation observation
  have reflectedHalf : 1/2<reflected.coordinate.re := by
    change 1/2<(starRingEnd ℂ observation.coordinate).re
    simpa only [Complex.conj_re] using rightHalf
  have actual := generated_kernel_ne_zero reflected (observation.conjugate_nontrivial nontrivial) reflectedHalf
  have coordinate : burnolDivisionZeroCompletedMellinCoordinate reflected reflectedHalf=
      barC (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) := by rfl
  rw [coordinate] at actual
  exact actual

private theorem mass_ne_zero (c : BurnolCompletedMellinCoordinate) (native : generatedK c≠0) : kernelMass c≠0 := by
  unfold kernelMass
  exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr native)
private theorem generated_projection (c : BurnolCompletedMellinCoordinate) : P (generatedK c)=generatedK c := by
  rw [generatedK_eq_original]
  exact congrArg (fun x:BurnolPaAmbientCarrier => (x:BurnolL2))
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K c))
private theorem generated_F_projection (c : BurnolCompletedMellinCoordinate) :
    P (fourierL2 (generatedK c))=fourierL2 (generatedK c) := by
  have source := fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius (generatedK c)
  change fourierL2 (P (generatedK c))=P (fourierL2 (generatedK c)) at source
  rw [generated_projection] at source
  exact source.symm
private theorem orthogonal_O (value : BurnolL2)
    (inside : value∈(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ) : O value=value :=
  Submodule.starProjection_eq_self_iff.mpr inside
private theorem orthogonal_P (value : BurnolL2)
    (inside : value∈(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ) : P value=0 := by
  change ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto value:BurnolL2)=0
  rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal inside,Submodule.coe_zero]

private theorem source_left_inverse (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (U c).adjoint (U c value)=value := by
  apply ext_inner_left ℂ
  intro test
  rw [ContinuousLinearMap.adjoint_inner_right,sourceCayley_inner]
private theorem source_right_inverse (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    U c ((U c).adjoint value)=value := by
  let inverse : BurnolL2 →ₗᵢ[ℂ] BurnolL2 := {
    (U c).adjoint.toLinearMap with
    norm_map' := fun x => by
      change ‖(U c).adjoint x‖=‖x‖
      rw [sourceCayley_actual_adjoint,sourceAdjointCayley_norm] }
  apply ext_inner_right ℂ
  intro test
  rw [←ContinuousLinearMap.adjoint_inner_right]
  exact inverse.inner_map_map value test

private theorem source_U_FK (c : BurnolCompletedMellinCoordinate) :
    U c (fourierL2 (generatedK c))=
      sourceForwardRatio c • generatedK (barC c)-
        (2*(sourceDamping c:ℂ)*kernelMass c) • physicalOutsideColumn c := by
  rw [sourceCayley_apply,original_R_FK_generated,sourceFKAction,smul_sub,smul_sub,smul_smul,smul_smul,smul_smul]
  have coefficient : (sourceDamping c:ℂ)*(sourceForwardRatio c/(sourceDamping c:ℂ))=sourceForwardRatio c := by
    field_simp [damping_ne_zero c]
  rw [coefficient,mul_inv_cancel₀ (damping_ne_zero c),one_smul]
  unfold kernelMass
  module
private theorem source_Uadj_Kbar (c : BurnolCompletedMellinCoordinate) :
    (U c).adjoint (generatedK (barC c))=
      sourceAdjointRatio c • fourierL2 (generatedK c)-
        (2*(sourceDamping c:ℂ)*kernelMass (barC c)) • hPowerPhysicalCorrection c := by
  rw [sourceCayley_actual_adjoint,sourceAdjointCayley,original_R_adjoint_conjugateK_generated,
    sourceConjugateAdjointAction,smul_sub,smul_sub,smul_smul,smul_smul,smul_smul]
  have coefficient : (sourceDamping c:ℂ)*(sourceAdjointRatio c/(sourceDamping c:ℂ))=sourceAdjointRatio c := by
    field_simp [damping_ne_zero c]
  rw [coefficient,mul_inv_cancel₀ (damping_ne_zero c),one_smul]
  unfold kernelMass
  module

private theorem source_P_UW (c : BurnolCompletedMellinCoordinate) :
    P (U c (hPowerPhysicalCorrection c))=
      (-2*(sourceDamping c:ℂ)*powerMass c) • generatedK (barC c) := by
  have source := paidPowerBBlock c (hPowerPhysicalCorrection c)
  rw [orthogonal_O _ (powerCorrection_orthogonal c)] at source
  have self : inner ℂ (hPowerPhysicalCorrection c) (hPowerPhysicalCorrection c)=powerMass c := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (Complex.ofReal_pow _ _).symm
  rw [self] at source
  exact source
private theorem source_P_UadjV (c : BurnolCompletedMellinCoordinate) :
    P ((U c).adjoint (physicalOutsideColumn c))=
      (-2*(sourceDamping c:ℂ)*powerMass (barC c)) • fourierL2 (generatedK c) := by
  have source := paidPowerCAdjointBlock c (physicalOutsideColumn c)
  rw [orthogonal_O _ (outsideColumn_orthogonal c)] at source
  have self : inner ℂ (physicalOutsideColumn c) (physicalOutsideColumn c)=powerMass (barC c) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖fourierL2.symm (hPowerPhysicalCorrection (barC c))‖:ℂ)^2=_
    rw [fourierL2.symm.norm_map]
    exact (Complex.ofReal_pow _ _).symm
  rw [self] at source
  exact source

section ActualSource
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
include nontrivial

private theorem actual_scalar_products :
    sourceAdjointRatio c*sourceForwardRatio c=1-4*(sourceDamping c:ℂ)^2*kernelMass (barC c)*powerMass c ∧
    sourceForwardRatio c*sourceAdjointRatio c=1-4*(sourceDamping c:ℂ)^2*kernelMass c*powerMass (barC c) := by
  constructor
  · have source := congrArg P (source_right_inverse c (generatedK (barC c)))
    rw [source_Uadj_Kbar] at source
    simp only [map_sub,map_smul,source_U_FK,generated_projection,
      orthogonal_P _ (outsideColumn_orthogonal c),smul_zero,sub_zero,source_P_UW,
      smul_smul] at source
    have factored : (sourceAdjointRatio c*sourceForwardRatio c+
        4*(sourceDamping c:ℂ)^2*kernelMass (barC c)*powerMass c-1) • generatedK (barC c)=0 := by
      linear_combination (norm := module) source
    have scalar := (smul_eq_zero.mp factored).resolve_right
      (conjugate_generated_kernel_ne_zero observation nontrivial half.down)
    linear_combination scalar
  · have source := congrArg P (source_left_inverse c (fourierL2 (generatedK c)))
    rw [source_U_FK] at source
    simp only [map_sub,map_smul,source_Uadj_Kbar,generated_F_projection,
      orthogonal_P _ (powerCorrection_orthogonal c),smul_zero,sub_zero,source_P_UadjV,
      smul_smul] at source
    have factored : (sourceForwardRatio c*sourceAdjointRatio c+
        4*(sourceDamping c:ℂ)^2*kernelMass c*powerMass (barC c)-1) • fourierL2 (generatedK c)=0 := by
      linear_combination (norm := module) source
    have FourierNe : fourierL2 (generatedK c)≠0 := by
      intro zero
      have same := congrArg fourierL2.symm zero
      rw [fourierL2.symm_apply_apply,map_zero] at same
      exact generated_kernel_ne_zero observation nontrivial half.down same
    have scalar := (smul_eq_zero.mp factored).resolve_right FourierNe
    linear_combination scalar

/-- Both coefficients and their balance are outputs of the same two actual full-L2 inverse actions. -/
theorem actual_scalar_balance_source :
    sourceAdjointRatio c*sourceForwardRatio c=1-4*(sourceDamping c:ℂ)^2*kernelMass (barC c)*powerMass c ∧
    sourceForwardRatio c*sourceAdjointRatio c=1-4*(sourceDamping c:ℂ)^2*kernelMass c*powerMass (barC c) ∧
    kernelMass (barC c)*powerMass c=kernelMass c*powerMass (barC c) := by
  have generated := actual_scalar_products observation nontrivial half
  refine ⟨generated.1,generated.2,?_⟩
  have difference : (4*(sourceDamping c:ℂ)^2)*
      (kernelMass (barC c)*powerMass c-kernelMass c*powerMass (barC c))=0 := by
    linear_combination generated.1-generated.2
  have coefficient : (4*(sourceDamping c:ℂ)^2)≠0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 (damping_ne_zero c))
  exact sub_eq_zero.mp ((mul_eq_zero.mp difference).resolve_left coefficient)

def sourcePowerCoupling : ℂ := sourceAdjointRatio c*kernelMass c/kernelMass (barC c)
def sourcePowerCayley : BurnolL2 :=
  (-2*(sourceDamping c:ℂ)*powerMass c) • generatedK (barC c)-
    sourcePowerCoupling observation half • physicalOutsideColumn c
def sourceReturnCoupling : ℂ := sourceForwardRatio c*kernelMass (barC c)/kernelMass c
def sourceColumnAdjointCayley : BurnolL2 :=
  (-2*(sourceDamping c:ℂ)*powerMass (barC c)) • fourierL2 (generatedK c)-
    sourceReturnCoupling observation half • hPowerPhysicalCorrection c

theorem actual_power_cayley_source :
    U c (hPowerPhysicalCorrection c)=sourcePowerCayley observation half := by
  have massNe := mass_ne_zero (barC c) (conjugate_generated_kernel_ne_zero observation nontrivial half.down)
  have source := source_right_inverse c (generatedK (barC c))
  rw [source_Uadj_Kbar] at source
  simp only [map_sub,map_smul,source_U_FK,smul_sub,smul_smul] at source
  rw [(actual_scalar_products observation nontrivial half).1] at source
  have coefficient : (2*(sourceDamping c:ℂ)*kernelMass (barC c))≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (damping_ne_zero c)) massNe
  have cost : (2*(sourceDamping c:ℂ)*kernelMass (barC c))*
      (sourceAdjointRatio c*kernelMass c/kernelMass (barC c))=
      2*(sourceDamping c:ℂ)*sourceAdjointRatio c*kernelMass c := by field_simp [massNe]
  have factored : (2*(sourceDamping c:ℂ)*kernelMass (barC c)) •
      (U c (hPowerPhysicalCorrection c)-sourcePowerCayley observation half)=0 := by
    unfold sourcePowerCayley sourcePowerCoupling
    rw [smul_sub,smul_sub,smul_smul,smul_smul,cost]
    linear_combination (norm := module) -source
  exact sub_eq_zero.mp ((smul_eq_zero.mp factored).resolve_left coefficient)

theorem actual_column_adjoint_cayley_source :
    sourceAdjointCayley c (physicalOutsideColumn c)=sourceColumnAdjointCayley observation half := by
  have massNe := mass_ne_zero c (generated_kernel_ne_zero observation nontrivial half.down)
  have source := source_left_inverse c (fourierL2 (generatedK c))
  rw [source_U_FK] at source
  simp only [map_sub,map_smul,source_Uadj_Kbar,smul_sub,smul_smul] at source
  rw [(actual_scalar_products observation nontrivial half).2] at source
  have coefficient : (2*(sourceDamping c:ℂ)*kernelMass c)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (damping_ne_zero c)) massNe
  have cost : (2*(sourceDamping c:ℂ)*kernelMass c)*sourceReturnCoupling observation half=
      2*(sourceDamping c:ℂ)*sourceForwardRatio c*kernelMass (barC c) := by
    unfold sourceReturnCoupling
    field_simp [massNe]
  have factored : (2*(sourceDamping c:ℂ)*kernelMass c) •
      ((U c).adjoint (physicalOutsideColumn c)-sourceColumnAdjointCayley observation half)=0 := by
    unfold sourceColumnAdjointCayley
    rw [smul_sub,smul_sub,smul_smul,smul_smul,cost]
    linear_combination (norm := module) -source
  have generated := sub_eq_zero.mp ((smul_eq_zero.mp factored).resolve_left coefficient)
  rw [sourceCayley_actual_adjoint] at generated
  exact generated

theorem actual_R_power_source :
    burnolDirectRightResolvent ((c).value/2) (hPowerPhysicalCorrection c)=
      (sourceDamping c:ℂ)⁻¹ • (sourcePowerCayley observation half-hPowerPhysicalCorrection c) := by
  have source := actual_power_cayley_source observation nontrivial half
  rw [sourceCayley_apply] at source
  have scaled := congrArg (fun x:BurnolL2 => (sourceDamping c:ℂ)⁻¹ • x) source
  rw [smul_add,smul_smul,inv_mul_cancel₀ (damping_ne_zero c),one_smul] at scaled
  rw [smul_sub]
  linear_combination (norm := module) scaled

theorem actual_R_adjoint_column_source :
    sourceAdjoint c (physicalOutsideColumn c)=
      (sourceDamping c:ℂ)⁻¹ • (sourceColumnAdjointCayley observation half-physicalOutsideColumn c) := by
  have source := actual_column_adjoint_cayley_source observation nontrivial half
  rw [sourceAdjointCayley] at source
  have scaled := congrArg (fun x:BurnolL2 => (sourceDamping c:ℂ)⁻¹ • x) source
  rw [smul_add,smul_smul,inv_mul_cancel₀ (damping_ne_zero c),one_smul] at scaled
  rw [smul_sub]
  linear_combination (norm := module) scaled

/-- Every full input retains both original outside prices and its full Pa+Q physical read. -/
theorem original_R_outside_pair_action (value : BurnolL2) :
    inner ℂ (physicalOutsideColumn c) (O (burnolDirectRightResolvent ((c).value/2) value))=
      -2*powerMass (barC c)*inner ℂ (fourierL2 (generatedK c)) (burnolEvenAmbientProjection value:BurnolL2)-
      (sourceDamping c:ℂ)⁻¹*(inner ℂ (physicalOutsideColumn c) (O value)+
        star (sourceReturnCoupling observation half)*inner ℂ (hPowerPhysicalCorrection c) (O value)) := by
  have columnRead (x : BurnolL2) : inner ℂ (physicalOutsideColumn c) (O x)=inner ℂ (physicalOutsideColumn c) x := by
    exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨physicalOutsideColumn c,outsideColumn_orthogonal c⟩ x
  have powerRead : inner ℂ (hPowerPhysicalCorrection c) (O value)=inner ℂ (hPowerPhysicalCorrection c) value := by
    exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨hPowerPhysicalCorrection c,powerCorrection_orthogonal c⟩ value
  have physicalRead : inner ℂ (fourierL2 (generatedK c)) (burnolEvenAmbientProjection value:BurnolL2)=
      inner ℂ (fourierL2 (generatedK c)) value := by
    rw [generatedK_eq_original]
    exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K c)) value
  have source := ContinuousLinearMap.adjoint_inner_left (U c) value (physicalOutsideColumn c)
  rw [sourceCayley_actual_adjoint,actual_column_adjoint_cayley_source observation nontrivial half,sourceColumnAdjointCayley,
    sourceCayley_apply,inner_sub_left,inner_smul_left,inner_smul_left,inner_add_right,inner_smul_right] at source
  have scalar : (starRingEnd ℂ) (sourceDamping c:ℂ)=(sourceDamping c:ℂ) := Complex.conj_ofReal _
  have mass : (starRingEnd ℂ) (powerMass (barC c))=powerMass (barC c) := Complex.conj_ofReal _
  simp only [map_mul,map_neg,map_ofNat,scalar,mass,starRingEnd_apply] at source
  simp only [columnRead,powerRead,physicalRead]
  apply mul_left_cancel₀ (damping_ne_zero c)
  rw [mul_sub,←mul_assoc (sourceDamping c:ℂ) (sourceDamping c:ℂ)⁻¹,
    mul_inv_cancel₀ (damping_ne_zero c),one_mul]
  linear_combination -source

end ActualSource
end OriginalKCrossParameterRAdjointSource.BPowerCayleySource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
