import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Source.PowerWave
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Gram

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local instance cayleyPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def sourceAdjointCayley (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  value+(sourceDamping c:ℂ) • sourceAdjoint c value

theorem sourceDamping_pos (c : BurnolCompletedMellinCoordinate) : 0<sourceDamping c := by
  exact sub_pos.mpr c.rightHalf

theorem sourceCayley_apply (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceCayley c value=value+(sourceDamping c:ℂ) • burnolDirectRightResolvent (c.value/2) value := rfl

private theorem rightQuarter (c : BurnolCompletedMellinCoordinate) : 1/4<(c.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [c.rightHalf]
private theorem starRightQuarter (c : BurnolCompletedMellinCoordinate) : 1/4<(star c.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [c.rightHalf]
private theorem outside_eq (value : BurnolL2) :
    outside value=value-(burnolEvenAmbientProjection value:BurnolL2) :=
  Submodule.starProjection_orthogonal_val value
private theorem physical_outside_zero (v : BurnolPaAmbientCarrier) : outside (v:BurnolL2)=0 := by
  rw [outside_eq]
  have same : burnolEvenAmbientProjection (v:BurnolL2)=v := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [same,sub_self]

private theorem original_R_real_energy (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    2*(inner ℂ value (burnolDirectRightResolvent (c.value/2) value)).re=
      -sourceDamping c*‖burnolDirectRightResolvent (c.value/2) value‖^2 := by
  have generated := burnolDirectRightResolvent_gram (c.value/2) (c.value/2)
    (rightQuarter c) (rightQuarter c) value
  have coefficient : c.value/2+star (c.value/2)-1/2=(sourceDamping c:ℂ) := by
    change c.value/2+(starRingEnd ℂ) (c.value/2)-1/2=(sourceDamping c:ℂ)
    rw [Complex.add_conj]
    norm_num [sourceDamping]
    ring
  rw [coefficient,inner_self_eq_norm_sq_to_K] at generated
  change inner ℂ value (burnolDirectRightResolvent (c.value/2) value)+
    (starRingEnd ℂ) (inner ℂ value (burnolDirectRightResolvent (c.value/2) value))=
      -(sourceDamping c:ℂ)*(‖burnolDirectRightResolvent (c.value/2) value‖:ℂ)^2 at generated
  rw [Complex.add_conj] at generated
  exact_mod_cast generated

/-- The source Gram law, with its exact real coefficient, makes the full Cayley action isometric. -/
theorem sourceCayley_norm (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ‖sourceCayley c value‖=‖value‖ := by
  rw [sourceCayley_apply]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_add_sq (𝕜:=ℂ),inner_smul_right,norm_smul]
  change ‖value‖^2+2*((sourceDamping c:ℂ)*inner ℂ value
    (burnolDirectRightResolvent (c.value/2) value)).re+
      (‖(sourceDamping c:ℂ)‖*‖burnolDirectRightResolvent (c.value/2) value‖)^2=‖value‖^2
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sourceDamping_pos c),mul_pow]
  linear_combination (sourceDamping c)*original_R_real_energy c value

theorem sourceCayley_inner (c : BurnolCompletedMellinCoordinate) (x y : BurnolL2) :
    inner ℂ (sourceCayley c x) (sourceCayley c y)=inner ℂ x y := by
  let action : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
    { (sourceCayley c).toLinearMap with norm_map' := sourceCayley_norm c }
  exact action.inner_map_map x y

/-- This adjoint is the actual Rplus source, with the same real damping. -/
theorem sourceCayley_actual_adjoint (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (sourceCayley c).adjoint value=sourceAdjointCayley c value := by
  apply ext_inner_right ℂ
  intro test
  rw [ContinuousLinearMap.adjoint_inner_left,sourceCayley_apply,sourceAdjointCayley,
    inner_add_right,inner_smul_right,inner_add_left,inner_smul_left]
  have actual := OriginalKCompactAdjointRSource.actual_original_R_adjoint (c.value/2)
    (rightQuarter c) value test
  simp only [star_div₀,star_ofNat] at actual
  change inner ℂ value (burnolDirectRightResolvent (c.value/2) test)=inner ℂ (sourceAdjoint c value) test at actual
  rw [actual]
  have realScalar : (starRingEnd ℂ) (sourceDamping c:ℂ)=(sourceDamping c:ℂ) := Complex.conj_ofReal _
  rw [realScalar]

/-- Fourier reverses the genuine resolvent direction; its norm transfers the full adjoint action. -/
theorem sourceAdjointCayley_norm (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ‖sourceAdjointCayley c value‖=‖value‖ := by
  have damping : sourceDamping (barC c)=sourceDamping c := by
    simp only [sourceDamping,OriginalPrimitiveRankBalance.conjugateCoordinate,Complex.star_def,Complex.conj_re]
  have actual := FiniteMobiusResolventFlux.fourier_R (star c.value/2) (starRightQuarter c) (fourierL2.symm value)
  rw [fourierL2.apply_symm_apply] at actual
  have source : sourceAdjointCayley c value=fourierL2 (sourceCayley (barC c) (fourierL2.symm value)) := by
    rw [sourceCayley_apply,map_add,map_smul,fourierL2.apply_symm_apply,damping]
    change value+(sourceDamping c:ℂ) • sourceAdjoint c value=
      value+(sourceDamping c:ℂ) • fourierL2 (burnolDirectRightResolvent (star c.value/2) (fourierL2.symm value))
    rw [actual]
    rfl
  rw [source,fourierL2.norm_map,sourceCayley_norm,fourierL2.symm.norm_map]

/-- The forward projected loss is the full Fourier-K/source-B-power vector cost. -/
theorem physical_forward_exact_loss (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    ‖(v:BurnolL2)‖^2-
      ‖(v:BurnolL2)+(sourceDamping c:ℂ) •
        (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (v:BurnolL2)):BurnolL2)‖^2=
      4*(sourceDamping c)^2*‖hPowerPhysicalCorrection (barC c)‖^2*
        ‖inner ℂ (fourierL2 (generatedK c)) (v:BurnolL2)‖^2 := by
  have projected : (burnolEvenAmbientProjection (sourceCayley c v):BurnolL2)=
      (v:BurnolL2)+(sourceDamping c:ℂ) •
        (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (v:BurnolL2)):BurnolL2) := by
    change burnolEvenAmbientProjectionEndomorphism (sourceCayley c v)=_
    rw [sourceCayley_apply,map_add,map_smul]
    have same : burnolEvenAmbientProjection (v:BurnolL2)=v := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    change (burnolEvenAmbientProjection (v:BurnolL2):BurnolL2)+_=_
    rw [same]
    rfl
  have outsideAction : outside (sourceCayley c v)=
      (sourceDamping c:ℂ) • ((-2*inner ℂ (fourierL2 (generatedK c)) (v:BurnolL2)) • physicalOutsideColumn c) := by
    rw [sourceCayley_apply,map_add,map_smul,physical_outside_zero,zero_add,original_R_physical_outside_source]
  have cost : ‖outside (sourceCayley c v)‖^2=
      4*(sourceDamping c)^2*‖hPowerPhysicalCorrection (barC c)‖^2*
        ‖inner ℂ (fourierL2 (generatedK c)) (v:BurnolL2)‖^2 := by
    rw [outsideAction]
    simp only [norm_smul,norm_mul,norm_neg,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (sourceDamping_pos c),mul_pow,physicalOutsideColumn,fourierL2.symm.norm_map]
    ring
  have balance := Submodule.norm_sq_eq_add_norm_sq_starProjection (sourceCayley c v)
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  change ‖sourceCayley c v‖^2=‖(burnolEvenAmbientProjection (sourceCayley c v):BurnolL2)‖^2+
    ‖outside (sourceCayley c v)‖^2 at balance
  rw [sourceCayley_norm,projected,cost] at balance
  linarith

/-- The independent adjoint loss retains the conjugate K direction and its whole B-power cost. -/
theorem physical_adjoint_exact_loss (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    ‖(v:BurnolL2)‖^2-
      ‖(v:BurnolL2)+(sourceDamping c:ℂ) •
        (burnolEvenAmbientProjection (sourceAdjoint c v):BurnolL2)‖^2=
      4*(sourceDamping c)^2*‖hPowerPhysicalCorrection c‖^2*
        ‖inner ℂ (generatedK (barC c)) (v:BurnolL2)‖^2 := by
  have amplitude : physicalAmplitude c v=-2*inner ℂ (generatedK (barC c)) (v:BurnolL2) := by
    rw [←outsidePhysicalSource_read,outsidePhysicalSource,inner_smul_left]
    change star (-2:ℂ)*inner ℂ (generatedK (barC c)) (v:BurnolL2)=_
    simp only [star_neg,star_ofNat]
  have projected : (burnolEvenAmbientProjection (sourceAdjointCayley c v):BurnolL2)=
      (v:BurnolL2)+(sourceDamping c:ℂ) • (burnolEvenAmbientProjection (sourceAdjoint c v):BurnolL2) := by
    change burnolEvenAmbientProjectionEndomorphism (sourceAdjointCayley c v)=_
    rw [sourceAdjointCayley,map_add,map_smul]
    have same : burnolEvenAmbientProjection (v:BurnolL2)=v := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    change (burnolEvenAmbientProjection (v:BurnolL2):BurnolL2)+_=_
    rw [same]
    rfl
  have outsideAction : outside (sourceAdjointCayley c v)=
      (sourceDamping c:ℂ) • ((-2*inner ℂ (generatedK (barC c)) (v:BurnolL2)) • hPowerPhysicalCorrection c) := by
    rw [sourceAdjointCayley,map_add,map_smul,physical_outside_zero,zero_add,outside_eq,
      physical_adjoint_full_defect,amplitude]
  have cost : ‖outside (sourceAdjointCayley c v)‖^2=
      4*(sourceDamping c)^2*‖hPowerPhysicalCorrection c‖^2*
        ‖inner ℂ (generatedK (barC c)) (v:BurnolL2)‖^2 := by
    rw [outsideAction]
    simp only [norm_smul,norm_mul,norm_neg,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (sourceDamping_pos c),mul_pow]
    ring
  have balance := Submodule.norm_sq_eq_add_norm_sq_starProjection (sourceAdjointCayley c v)
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  change ‖sourceAdjointCayley c v‖^2=‖(burnolEvenAmbientProjection (sourceAdjointCayley c v):BurnolL2)‖^2+
    ‖outside (sourceAdjointCayley c v)‖^2 at balance
  rw [sourceAdjointCayley_norm,projected,cost] at balance
  linarith

/-- The next physical field has the complete incoming outside vector deducted before energy is read. -/
theorem original_R_physical_incoming_source (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2)
      (burnolEvenAmbientProjection value:BurnolL2)):BurnolL2)=
    (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) value):BurnolL2)+
      (2*inner ℂ (hPowerPhysicalCorrection c) (outside value)) • generatedK (barC c) := by
  have full : value=(burnolEvenAmbientProjection value:BurnolL2)+outside value := by rw [outside_eq];module
  have action := congrArg burnolEvenAmbientProjectionEndomorphism
    (congrArg (burnolDirectRightResolventCLM c) full)
  rw [map_add,map_add] at action
  change (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) value):BurnolL2)=
    (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2)
      (burnolEvenAmbientProjection value:BurnolL2)):BurnolL2)+
    (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (outside value)):BurnolL2) at action
  rw [original_R_outside_physical_generatedK] at action
  linear_combination (norm := module) -action

/-- This exact energy equation is on the original raw n to n+1 occurrence, with full incoming stock. -/
theorem actual_physical_incoming_energy (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
    let raw := OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal
    let next := OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)
    ‖(burnolEvenAmbientProjection raw:BurnolL2)‖^2-
      ‖(burnolEvenAmbientProjection raw:BurnolL2)+
        (sourceDamping c:ℂ) • (burnolEvenAmbientProjection next:BurnolL2)+
        (2*(sourceDamping c:ℂ)*inner ℂ (hPowerPhysicalCorrection c) (outside raw)) • generatedK (barC c)‖^2=
      4*(sourceDamping c)^2*‖hPowerPhysicalCorrection (barC c)‖^2*
        ‖inner ℂ (fourierL2 (generatedK c)) (burnolEvenAmbientProjection raw:BurnolL2)‖^2 := by
  dsimp only
  let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let raw := OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal
  have energy := physical_forward_exact_loss c (burnolEvenAmbientProjection raw)
  rw [original_R_physical_incoming_source] at energy
  have successor : burnolDirectRightResolvent (c.value/2) raw=
      OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1) := by
    rw [OriginalKCombFirstFullSourceDynamics.raw_successor,OriginalKCombCofinalRAction.original_R_direct]
    rfl
  rw [successor] at energy
  have vector : (burnolEvenAmbientProjection raw:BurnolL2)+
      (sourceDamping c:ℂ) • ((burnolEvenAmbientProjection
        (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)):BurnolL2)+
        (2*inner ℂ (hPowerPhysicalCorrection c) (outside raw)) • generatedK (barC c))=
      (burnolEvenAmbientProjection raw:BurnolL2)+
        (sourceDamping c:ℂ) • (burnolEvenAmbientProjection
          (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)):BurnolL2)+
        (2*(sourceDamping c:ℂ)*inner ℂ (hPowerPhysicalCorrection c) (outside raw)) • generatedK (barC c) := by module
  rw [vector] at energy
  exact energy

end OriginalKCrossParameterRAdjointSource.CayleyEnergySource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
