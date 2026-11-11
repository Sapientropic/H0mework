import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance debtPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
abbrev sourceA := OriginalKDecodedPaRFourFaceSourceAction.sourceA observation nontrivial half depth ordinal h H N

theorem source_Pa_retracted : paProjection (sourceA observation nontrivial half depth ordinal h H N)=
 sourceA observation nontrivial half depth ordinal h H N := by
 let a := OriginalKDecodedPaRSourceSuccessor.decodedPaSource observation nontrivial half depth ordinal h H N
 have physical : burnolEvenAmbientProjection (a.val : BurnolL2)=a.val := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self a.val
 change ((burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (burnolEvenAmbientProjection (a.val : BurnolL2)) : BurnolPaAmbientCarrier) : BurnolL2)=a.val
 rw [physical,burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mpr a.property]

theorem source_unit_zero : unitProjection (sourceA observation nontrivial half depth ordinal h H N)=0 := by
 let a := OriginalKDecodedPaRSourceSuccessor.decodedPaSource observation nontrivial half depth ordinal h H N
 have physical : burnolEvenAmbientProjection (a.val : BurnolL2)=a.val := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self a.val
 change ((burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection (burnolEvenAmbientProjection (a.val : BurnolL2)) : BurnolPaAmbientCarrier) : BurnolL2)=0
 rw [physical,Submodule.starProjection_orthogonal_apply_eq_zero a.property]
 rfl

theorem source_pa_foot : paProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)=
 (OriginalKDecodedPaRSourceEnergy.PaSourceR observation nontrivial half depth ordinal h H N : BurnolL2) := by
 have physical : burnolEvenAmbientProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)=
  OriginalKDecodedPaRSourceEnergy.physicalSourceR observation nontrivial half depth ordinal h H N :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
  (OriginalKDecodedPaRSourceEnergy.physicalSourceR observation nontrivial half depth ordinal h H N)
 change ((burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  (burnolEvenAmbientProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)) : BurnolPaAmbientCarrier) : BurnolL2)=_
 rw [physical]
 rfl

theorem source_unit_foot : unitProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)=
 (OriginalKDecodedPaRSourceEnergy.unitRankSourceR observation nontrivial half depth ordinal h H N : BurnolL2) := by
 have physical : burnolEvenAmbientProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)=
  OriginalKDecodedPaRSourceEnergy.physicalSourceR observation nontrivial half depth ordinal h H N :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
  (OriginalKDecodedPaRSourceEnergy.physicalSourceR observation nontrivial half depth ordinal h H N)
 change ((burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (burnolEvenAmbientProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)) : BurnolPaAmbientCarrier) : BurnolL2)=_
 rw [physical]
 rfl

theorem source_outside_zero : outsideProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)=0 :=
 Submodule.starProjection_orthogonal_apply_eq_zero
 (OriginalKDecodedPaRSourceEnergy.source_R_physical observation nontrivial half depth ordinal h H N)

theorem source_Pa_vector_action :
 HasDerivAt (fun t : ℝ => paProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N)))
  ((observation.coordinate/2-1/4) • paProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)+sourceA observation nontrivial half depth ordinal h H N) 0 := by
 have action := Energy.source_R_vector_action observation nontrivial half depth ordinal h H N
 have pushed := ((paProjection).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 action
 convert! pushed using 1
 change (observation.coordinate/2-1/4) • paProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)+
  sourceA observation nontrivial half depth ordinal h H N = paProjection
  ((observation.coordinate/2-1/4) • Energy.sourceR observation nontrivial half depth ordinal h H N+sourceA observation nontrivial half depth ordinal h H N)
 rw [map_add,map_smul,source_Pa_retracted]

theorem source_unit_vector_action :
 HasDerivAt (fun t : ℝ => unitProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N)))
  ((observation.coordinate/2-1/4) • unitProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)) 0 := by
 have action := Energy.source_R_vector_action observation nontrivial half depth ordinal h H N
 have pushed := ((unitProjection).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 action
 convert! pushed using 1
 change (observation.coordinate/2-1/4) • unitProjection (Energy.sourceR observation nontrivial half depth ordinal h H N) = unitProjection
  ((observation.coordinate/2-1/4) • Energy.sourceR observation nontrivial half depth ordinal h H N+sourceA observation nontrivial half depth ordinal h H N)
 rw [map_add,map_smul,source_unit_zero,add_zero]

theorem source_outside_vector_action :
 HasDerivAt (fun t : ℝ => outsideProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N))) 0 0 := by
 have action := Energy.source_R_vector_action observation nontrivial half depth ordinal h H N
 have pushed := ((outsideProjection).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 action
 convert! pushed using 1
 change 0=outsideProjection
  ((observation.coordinate/2-1/4) • Energy.sourceR observation nontrivial half depth ordinal h H N+sourceA observation nontrivial half depth ordinal h H N)
 rw [map_add,map_smul,source_outside_zero,smul_zero,zero_add]
 exact (Submodule.starProjection_orthogonal_apply_eq_zero
    (OriginalKDecodedPaRSourceSuccessor.decodedPaSource observation nontrivial half depth ordinal h H N).val.property).symm

private theorem complex_norm_source_derivative {f : ℝ → BurnolL2} {v : BurnolL2}
 (action : HasDerivAt f v 0) : HasDerivAt (fun t : ℝ => ‖f t‖^2) (2*(inner ℂ (f 0) v).re) 0 := by
 have differentiated := action.inner ℂ action
 have realDerivative := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 differentiated
 convert! realDerivative using 1
 · funext t
   have self : inner ℂ (f t) (f t)=(‖f t‖^2 : ℂ) := inner_self_eq_norm_sq_to_K _
   change ‖f t‖^2=(inner ℂ (f t) (f t)).re
   rw [self]
   simp only [← Complex.ofReal_pow,Complex.ofReal_re]
 · change 2*(inner ℂ (f 0) v).re=(inner ℂ (f 0) v+inner ℂ v (f 0)).re
   have symmetric : (inner ℂ v (f 0)).re=(inner ℂ (f 0) v).re := inner_re_symm (𝕜:=ℂ) v (f 0)
   rw [Complex.add_re,symmetric]
   ring

private theorem complex_inner_source_velocity (r a : BurnolL2) (q : ℂ) :
 (inner ℂ r (q • r+a)).re=q.re*‖r‖^2+(inner ℂ r a).re := by
 rw [inner_add_right,inner_smul_right]
 have self : inner ℂ r r=(‖r‖^2 : ℂ) := inner_self_eq_norm_sq_to_K r
 rw [self]
 simp only [← Complex.ofReal_pow,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem source_Pa_norm_debit :
 HasDerivAt (fun t : ℝ => ‖paProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N))‖^2)
  (-(2*(observation.coordinate/2-1/4).re*‖Energy.sourceRankCoefficient observation nontrivial half depth ordinal h H N • Energy.originalUnitRank observation nontrivial half‖^2)) 0 := by
 have action := complex_norm_source_derivative (source_Pa_vector_action observation nontrivial half depth ordinal h H N)
 have generated := Energy.source_Pa_unit_complete_energy observation nontrivial half depth ordinal h H N
 simp only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] at action
 rw [complex_inner_source_velocity] at action
 have e := source_pa_foot observation nontrivial half depth ordinal h H N
 change -(inner ℂ ((OriginalKDecodedPaRSourceEnergy.PaSourceR observation nontrivial half depth ordinal h H N : BurnolPaAmbientCarrier) : BurnolL2)
  (sourceA observation nontrivial half depth ordinal h H N)).re =
  (observation.coordinate/2-1/4).re *
   (‖((OriginalKDecodedPaRSourceEnergy.PaSourceR observation nontrivial half depth ordinal h H N : BurnolPaAmbientCarrier) : BurnolL2)‖^2+
    ‖Energy.sourceRankCoefficient observation nontrivial half depth ordinal h H N • Energy.originalUnitRank observation nontrivial half‖^2) at generated
 rw [←e] at generated
 convert! action using 1
 nlinarith [generated]

theorem source_unit_norm_credit :
 HasDerivAt (fun t : ℝ => ‖unitProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N))‖^2)
  (2*(observation.coordinate/2-1/4).re*‖Energy.sourceRankCoefficient observation nontrivial half depth ordinal h H N • Energy.originalUnitRank observation nontrivial half‖^2) 0 := by
 have action := complex_norm_source_derivative (source_unit_vector_action observation nontrivial half depth ordinal h H N)
 simp only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] at action
 have coefficient := complex_inner_source_velocity
  (unitProjection (Energy.sourceR observation nontrivial half depth ordinal h H N)) 0 (observation.coordinate/2-1/4)
 rw [add_zero] at coefficient
 simp only [inner_zero_right,Complex.zero_re,add_zero] at coefficient
 rw [coefficient,source_unit_foot,OriginalKDecodedPaRSourceEnergy.source_actual_unit_rank] at action
 convert! action using 1
 simp only [Submodule.coe_norm]
 ring

theorem source_outside_norm_zero_slope :
 HasDerivAt (fun t : ℝ => ‖outsideProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N))‖^2) 0 0 := by
 have action := complex_norm_source_derivative (source_outside_vector_action observation nontrivial half depth ordinal h H N)
 simp only [inner_zero_right,Complex.zero_re,mul_zero] at action
 exact action

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
