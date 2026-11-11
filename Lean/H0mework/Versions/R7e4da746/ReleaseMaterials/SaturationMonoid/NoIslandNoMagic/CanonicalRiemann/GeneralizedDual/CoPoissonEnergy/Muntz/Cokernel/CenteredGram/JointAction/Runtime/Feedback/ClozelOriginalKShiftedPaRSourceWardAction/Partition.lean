import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKShiftedPaRSourceWardAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Budget
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Split
export OriginalKPaUnitOutsideSourceDebtAction (Branches paProjection unitProjection outsideProjection splitProjection fullSplitBudget split_projection_full_budget)
end Split

private theorem complex_norm_source_derivative {f : ℝ → BurnolL2} {v : BurnolL2} {point : ℝ}
 (action : HasDerivAt f v point) : HasDerivAt (fun t : ℝ => ‖f t‖^2) (2*(inner ℂ (f point) v).re) point := by
 have differentiated := action.inner ℂ action
 have realDerivative := Complex.reCLM.hasFDerivAt.comp_hasDerivAt point differentiated
 convert! realDerivative using 1
 · funext t
   have self : inner ℂ (f t) (f t)=(‖f t‖^2 : ℂ) := inner_self_eq_norm_sq_to_K _
   change ‖f t‖^2=(inner ℂ (f t) (f t)).re
   rw [self]
   simp only [← Complex.ofReal_pow,Complex.ofReal_re]
 · change 2*(inner ℂ (f point) v).re=(inner ℂ (f point) v+inner ℂ v (f point)).re
   have symmetric : (inner ℂ v (f point)).re=(inner ℂ (f point) v).re := inner_re_symm (𝕜:=ℂ) v (f point)
   rw [Complex.add_re,symmetric]
   ring

private theorem complex_inner_source_velocity (r a : BurnolL2) (q : ℂ) :
 (inner ℂ r (q • r+a)).re=q.re*‖r‖^2+(inner ℂ r a).re := by
 rw [inner_add_right,inner_smul_right]
 have self : inner ℂ r r=(‖r‖^2 : ℂ) := inner_self_eq_norm_sq_to_K r
 rw [self]
 simp only [← Complex.ofReal_pow,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

def shiftedSplit (shift : ℝ) : Split.Branches := Split.splitProjection (shiftedR observation nontrivial half depth ordinal h H N shift)
def shiftedSourceSplit (shift : ℝ) : Split.Branches := Split.splitProjection (shiftedA observation nontrivial half depth ordinal h H N shift)

theorem source_projection_Ward (projection : BurnolL2 →L[ℂ] BurnolL2) (shift : ℝ) :
 HasDerivAt (fun t : ℝ => projection (shiftedR observation nontrivial half depth ordinal h H N t))
  ((observation.coordinate/2-1/4) • projection (shiftedR observation nontrivial half depth ordinal h H N shift)+
   projection (shiftedA observation nontrivial half depth ordinal h H N shift)) shift := by
 have action := source_Ward_at_shift observation nontrivial half depth ordinal h H N shift
 have pushed := (projection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt shift action
 convert! pushed using 1
 change (observation.coordinate/2-1/4) • projection (shiftedR observation nontrivial half depth ordinal h H N shift)+
   projection (shiftedA observation nontrivial half depth ordinal h H N shift)=
 projection (shiftedVelocity observation nontrivial half depth ordinal h H N shift)
 exact (map_add projection _ _).trans (congrArg (fun value => value+projection (shiftedA observation nontrivial half depth ordinal h H N shift))
  (map_smul projection _ _)) |>.symm

def projectedDebtDensity (projection : BurnolL2 →L[ℂ] BurnolL2) (shift : ℝ) : ℝ :=
 2*((observation.coordinate/2-1/4).re*‖projection (shiftedR observation nontrivial half depth ordinal h H N shift)‖^2+
 (inner ℂ (projection (shiftedR observation nontrivial half depth ordinal h H N shift))
   (projection (shiftedA observation nontrivial half depth ordinal h H N shift))).re)

theorem source_projected_norm_derivative (projection : BurnolL2 →L[ℂ] BurnolL2) (shift : ℝ) :
 HasDerivAt (fun t : ℝ => ‖projection (shiftedR observation nontrivial half depth ordinal h H N t)‖^2)
  (projectedDebtDensity observation nontrivial half depth ordinal h H N projection shift) shift := by
 have action := complex_norm_source_derivative (source_projection_Ward observation nontrivial half depth ordinal h H N projection shift)
 rw [complex_inner_source_velocity] at action
 exact action

theorem shifted_full_source_budget (shift : ℝ) :
 Split.fullSplitBudget (shiftedSplit observation nontrivial half depth ordinal h H N shift)=
 ‖Energy.sourceR observation nontrivial half depth ordinal h H N‖^2 := by
 rw [shiftedSplit,Split.split_projection_full_budget]
 exact congrArg (fun value : ℝ => value^2) ((burnolMultiplicativeDilation (-shift/2)).norm_map _)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
