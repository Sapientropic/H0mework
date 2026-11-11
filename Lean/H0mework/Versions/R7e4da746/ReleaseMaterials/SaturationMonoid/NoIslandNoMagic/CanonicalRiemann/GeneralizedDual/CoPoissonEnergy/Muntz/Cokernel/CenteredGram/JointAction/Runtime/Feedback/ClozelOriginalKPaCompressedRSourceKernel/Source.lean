import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKShiftedPaRSourceWardAction.Consumer
import Mathlib.Analysis.InnerProductSpace.Calculus
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCompressedRSourceKernel
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Op
export OriginalKCombPhysicalAction (R)
end Op
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (source : BurnolL2)

def sourceR : BurnolL2 := Op.R observation nontrivial half source

/-- The actual original resolvent source action generates its Ward vector for every whole source, before any Pa projection or kernel target. -/
theorem source_R_vector_action :
 HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2) (sourceR observation nontrivial half source))
  ((observation.coordinate/2-1/4) • sourceR observation nontrivial half source+source) 0 := by
 unfold sourceR
 rw [OriginalKCombCofinalRAction.original_R_direct]
 exact burnolDirectRightResolventOrbit_hasDerivAt _
  (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) source

/-- Unitarity forces this source's own generated norm-square derivative to vanish; no energy cancellation is an input. -/
theorem source_R_inner_energy :
 inner ℂ (sourceR observation nontrivial half source)
  ((observation.coordinate/2-1/4) • sourceR observation nontrivial half source+
    source) +
 inner ℂ ((observation.coordinate/2-1/4) • sourceR observation nontrivial half source+
    source)
  (sourceR observation nontrivial half source) = 0 := by
 have action := source_R_vector_action observation nontrivial half source
 have differentiated := action.inner ℂ action
 have constant : (fun t : ℝ => inner ℂ
  (burnolMultiplicativeDilation (-t/2) (sourceR observation nontrivial half source))
  (burnolMultiplicativeDilation (-t/2) (sourceR observation nontrivial half source))) =
  fun _ : ℝ => inner ℂ (sourceR observation nontrivial half source)
   (sourceR observation nontrivial half source) := by
  funext t
  exact (burnolMultiplicativeDilation (-t/2)).inner_map_map _ _
 rw [constant] at differentiated
 simpa only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] using
  differentiated.unique (hasDerivAt_const (0 : ℝ) _)

theorem source_R_energy :
 (inner ℂ (sourceR observation nontrivial half source)
  (source)).re =
 -((observation.coordinate/2-1/4).re * ‖sourceR observation nontrivial half source‖^2) := by
 let r := sourceR observation nontrivial half source
 let a := source
 let q := observation.coordinate/2-1/4
 have self : inner ℂ r r=(‖r‖^2 : ℂ) := inner_self_eq_norm_sq_to_K r
 have reverse : inner ℂ a r=star (inner ℂ r a) := (inner_conj_symm (𝕜:=ℂ) a r).symm
 have generated := source_R_inner_energy observation nontrivial half source
 change inner ℂ r (q • r+a)+inner ℂ (q • r+a) r=0 at generated
 rw [inner_add_right,inner_smul_right,inner_add_left,inner_smul_left,self,reverse] at generated
 have realGenerated := congrArg Complex.re generated
 simp only [← Complex.ofReal_pow,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
  mul_zero,sub_zero,Complex.star_def,Complex.conj_re,Complex.zero_re] at realGenerated
 change (inner ℂ r a).re=-(q.re*‖r‖^2)
 linarith

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCompressedRSourceKernel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
