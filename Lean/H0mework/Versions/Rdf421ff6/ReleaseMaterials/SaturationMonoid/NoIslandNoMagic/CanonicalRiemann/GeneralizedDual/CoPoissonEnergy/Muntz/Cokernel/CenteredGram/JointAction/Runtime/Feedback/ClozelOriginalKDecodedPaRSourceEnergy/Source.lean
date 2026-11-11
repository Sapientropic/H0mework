import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRFourFaceSourceAction.Consumer
import Mathlib.Analysis.InnerProductSpace.Calculus
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceEnergy
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Four
export OriginalKDecodedPaRFourFaceSourceAction (ownFourFaceSource own_four_face_read own_source_ward_action sourceA receivedOwnStock received_source_ward_action received_material_own_stock)
end Four
namespace Op
export OriginalKCombPhysicalAction (R)
end Op
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

def sourceR : BurnolL2 :=
 (Four.ownFourFaceSource observation nontrivial half depth ordinal h H N).1.1+
 (Four.ownFourFaceSource observation nontrivial half depth ordinal h H N).1.2

theorem source_R_read : sourceR observation nontrivial half depth ordinal h H N =
 Op.R observation nontrivial half (Four.sourceA observation nontrivial half depth ordinal h H N) := by
 unfold sourceR
 rw [Four.own_four_face_read]
 dsimp only
 unfold OriginalKCombCofinalPaAction.paired OriginalKCombCofinalPaAction.sibling
 module

/-- The two source Ward legs generate the full resolvent vector action before energy is read. -/
theorem source_R_vector_action :
 HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2) (sourceR observation nontrivial half depth ordinal h H N))
  ((observation.coordinate/2-1/4) • sourceR observation nontrivial half depth ordinal h H N+
    Four.sourceA observation nontrivial half depth ordinal h H N) 0 := by
 have ward := Four.own_source_ward_action observation nontrivial half depth ordinal h H N
 have generated := ward.1.add ward.2
 convert! generated using 1
 · funext t
   unfold sourceR
   rw [map_add]
   rfl
 · rw [Four.own_four_face_read]
   dsimp only
   unfold sourceR
   rw [Four.own_four_face_read]
   dsimp only
   module

/-- Unitarity forces this source's own generated norm-square derivative to vanish; no energy cancellation is an input. -/
theorem source_R_inner_energy :
 inner ℂ (sourceR observation nontrivial half depth ordinal h H N)
  ((observation.coordinate/2-1/4) • sourceR observation nontrivial half depth ordinal h H N+
    Four.sourceA observation nontrivial half depth ordinal h H N) +
 inner ℂ ((observation.coordinate/2-1/4) • sourceR observation nontrivial half depth ordinal h H N+
    Four.sourceA observation nontrivial half depth ordinal h H N)
  (sourceR observation nontrivial half depth ordinal h H N) = 0 := by
 have action := source_R_vector_action observation nontrivial half depth ordinal h H N
 have differentiated := action.inner ℂ action
 have constant : (fun t : ℝ => inner ℂ
  (burnolMultiplicativeDilation (-t/2) (sourceR observation nontrivial half depth ordinal h H N))
  (burnolMultiplicativeDilation (-t/2) (sourceR observation nontrivial half depth ordinal h H N))) =
  fun _ : ℝ => inner ℂ (sourceR observation nontrivial half depth ordinal h H N)
   (sourceR observation nontrivial half depth ordinal h H N) := by
  funext t
  exact (burnolMultiplicativeDilation (-t/2)).inner_map_map _ _
 rw [constant] at differentiated
 simpa only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] using
  differentiated.unique (hasDerivAt_const (0 : ℝ) _)

theorem source_R_energy :
 (inner ℂ (sourceR observation nontrivial half depth ordinal h H N)
  (Four.sourceA observation nontrivial half depth ordinal h H N)).re =
 -((observation.coordinate/2-1/4).re * ‖sourceR observation nontrivial half depth ordinal h H N‖^2) := by
 let r := sourceR observation nontrivial half depth ordinal h H N
 let a := Four.sourceA observation nontrivial half depth ordinal h H N
 let q := observation.coordinate/2-1/4
 have self : inner ℂ r r=(‖r‖^2 : ℂ) := inner_self_eq_norm_sq_to_K r
 have reverse : inner ℂ a r=star (inner ℂ r a) := (inner_conj_symm (𝕜:=ℂ) a r).symm
 have generated := source_R_inner_energy observation nontrivial half depth ordinal h H N
 change inner ℂ r (q • r+a)+inner ℂ (q • r+a) r=0 at generated
 rw [inner_add_right,inner_smul_right,inner_add_left,inner_smul_left,self,reverse] at generated
 have realGenerated := congrArg Complex.re generated
 simp only [← Complex.ofReal_pow,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
  mul_zero,sub_zero,Complex.star_def,Complex.conj_re,Complex.zero_re] at realGenerated
 change (inner ℂ r a).re=-(q.re*‖r‖^2)
 linarith

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceEnergy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
