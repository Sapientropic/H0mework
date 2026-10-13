import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Algebra
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.WeylPairing
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRResponse.Forcing
import Mathlib.Analysis.InnerProductSpace.Calculus
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
namespace ActionSource
export OriginalKFullSourceRResponse (completeSource pairedResponse siblingResponse sourceResidual actual_source_paired_response actual_complete_residual_forcing)
end ActionSource
local instance conservationAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q

def rawQ : BurnolL2 →L[ℂ] BurnolL2 :=
 (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp Q

def omitted : BurnolL2 →L[ℂ] BurnolL2 := ContinuousLinearMap.id ℂ BurnolL2-rawQ

def originalOutside : BurnolL2 →L[ℂ] BurnolL2 :=
 (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.starProjection

def rawPa : BurnolL2 →L[ℂ] BurnolL2 :=
 (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp OriginalKCombCofinalPaAction.E

private theorem actual_omitted_inventory (x : BurnolL2) :
 omitted x=originalOutside x+rawPa x := by
 have inside := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal (P x)
 have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal x
 have rawInside := congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) inside
 change rawPa x+rawQ x=(P x : BurnolL2) at rawInside
 change (P x : BurnolL2)+originalOutside x=x at physical
 change x-rawQ x=originalOutside x+rawPa x
 calc
  x-rawQ x=((P x : BurnolL2)+originalOutside x)-rawQ x := congrArg (fun value : BurnolL2=>value-rawQ x) physical.symm
  _ = originalOutside x+rawPa x := by rw [←rawInside]; abel

private theorem outside_inner_physical (x : BurnolL2) (y : BurnolPaAmbientCarrier) :
 inner ℂ (originalOutside x) (y : BurnolL2)=0 := by
 have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal x
 have outside : originalOutside x=x-(P x : BurnolL2) := by
  change (P x : BurnolL2)+originalOutside x=x at physical
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact physical
 rw [outside]
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_inner_eq_zero x (y : BurnolL2) y.property

private theorem omitted_gram_inventory (x y : BurnolL2) :
 inner ℂ (omitted x) (omitted y)=
 inner ℂ (originalOutside x) (originalOutside y)+
 inner ℂ (OriginalKCombCofinalPaAction.E x) (OriginalKCombCofinalPaAction.E y) := by
 have left := outside_inner_physical x (OriginalKCombCofinalPaAction.E y)
 change inner ℂ (originalOutside x) (rawPa y)=0 at left
 have right : inner ℂ (rawPa x) (originalOutside y)=0 :=
  inner_eq_zero_symm.mpr (outside_inner_physical y (OriginalKCombCofinalPaAction.E x))
 rw [actual_omitted_inventory x,actual_omitted_inventory y,inner_add_left,inner_add_right,inner_add_right,left,right]
 change inner ℂ (originalOutside x) (originalOutside y)+0+(0+inner ℂ (OriginalKCombCofinalPaAction.E x) (OriginalKCombCofinalPaAction.E y))=_
 ring

private theorem Q_normal_read (x y : BurnolL2) :
 inner ℂ (Q x) (Q y)=inner ℂ (rawQ x) y := by
 let pa := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ
 have inside : Q x ∈ pa := pa.starProjection_apply_mem (P x)
 have low := pa.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨Q x,inside⟩ (P y)
 have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left (Q x) y
 exact low.trans physical

private theorem rawQ_inner (x y : BurnolL2) :
 inner ℂ (rawQ x) y=inner ℂ x (rawQ y) := by
 have left := Q_normal_read x y
 have right := Q_normal_read y x
 calc
  _ = inner ℂ (Q x) (Q y) := left.symm
  _ = star (inner ℂ (Q y) (Q x)) := (inner_conj_symm _ _).symm
  _ = star (inner ℂ (rawQ y) x) := by rw [right]
  _ = _ := inner_conj_symm _ _

private theorem rawQ_idempotent (x : BurnolL2) : rawQ (rawQ x)=rawQ x := by
 have physical : P (rawQ x)=Q x := by
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self (Q x)
 have inside : Q x ∈ burnolCompactCoPoissonClosedRange.toSubmoduleᗮ :=
  burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection_apply_mem (P x)
 apply congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2))
 change Q (rawQ x)=Q x
 unfold OriginalKCombCofinalPaAction.Q
 change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection (P (rawQ x))=Q x
 rw [physical]
 exact burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection_eq_self_iff.mpr inside

private theorem actual_whole_gram_split (x y : BurnolL2) :
 inner ℂ x y=inner ℂ (Q x) (Q y)+inner ℂ (omitted x) (omitted y) := by
 have idempotent := rawQ_idempotent y
 have normal := Q_normal_read x y
 have self := rawQ_inner x y
 have cross : inner ℂ (rawQ x) (rawQ y)=inner ℂ (rawQ x) y := by
  rw [rawQ_inner x (rawQ y),idempotent,←rawQ_inner x y]
 change inner ℂ x y=inner ℂ (Q x) (Q y)+inner ℂ (x-rawQ x) (y-rawQ y)
 rw [inner_sub_left,inner_sub_right,inner_sub_right,normal,cross,←self]
 ring

private theorem split_forced_price (x y vx vy : BurnolL2) :
 inner ℂ x vy+inner ℂ vx y=
  inner ℂ (Q x) (Q vy)+inner ℂ (Q vx) (Q y)+
  (inner ℂ (omitted x) (omitted vy)+inner ℂ (omitted vx) (omitted y)) := by
 rw [actual_whole_gram_split x vy,actual_whole_gram_split vx y]
 ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def pairedVelocity (h : ℝ) : BurnolL2 :=
 (observation.coordinate/2-1/4) • ActionSource.siblingResponse observation nontrivial half h+
 (1/2:ℂ) • (ActionSource.completeSource observation nontrivial half h-fourierL2 (ActionSource.completeSource observation nontrivial half h))
def siblingVelocity (h : ℝ) : BurnolL2 :=
 (observation.coordinate/2-1/4) • ActionSource.pairedResponse observation nontrivial half h+
 (1/2:ℂ) • (ActionSource.completeSource observation nontrivial half h+fourierL2 (ActionSource.completeSource observation nontrivial half h))
def actualOmittedFlux (h : ℝ) : ℂ :=
 inner ℂ (omitted (ActionSource.pairedResponse observation nontrivial half h)) (omitted (siblingVelocity observation nontrivial half h))+
 inner ℂ (omitted (pairedVelocity observation nontrivial half h)) (omitted (ActionSource.siblingResponse observation nontrivial half h))

def actualOutsideFlux (h : ℝ) : ℂ :=
 inner ℂ (originalOutside (ActionSource.pairedResponse observation nontrivial half h)) (originalOutside (siblingVelocity observation nontrivial half h))+
 inner ℂ (originalOutside (pairedVelocity observation nontrivial half h)) (originalOutside (ActionSource.siblingResponse observation nontrivial half h))
def actualPaFlux (h : ℝ) : ℂ :=
 inner ℂ (OriginalKCombCofinalPaAction.E (ActionSource.pairedResponse observation nontrivial half h)) (OriginalKCombCofinalPaAction.E (siblingVelocity observation nontrivial half h))+
 inner ℂ (OriginalKCombCofinalPaAction.E (pairedVelocity observation nontrivial half h)) (OriginalKCombCofinalPaAction.E (ActionSource.siblingResponse observation nontrivial half h))

theorem actual_generated_flux_inventory (h : ℝ) :
 actualOmittedFlux observation nontrivial half h=actualOutsideFlux observation nontrivial half h+actualPaFlux observation nontrivial half h := by
 unfold actualOmittedFlux actualOutsideFlux actualPaFlux
 rw [omitted_gram_inventory,omitted_gram_inventory]
 ring

theorem actual_whole_forcing_conserves_gram (h : ℝ) :
 inner ℂ (ActionSource.pairedResponse observation nontrivial half h) (siblingVelocity observation nontrivial half h)+
 inner ℂ (pairedVelocity observation nontrivial half h) (ActionSource.siblingResponse observation nontrivial half h)=0 := by
 have forcing := ActionSource.actual_source_paired_response observation nontrivial half h
 have action := forcing.1.inner (𝕜:=ℂ) forcing.2
 have constant : (fun t : ℝ=>inner ℂ
   (burnolMultiplicativeDilation (-t/2) (ActionSource.pairedResponse observation nontrivial half h))
   (burnolMultiplicativeDilation (-t/2) (ActionSource.siblingResponse observation nontrivial half h)))=
   fun _=>inner ℂ (ActionSource.pairedResponse observation nontrivial half h) (ActionSource.siblingResponse observation nontrivial half h) :=
   funext fun t=>(burnolMultiplicativeDilation (-t/2)).inner_map_map _ _
 rw [constant] at action
 have generated := action.unique (hasDerivAt_const (0:ℝ) _)
 simpa only [pairedVelocity,siblingVelocity,neg_zero,zero_div,burnolMultiplicativeDilation_zero] using generated

theorem actual_projected_forcing_price (h : ℝ) :
 inner ℂ (Q (ActionSource.pairedResponse observation nontrivial half h)) (Q (siblingVelocity observation nontrivial half h))+
 inner ℂ (Q (pairedVelocity observation nontrivial half h)) (Q (ActionSource.siblingResponse observation nontrivial half h))=
 -actualOmittedFlux observation nontrivial half h := by
 have conserved := actual_whole_forcing_conserves_gram observation nontrivial half h
 rw [split_forced_price] at conserved
 unfold actualOmittedFlux
 linear_combination conserved

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
