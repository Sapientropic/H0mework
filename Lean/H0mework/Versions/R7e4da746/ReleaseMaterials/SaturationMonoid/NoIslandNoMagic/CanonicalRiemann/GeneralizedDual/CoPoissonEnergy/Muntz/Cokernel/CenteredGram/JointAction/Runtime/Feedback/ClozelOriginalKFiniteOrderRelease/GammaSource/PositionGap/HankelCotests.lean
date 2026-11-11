import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierHeadHistory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open Complex BurnolPhysicalState
open scoped InnerProductSpace lp

open private conjugate_twice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction

namespace Gram
export SourceGeneratedFiniteGram (Coordinates action Kernel Compatible sourceEffect)
export SourceGeneratedFiniteGram.Projection
  (gram rhs synthesis kernel_synthesis predictable predictable_readback sourceSpan)
end Gram

local notation "Seq" => ℓ²(Nat, ℂ)
local notation "F" => fourierL2
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate

local instance : CompleteSpace PositionField :=
  IsComplete.completeSpace_coe positionSpace.isClosed.isComplete

private theorem hankel_pair (c : BurnolCompletedMellinCoordinate) (a b : Seq) :
    inner ℂ a (hankel c b) = inner ℂ ((basis (d c)).repr.symm a : BurnolL2)
      (F ((basis c).repr.symm b : BurnolL2)) := by
  calc
    _ = inner ℂ ((basis (d c)).repr.symm a) ((basis (d c)).repr.symm (hankel c b)) :=
      ((basis (d c)).repr.symm.inner_map_map a (hankel c b)).symm
    _ = _ := by
      let v := F ((basis c).repr.symm b : BurnolL2)
      change inner ℂ ((basis (d c)).repr.symm a)
        ((basis (d c)).repr.symm ((basis (d c)).repr (PositionField.orthogonalProjectionOnto v))) = _
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact PositionField.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

/-- The reverse Fourier chart is the true adjoint of the original Hankel map. -/
theorem actual_hankel_adjoint (c : BurnolCompletedMellinCoordinate) :
    (hankel c).adjoint = hankel (d c) := by
  apply ContinuousLinearMap.ext
  intro a
  apply ext_inner_right ℂ
  intro b
  let u := (basis (d c)).repr.symm a
  let v := (basis c).repr.symm b
  have moved := fourierL2.inner_map_map (u : BurnolL2) (F (v : BurnolL2))
  rw [fourierL2_fourierL2, mem_evenL2ClosedFace_iff.mp v.property.2] at moved
  have reverse := hankel_pair (d c) b a
  rw [conjugate_twice] at reverse
  calc
    inner ℂ ((hankel c).adjoint a) b = inner ℂ a (hankel c b) :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = inner ℂ (u : BurnolL2) (F (v : BurnolL2)) := hankel_pair c a b
    _ = inner ℂ (F (u : BurnolL2)) (v : BurnolL2) := moved.symm
    _ = star (inner ℂ (v : BurnolL2) (F (u : BurnolL2))) := (inner_conj_symm _ _).symm
    _ = star (inner ℂ b (hankel (d c) a)) := congrArg star reverse.symm
    _ = inner ℂ (hankel (d c) a) b := inner_conj_symm _ _

private theorem single_read (a : Seq) (i : Nat) :
    inner ℂ (lp.single 2 i (1 : ℂ)) a = a i := by
  rw [lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]

/-- Each finite cotest is a literal column of the reverse original Hankel action. -/
def hankelCotest (c : BurnolCompletedMellinCoordinate) (i : Nat) : Seq :=
  hankel (d c) (lp.single 2 i (1 : ℂ))

theorem actual_hankel_cotest (c : BurnolCompletedMellinCoordinate) (a : Seq) (i : Nat) :
    inner ℂ (hankelCotest c i) a = hankel c a i := by
  rw [hankelCotest, ← actual_hankel_adjoint, ContinuousLinearMap.adjoint_inner_left]
  exact single_read _ _

def finiteCotests (c : BurnolCompletedMellinCoordinate) (n : Nat) (i : Fin n) : Seq :=
  hankelCotest c i

private theorem pulses_orthonormal (n : Nat) :
    Orthonormal ℂ (fun i : Fin n => (lp.single 2 i.val (1 : ℂ) : Seq)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [single_read, lp.single_apply, Pi.single_apply]
  by_cases same : i = j
  · subst j
    rw [if_pos rfl, if_pos rfl]
  · have distinct : i.val ≠ j.val := fun equal => same (Fin.ext equal)
    rw [if_neg distinct, if_neg same]

/-- The finite Gram kernel is eliminated by the actual reverse Hankel columns. -/
theorem actual_cotest_gram_faithful (c : BurnolCompletedMellinCoordinate) (n : Nat)
    (weight : Gram.Coordinates (Fin n))
    (silent : Gram.action (Gram.gram (finiteCotests c n)) weight = 0) : weight = 0 := by
  have material := Gram.kernel_synthesis (finiteCotests c n)
    (show weight ∈ Gram.Kernel (Gram.gram (finiteCotests c n)) from silent)
  change Gram.synthesis (finiteCotests c n) weight = 0 at material
  have values : hankel (d c) (∑ i : Fin n, weight i • lp.single 2 i.val (1 : ℂ)) = 0 := by
    rw [map_sum]
    simp only [map_smul]
    exact material
  have original := hankel_injective (d c) (values.trans (map_zero _).symm)
  ext i
  have recovered := (pulses_orthonormal n).inner_right_fintype (fun j => weight j) i
  rw [original, inner_zero_right] at recovered
  exact recovered.symm

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
