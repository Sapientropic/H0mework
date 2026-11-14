import H0mework.Realization.Operations.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.ExpandedGap
import H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.PaBoundaryCommutator

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.PhysicalPortDefect

open SourceGeneratedScalarDifferentialResidual SourceGeneratedObservationAction
open scoped InnerProductSpace

private abbrev physicalGap : Submodule ℂ BurnolL2 :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation
local notation "P" => burnolEvenAmbientProjection

local instance : CompleteSpace physicalGap :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete.completeSpace_coe

variable {G : Type*} [AddCommGroup G] [Module ℂ G]

/-- A physical-only observation retaining a nonzero covector has a genuine original-R
    action defect. The whole inward clock would otherwise force the retained column to vanish. -/
theorem nonzero (coordinate : BurnolCompletedMellinCoordinate) (read : BurnolL2 →ₗ[ℂ] G)
    (column : BurnolL2) (columnLive : column ≠ 0)
    (physical : ∀ value, P value = 0 → read value = 0)
    (cotest : G →ₗ[ℂ] ℂ) (readsColumn : ∀ value, cotest (read value) = inner ℂ column value) :
    actionDefect (R coordinate).toLinearMap read ≠ 0 := by
  intro vanished
  have invariant := (actionDefect_eq_zero_iff (R coordinate).toLinearMap read).mp vanished
  have powers (value : BurnolL2) (initial : read value = 0) (n : ℕ) :
      read (((R coordinate)^n) value) = 0 := by
    induction n with
    | zero => rw [pow_zero]; exact initial
    | succ n prior =>
      rw [pow_succ']
      change read ((R coordinate) (((R coordinate)^n) value)) = 0
      have held : canonicalResidual read ((R coordinate) (((R coordinate)^n) value)) = 0 :=
        invariant (LinearMap.mem_ker.mpr prior)
      exact (canonicalResidual_eq_zero_iff read _).mp held
  have shifted (h : ℝ) (positive : 0 < h) : D (h/2) column ∈ physicalGap := by
    rw [← physicalGap.orthogonal_orthogonal]
    apply (physicalGapᗮ.mem_orthogonal' _).mpr
    intro value outside
    have projected : P value = 0 := physicalGap.orthogonalProjectionOnto_apply_of_mem_orthogonal outside
    have quiet (n : ℕ) : (innerSL ℂ column) (((R coordinate)^(n+1)) value) = 0 := by
      change inner ℂ column _ = 0
      rw [← readsColumn, powers value (physical value projected), map_zero]
    have source := DilationFromPowers.observed_inward_zero (innerSL ℂ column) coordinate value quiet h positive
    have reverse : D (h/2) (D (-h/2) value) = value := by
      rw [burnolMultiplicativeDilation_add, show h/2 + -h/2 = 0 by ring,
        burnolMultiplicativeDilation_zero]
    have conserved := (D (h/2)).inner_map_map column (D (-h/2) value)
    rw [reverse] at conserved
    exact conserved.trans source
  have zero : fourierL2.symm column = 0 := by
    apply ExpandedGap.zero_of_all_inward_frequency_gap
    intro h positive
    rw [fourierL2_burnolMultiplicativeDilation, neg_div, neg_neg, fourierL2.apply_symm_apply]
    exact (shifted h positive).1.1
  exact columnLive (by simpa only [fourierL2.apply_symm_apply, map_zero] using congrArg fourierL2 zero)

end OriginalRSourceJointContact.OutsideHistory.PhysicalPortDefect
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
