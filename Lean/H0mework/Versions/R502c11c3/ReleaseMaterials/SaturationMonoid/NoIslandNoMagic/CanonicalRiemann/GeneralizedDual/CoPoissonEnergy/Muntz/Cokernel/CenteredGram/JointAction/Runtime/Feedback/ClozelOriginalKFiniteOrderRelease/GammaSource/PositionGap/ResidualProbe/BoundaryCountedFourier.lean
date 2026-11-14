import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedPosition
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PairedCayleyAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedFourier

open BurnolPhysicalState OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource

open private forward_fourier fourier_adjoint observe center_zero_iff adjoint_even residual_zero_iff counting_R evenPart_source
  from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PairedCayleyAction
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedIncrement
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedPosition
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedTransport
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryQuarterRelease

local notation "F" => fourierL2
local notation "E" => BoundaryCountedInverse.cellEquiv
local notation "R" => burnolDirectRightResolventCLM
local notation "T" => sourceCayley
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "position" => HilbertInventory.positionSpace
local notation "S" => HilbertInventory.PositionField
local notation "q" => burnolUnscaledCommonGapRadius
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => BoundaryCountedPosition.expandedResidual
local notation "extend" => burnolQuarterZeroExtension
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Gq" => BurnolQuarterMeanZeroCarrier

/-- The reverse original count is the inverse Fourier transport of the actual forward cell. -/
def dualEquiv (N : Nat) (positive : 0 < N) : BurnolL2 ≃L[ℂ] BurnolL2 :=
  ((F).toContinuousLinearEquiv.trans (E N positive)).trans (F).symm.toContinuousLinearEquiv

theorem dualEquiv_apply (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    dualEquiv N positive w = DualSource.source (N+1) w - DualSource.source N w := by
  change (F).symm (E N positive (F w)) = _
  rw [BoundaryCountedInverse.cellEquiv_apply, BoundaryCountedInverse.cell_apply,
    forward_fourier, forward_fourier, ← map_sub, (F).symm_apply_apply]

theorem dualEquiv_adjoint (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    dualEquiv N positive w = (BoundaryCountedInverse.cell N).adjoint w := by
  rw [dualEquiv_apply, CountingDual.dual_eq_adjoint, CountingDual.dual_eq_adjoint, BoundaryCountedInverse.cell,
    map_sub, sub_apply]

theorem inverse_fourier_cell (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    (F).symm (E N positive w) = dualEquiv N positive ((F).symm w) := by
  change (F).symm (E N positive w) = (F).symm (E N positive (F ((F).symm w)))
  rw [(F).apply_symm_apply]

/-- The true reverse cell generates the complete frequency face as a closed image. -/
def frequencyFace (N : Nat) (positive : 0 < N) : ClosedSubmodule ℂ BurnolL2 :=
  (position).comap (dualEquiv N positive).symm.toContinuousLinearMap

theorem dual_frequency_iff (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    dualEquiv N positive w ∈ frequencyFace N positive ↔ w ∈ position := by
  change (dualEquiv N positive).symm (dualEquiv N positive w) ∈ position ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply]

def frequencyResidual (N : Nat) (positive : 0 < N) : BurnolL2 →L[ℂ] BurnolL2 :=
  (frequencyFace N positive).toSubmoduleᗮ.starProjection

private theorem frequency_zero_iff (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    frequencyResidual N positive w = 0 ↔ w ∈ frequencyFace N positive := by
  unfold frequencyResidual
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  rfl

private theorem recover_frequency (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    observe ((dualEquiv N positive).symm (frequencyResidual N positive (dualEquiv N positive w))) = observe w := by
  let frequency := frequencyFace N positive
  let projection := frequency.toSubmodule.starProjection
  let decoder := (dualEquiv N positive).symm
  have retained : decoder (projection (dualEquiv N positive w)) ∈ position :=
    (Submodule.starProjection_apply_mem frequency.toSubmodule (dualEquiv N positive w) :
      projection (dualEquiv N positive w) ∈ frequency)
  have killed : observe (decoder (projection (dualEquiv N positive w))) = 0 :=
    (center_zero_iff _).mpr retained.1
  unfold frequencyResidual
  rw [Submodule.starProjection_orthogonal]
  change observe (decoder (dualEquiv N positive w - projection (dualEquiv N positive w))) = _
  rw [map_sub, ContinuousLinearEquiv.symm_apply_apply, map_sub, killed, sub_zero]

private theorem inverse_fourier_even (w : BurnolL2) (even : reflectL2 w = w) :
    (F).symm w = F w := by
  apply (F).injective
  rw [(F).apply_symm_apply, fourierL2_fourierL2, even]

/-- The two orthogonal residuals are observations of the same actual counted field. -/
def jointResidual (N : Nat) (positive : 0 < N) : BurnolL2 →L[ℂ] (BurnolL2 × BurnolL2) :=
  (Q N).prod ((frequencyResidual N positive).comp (F).symm.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem joint_zero_iff (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    jointResidual N positive (E N positive w) = 0 ↔ w ∈ evenBurnolClosedFace q := by
  change (Q N (E N positive w), frequencyResidual N positive ((F).symm (E N positive w))) = (0,0) ↔ _
  simp only [Prod.mk.injEq]
  rw [residual_zero_iff, BoundaryCountedPosition.cell_position_iff N positive, inverse_fourier_cell N positive,
    frequency_zero_iff, dual_frequency_iff N positive]
  constructor
  · rintro ⟨physical, frequency⟩
    rw [inverse_fourier_even w (mem_evenL2ClosedFace_iff.mp physical.2)] at frequency
    exact ⟨⟨physical.1, frequency.1⟩, physical.2⟩
  · intro physical
    rw [inverse_fourier_even w (mem_evenL2ClosedFace_iff.mp physical.2)]
    exact ⟨⟨physical.1.1, physical.2⟩, ⟨physical.1.2, fourierL2_mem_evenL2ClosedFace physical.2⟩⟩

theorem joint_fibre (N : Nat) (positive : 0 < N) (left right : BurnolL2) :
    jointResidual N positive (E N positive left) = jointResidual N positive (E N positive right) ↔
      left - right ∈ evenBurnolClosedFace q := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, joint_zero_iff]

/-- Both B drives come from the actual distinct position and frequency residuals of one counted field. -/
def countedBInput (N : Nat) (positive : 0 < N) (counted : BurnolL2) : Gq × Gq :=
  let ports := jointResidual N positive counted
  (BoundaryCountedPosition.recoverQuarter N positive ports.1, observe ((dualEquiv N positive).symm ports.2))

theorem counted_B_source (N : Nat) (positive : 0 < N) (w : BurnolL2) (even : reflectL2 w = w) :
    countedBInput N positive (E N positive w) = burnolAmbientMeanZeroBlockRhs w := by
  change (BoundaryCountedPosition.recoverQuarter N positive (Q N (E N positive w)),
    observe ((dualEquiv N positive).symm (frequencyResidual N positive ((F).symm (E N positive w))))) = _
  rw [BoundaryCountedPosition.recover_expanded N positive, inverse_fourier_cell N positive,
    recover_frequency N positive, inverse_fourier_even w even]
  unfold burnolAmbientMeanZeroBlockRhs burnolAmbientMeanZeroPosition burnolAmbientMeanZeroFourier
  rw [evenPart_source w even]
  rfl

/-- The existing original B acts on the two restored drives before either correction is projected. -/
def countedCorrection (N : Nat) (positive : 0 < N) (counted : BurnolL2) : BurnolL2 :=
  let rhs := countedBInput N positive counted
  burnolAmbientEvenPart (extend (burnolMeanZeroBlockFirst rhs : Hq) + F (extend (burnolMeanZeroBlockSecond rhs : Hq)))

theorem counted_B_projection (N : Nat) (positive : 0 < N) (w : BurnolL2) (even : reflectL2 w = w) :
    (P w : BurnolL2) = w - countedCorrection N positive (E N positive w) := by
  change ((evenBurnolClosedFace (1 / 4 : ℝ)).toSubmodule.orthogonalProjectionOnto w : BurnolL2) = _
  rw [burnolEvenOrthogonalProjectionOnto_eq_resolventFormula, burnolAmbientExtendedSonineProjectionFormula,
    evenPart_source w even, countedCorrection, counted_B_source N positive w even]
  rfl

private theorem inverse_fourier_cayley (coordinate : BurnolCompletedMellinCoordinate) (w : BurnolL2) :
    (F).symm (T coordinate w) = (T (C coordinate)).adjoint ((F).symm w) := by
  apply (F).injective
  rw [(F).apply_symm_apply, fourier_adjoint, BoundaryXiSlot.conjugate_twice coordinate, (F).apply_symm_apply]

private theorem inverse_fourier_R (coordinate : BurnolCompletedMellinCoordinate) (w : BurnolL2) :
    (F).symm (R coordinate w) =
      (sourceDamping coordinate : ℂ)⁻¹ • ((T (C coordinate)).adjoint ((F).symm w) - (F).symm w) := by
  rw [← inverse_fourier_cayley, sourceCayley_apply, map_add, map_smul, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (sourceDamping_pos coordinate).ne'), one_smul]
  rfl

private theorem forward_counting_R (coordinate : BurnolCompletedMellinCoordinate) (N : Nat) (positive : 0 < N)
    (w : BurnolL2) :
    E N positive (R coordinate w) = R coordinate (E N positive w) := by
  simp only [BoundaryCountedInverse.cellEquiv_apply, BoundaryCountedInverse.cell_apply, counting_R, map_sub]

/-- The whole hidden frequency component generates an actual boundary release at the next R action. -/
theorem hidden_frequency_step (coordinate : BurnolCompletedMellinCoordinate) (N : Nat)
    (positive : 0 < N) (value : S) :
    frequencyResidual N positive ((F).symm (R coordinate (F (dualEquiv N positive (value : BurnolL2))))) =
      (sourceDamping coordinate : ℂ)⁻¹ • frequencyResidual N positive
        (dualEquiv N positive (extend (BoundaryQuarterRelease.release (C coordinate) value : Hq))) := by
  let old := (value : BurnolL2)
  let acted := (T (C coordinate)).adjoint old
  let kept := (position).toSubmodule.starProjection acted
  let released := extend (BoundaryQuarterRelease.release (C coordinate) value : Hq)
  have inside : kept ∈ position := Submodule.starProjection_apply_mem _ _
  have cut : acted - kept = released :=
    BoundaryQuarterRelease.position_cut acted (adjoint_even (C coordinate) old (mem_evenL2ClosedFace_iff.mp value.property.2))
  have oldZero : frequencyResidual N positive (dualEquiv N positive old) = 0 :=
    (frequency_zero_iff N positive _).mpr ((dual_frequency_iff N positive _).mpr value.property)
  have keptZero : frequencyResidual N positive (dualEquiv N positive kept) = 0 :=
    (frequency_zero_iff N positive _).mpr ((dual_frequency_iff N positive _).mpr inside)
  have carry : F (dualEquiv N positive old) = E N positive (F old) := by
    change F ((F).symm (E N positive (F old))) = _
    rw [(F).apply_symm_apply]
  change frequencyResidual N positive ((F).symm (R coordinate (F (dualEquiv N positive old)))) = _
  rw [carry, ← forward_counting_R coordinate N positive, inverse_fourier_cell N positive,
    inverse_fourier_R, (F).symm_apply_apply]
  change frequencyResidual N positive
    (dualEquiv N positive ((sourceDamping coordinate : ℂ)⁻¹ • (acted - old))) =
      (sourceDamping coordinate : ℂ)⁻¹ • frequencyResidual N positive (dualEquiv N positive released)
  rw [map_smul, map_smul, map_sub, map_sub, oldZero, sub_zero, ← cut, map_sub, map_sub, keptZero, sub_zero]

/-- The source of the missing frequency update is the old full field in the exact reverse image. -/
def hiddenSource (N : Nat) (positive : 0 < N) (counted : BurnolL2) : S :=
  let carrier := frequencyFace N positive
  let kept := carrier.toSubmodule.starProjection ((F).symm counted)
  ⟨(dualEquiv N positive).symm kept, Submodule.starProjection_apply_mem carrier.toSubmodule _⟩

theorem frequency_step (coordinate : BurnolCompletedMellinCoordinate) (N : Nat)
    (positive : 0 < N) (counted : BurnolL2) :
    let visible := frequencyResidual N positive ((F).symm counted)
    frequencyResidual N positive ((F).symm (R coordinate counted)) =
      frequencyResidual N positive ((F).symm (R coordinate (F visible))) +
        (sourceDamping coordinate : ℂ)⁻¹ • frequencyResidual N positive
          (dualEquiv N positive (extend (BoundaryQuarterRelease.release (C coordinate)
            (hiddenSource N positive counted) : Hq))) := by
  let carrier := frequencyFace N positive
  let kept := carrier.toSubmodule.starProjection ((F).symm counted)
  let visible := frequencyResidual N positive ((F).symm counted)
  have split : visible + kept = (F).symm counted :=
    (add_comm _ _).trans (carrier.toSubmodule.starProjection_add_starProjection_orthogonal _)
  have whole : F visible + F kept = counted := by
    rw [← map_add, split, (F).apply_symm_apply]
  have retained : dualEquiv N positive (hiddenSource N positive counted : BurnolL2) = kept :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  change frequencyResidual N positive ((F).symm (R coordinate counted)) = _
  conv_lhs => rw [← whole]
  rw [map_add, map_add, map_add, ← retained, hidden_frequency_step]

private theorem frequency_release_live (N : Nat) (positive : 0 < N) (released : Gq)
    (live : released ≠ 0) :
    frequencyResidual N positive (dualEquiv N positive (extend (released : Hq))) ≠ 0 := by
  intro erased
  have lost := (dual_frequency_iff N positive _).mp ((frequency_zero_iff N positive _).mp erased)
  have zero : observe (extend (released : Hq)) = 0 := (center_zero_iff _).mpr lost.1
  have restored : observe (extend (released : Hq)) = released := by
    change OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction (extend (released : Hq))) = _
    rw [burnolQuarterRestriction_zeroExtension]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self released
  exact live (restored.symm.trans zero)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "slot" => BoundaryAdjointDefect.nativeSlot observation nontrivial half depth

/-- The Fourier face of this actual slot is silent now and the original R action releases it. -/
theorem actual_frequency_birth (ordinal N : Nat) (positive : 0 < N) :
    let input := F (dualEquiv N positive (slot ordinal : BurnolL2))
    frequencyResidual N positive ((F).symm input) = 0 ∧
      frequencyResidual N positive ((F).symm (R c input)) ≠ 0 := by
  dsimp only
  constructor
  · rw [(F).symm_apply_apply, frequency_zero_iff, dual_frequency_iff N positive]
    exact (slot ordinal).property
  · rw [hidden_frequency_step c N positive (slot ordinal)]
    apply smul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'))
    exact frequency_release_live N positive _
      (BoundaryQuarterRelease.actual_release_live observation nontrivial half depth ordinal)

/-- The actual paired B projection reads the original counted field on its own cofinal slot. -/
theorem actual_counted_B (ordinal N : Nat) (positive : 0 < N) :
    let w := (T a).adjoint (slot ordinal : BurnolL2)
    (P w : BurnolL2) = w - countedCorrection N positive
      (BoundaryCountedTransport.countedWhole a (slot ordinal) N) := by
  let w := (T a).adjoint (slot ordinal : BurnolL2)
  have even := adjoint_even a (slot ordinal : BurnolL2)
    (mem_evenL2ClosedFace_iff.mp (slot ordinal).property.2)
  have source := counted_B_projection N positive w even
  rw [BoundaryCountedInverse.cellEquiv_apply, BoundaryCountedInverse.cell_apply] at source
  exact source

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedFourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
