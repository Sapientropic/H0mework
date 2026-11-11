import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCountedPaSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology BigOperators
namespace PA
export OriginalKCombCofinalPaAction (E Q invisible invisible_mem wholePa_normal_read)
end PA
namespace Native
export OriginalKCombFirstFullSourceDynamics (raw raw_successor input next_pair raw_xi_source)
end Native
namespace Reentry
export OriginalKDirectRCofinalReentrySourceAction
  (sourceReentryVector sourceReentryAction full_invisible_reentry
   source_unit_invisible_pair_Q outside_P_R_E_zero)
end Reentry
namespace LogSource
export OriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
  (sourceLogCoefficient correction_source_log_action)
end LogSource
local notation "R" => burnolDirectRightResolventCLM
local notation "bc" => burnolPaResolventSourceCoefficient
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
open private reverse_resolvent from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent

/-- The whole original counting programme retains its original integer and continuous inventory. -/
def counted (N : ℕ) (value : BurnolL2) : BurnolL2 := DualSource.source N value

theorem counted_inventory (N : ℕ) (value : BurnolL2) :
    counted N value = (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 n value) -
      ∫ a : ℝ in Ioc 0 (N:ℝ), ContinuousChannels.channel 1 a value := rfl

private theorem counted_R (N : ℕ) (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    counted N (R c value)=R c (counted N value) := by
  have actual := reverse_resolvent N (barC c) value
  change DualSource.source N (burnolDirectRightResolvent (star (barC c).value/2) value)=
    burnolDirectRightResolvent (star (barC c).value/2) (DualSource.source N value) at actual
  change DualSource.source N (burnolDirectRightResolvent (c.value/2) value)=
    burnolDirectRightResolvent (c.value/2) (DualSource.source N value)
  simpa only [OriginalPrimitiveRankBalance.conjugateCoordinate, star_star] using actual

/-- The complete original source supplies this shell; no future Pa field is supplied. -/
def correction (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolPaAmbientCarrier :=
  sourceVolterraPhysical c (burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E value)))

theorem correction_integral (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    correction c value = ∫ u : ℝ in Icc (1/4:ℝ) 4,
      volterraSourceDensity c (burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E value))) u •
        volterraPhysicalShell c u := rfl

theorem correction_mem (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    correction c value ∈ burnolCompactCoPoissonClosedRange := sourceVolterraPhysical_mem c _

private theorem correction_original (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    correction c value=burnolPaSourceCorrection c ⟨PA.E value,Submodule.starProjection_apply_mem _ _⟩ :=
  sourceVolterraPhysical_original_correction c _ (Submodule.starProjection_apply_mem _ _)

private theorem correction_coefficient (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    bc c (correction c value)=LogSource.sourceLogCoefficient c (PA.E value) :=
  (congrArg (bc c) (correction_original c value)).trans
    (LogSource.correction_source_log_action c (PA.E value) (Submodule.starProjection_apply_mem _ _))

private theorem E_of_mem (value : BurnolPaAmbientCarrier)
    (inside : value∈burnolCompactCoPoissonClosedRange) : PA.E (value:BurnolL2)=value := by
  change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (burnolEvenAmbientProjection (value:BurnolL2))=value
  have physical : burnolEvenAmbientProjection (value:BurnolL2)=value :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [physical]
  exact Submodule.starProjection_eq_self_iff.mpr inside

theorem full_source (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    R c value=(correction c value:BurnolL2)+bc c (PA.E value) • burnolUnitTailResponse c 4+
      R c (PA.invisible value) := by
  have actual := congrArg (fun p : BurnolPaAmbientCarrier=>(p:BurnolL2)) (correction_original c value)
  change (correction c value:BurnolL2)=R c (PA.E value:BurnolL2)-
    bc c (PA.E value) • burnolUnitTailResponse c 4 at actual
  unfold PA.invisible
  rw [map_sub]
  linear_combination (norm:=module) -actual

section OriginalZero
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "unit" => burnolUnitTailResponse c 4
local notation "Funit" => fourierL2 (burnolUnitTailResponse (barC c) 4)

include nontrivial in
theorem full_Pa_source (value : BurnolL2) :
    PA.E (R c value)=correction c value+bc c (PA.E value) • PA.E unit+
      inner ℂ Funit (PA.Q value:BurnolL2) • (Reentry.sourceReentryVector c:BurnolPaAmbientCarrier) := by
  have actual := congrArg PA.E (full_source c value)
  rw [map_add,map_add,map_smul,E_of_mem _ (correction_mem c value)] at actual
  have reentry := Reentry.full_invisible_reentry c value
  change PA.E (R c (PA.invisible value))=
    inner ℂ Funit (PA.invisible value) • (Reentry.sourceReentryVector c:BurnolPaAmbientCarrier) at reentry
  rw [Reentry.source_unit_invisible_pair_Q observation nontrivial half.down] at reentry
  rw [reentry] at actual
  exact actual

/-- The counted field is a new effect of the actual original input, not a new member of the old R actor. -/
def actualField (depth ordinal N : ℕ) : BurnolL2 :=
  counted N (Native.raw observation nontrivial half depth ordinal)

theorem actual_input_inventory (depth ordinal N : ℕ) :
    actualField observation nontrivial half depth ordinal N=
      counted N (Native.input observation nontrivial half depth ordinal).1+
        counted N (Native.input observation nontrivial half depth ordinal).2 := by
  unfold actualField Native.raw counted
  simp only [CountingDual.dual_eq_adjoint,map_add]

theorem actual_counted_next (depth ordinal N : ℕ) :
    actualField observation nontrivial half depth (ordinal+1) N=
      R c (actualField observation nontrivial half depth ordinal N) := by
  unfold actualField
  rw [Native.raw_successor,OriginalKCombCofinalRAction.original_R_direct]
  exact counted_R N c _

theorem actual_full_inventory (depth ordinal N : ℕ) :
    actualField observation nontrivial half depth ordinal N=
      (PA.E (actualField observation nontrivial half depth ordinal N):BurnolL2)+
      (PA.Q (actualField observation nontrivial half depth ordinal N):BurnolL2)+
      outside (actualField observation nontrivial half depth ordinal N) := by
  let value:=actualField observation nontrivial half depth ordinal N
  have split:=congrArg (fun p:BurnolPaAmbientCarrier=>(p:BurnolL2))
    (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
      (burnolEvenAmbientProjection value))
  change (PA.E value:BurnolL2)+(PA.Q value:BurnolL2)=(burnolEvenAmbientProjection value:BurnolL2) at split
  change value=_
  rw [show outside value=value-(burnolEvenAmbientProjection value:BurnolL2) from
    Submodule.starProjection_orthogonal_val value]
  linear_combination (norm:=module) -split

/-- Only the Pa return of this retained outside stock vanishes, by the original zero-owned unit. -/
theorem actual_outside_return (depth ordinal N : ℕ) :
    PA.E (R c (outside (actualField observation nontrivial half depth ordinal N)))=0 :=
  Reentry.outside_P_R_E_zero observation nontrivial half.down _

theorem actual_Pa_source (depth ordinal N : ℕ) :
    PA.E (actualField observation nontrivial half depth (ordinal+1) N)=
      correction c (actualField observation nontrivial half depth ordinal N)+
      bc c (PA.E (actualField observation nontrivial half depth ordinal N)) • PA.E unit+
      inner ℂ Funit (PA.Q (actualField observation nontrivial half depth ordinal N):BurnolL2) •
        (Reentry.sourceReentryVector c:BurnolPaAmbientCarrier) := by
  rw [actual_counted_next]
  exact full_Pa_source observation nontrivial half _

theorem actual_coefficient_source (depth ordinal N : ℕ) :
    bc c (PA.E (actualField observation nontrivial half depth (ordinal+1) N))=
      LogSource.sourceLogCoefficient c (PA.E (actualField observation nontrivial half depth ordinal N))+
      bc c (PA.E (actualField observation nontrivial half depth ordinal N))*bc c (PA.E unit)+
      inner ℂ Funit (PA.Q (actualField observation nontrivial half depth ordinal N):BurnolL2)*
        bc c (Reentry.sourceReentryVector c:BurnolPaAmbientCarrier) := by
  rw [actual_Pa_source,map_add,map_add,map_smul,map_smul,correction_coefficient]
  simp only [smul_eq_mul]

theorem actual_Mobius_source (depth ordinal N : ℕ) :
    burnolMobiusSourceL2 (PA.E (actualField observation nontrivial half depth (ordinal+1) N))=
      burnolTateReciprocalL2 (sourceVolterraWindow c (burnolTateReciprocalL2
        (burnolMobiusSourceL2 (PA.E (actualField observation nontrivial half depth ordinal N)))))+
      bc c (PA.E (actualField observation nontrivial half depth ordinal N)) • burnolMobiusSourceL2 (PA.E unit)+
      inner ℂ Funit (PA.Q (actualField observation nontrivial half depth ordinal N):BurnolL2) •
        burnolMobiusSourceL2 (Reentry.sourceReentryVector c:BurnolPaAmbientCarrier) := by
  rw [actual_Pa_source,map_add,map_add,map_smul,map_smul]
  congr 2
  have source:=sourceVolterraPhysical_source c
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (actualField observation nontrivial half depth ordinal N))))
    (original_tate_source_even _) (sourceAnnulusCut_original_pa _ (Submodule.starProjection_apply_mem _ _))
  have back:=congrArg burnolTateReciprocalL2 source
  simpa only [correction,burnolTateReciprocalL2_involutive] using back

end OriginalZero
end OriginalKCountedPaSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
