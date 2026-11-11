import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalReentrySourceAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open scoped InnerProductSpace
local instance paAdjointPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The coefficient covector uses the already generated re-entry source and actual Fourier action. -/
def paCoefficientSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector
      (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) : BurnolPaAmbientCarrier)

def wholeUnitSourcePrice (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  inner ℂ (generatedK coordinate) (burnolUnitTailResponse coordinate 4)

def paAdjointSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  star (wholeUnitSourcePrice coordinate) • paCoefficientSource coordinate

/-- B acts on the complete source field; the Pa source is then removed as a whole vector. -/
def qAdjointSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolAmbientExtendedSonineProjectionFormula (sourceAdjointField coordinate) -
    (paAdjointSource coordinate : BurnolL2)

private theorem conjugateCoordinate_twice (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalPrimitiveRankBalance.conjugateCoordinate
      (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) = coordinate := by
  cases coordinate
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate, star_star]

private theorem paCoefficientSource_mem (coordinate : BurnolCompletedMellinCoordinate) :
    paCoefficientSource coordinate ∈ burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange
    (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector
      (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)).property

theorem paCoefficientSource_read (coordinate : BurnolCompletedMellinCoordinate)
    (g : BurnolPaAmbientCarrier) (inside : g ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ (paCoefficientSource coordinate) g = burnolPaResolventSourceCoefficient coordinate g := by
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  let r := (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector
    (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) : BurnolPaAmbientCarrier)
  have FgPa : F g ∈ burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside
  have read := OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector_read
    (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) (F g) FgPa
  rw [conjugateCoordinate_twice] at read
  change inner ℂ (F g) r = star (burnolPaResolventSourceCoefficient coordinate (F (F g))) at read
  have invol (v : BurnolPaAmbientCarrier) : F (F v)=v :=
    evenFaceFourier_involutive burnolUnscaledCommonGapRadius v
  rw [invol] at read
  have symmetric := inner_conj_symm (𝕜:=ℂ) r (F g)
  change star (inner ℂ (F g) r)=inner ℂ r (F g) at symmetric
  rw [read,star_star] at symmetric
  change inner ℂ (F r) g = _
  calc
    inner ℂ (F r) g = inner ℂ r (F g) := by
      simpa only [invol] using F.inner_map_map r (F g)
    _ = _ := symmetric.symm

/-- The actual Pa resolvent correction is killed by K's paid Pa orthogonality. -/
theorem paAdjointSource_tests (coordinate : BurnolCompletedMellinCoordinate)
    (orthogonal : burnolCompletedMellinRieszVector coordinate ∈
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ)
    (g : BurnolPaAmbientCarrier) (inside : g ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ (sourceAdjointField coordinate) (g : BurnolL2) =
      inner ℂ (paAdjointSource coordinate) g := by
  let corrected := burnolPaSourceCorrection coordinate ⟨g,inside⟩
  have correctedPa := burnolPaSourceCorrection_mem coordinate ⟨g,inside⟩
  have killed : inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (corrected : BurnolL2) = 0 := by
    exact inner_eq_zero_symm.mp (orthogonal corrected correctedPa)
  have split : burnolDirectRightResolvent (coordinate.value/2) (g : BurnolL2) =
      (corrected : BurnolL2)+burnolPaResolventSourceCoefficient coordinate g •
        burnolUnitTailResponse coordinate 4 := by
    change burnolDirectRightResolvent (coordinate.value/2) (g : BurnolL2) =
      (burnolDirectRightResolvent (coordinate.value/2) (g : BurnolL2)-
        burnolPaResolventSourceCoefficient coordinate g • burnolUnitTailResponse coordinate 4)+_
    abel
  have actual := original_R_full_input coordinate (g : BurnolL2)
  rw [split,inner_add_right,inner_smul_right,killed,zero_add] at actual
  rw [paAdjointSource,inner_smul_left]
  change _ = star (star (wholeUnitSourcePrice coordinate))*inner ℂ (paCoefficientSource coordinate) g
  rw [star_star,paCoefficientSource_read coordinate g inside]
  unfold wholeUnitSourcePrice
  rw [generatedK_eq_original]
  exact actual.symm.trans (mul_comm _ _)

/-- All original Pa tests identify the complete Pa component of H with its generated rank-one source. -/
theorem paAdjointSource_actual (coordinate : BurnolCompletedMellinCoordinate)
    (orthogonal : burnolCompletedMellinRieszVector coordinate ∈
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) :
    OriginalKCombCofinalPaAction.E (sourceAdjointField coordinate) = paAdjointSource coordinate := by
  have normal (g : BurnolPaAmbientCarrier) (inside : g ∈ burnolCompactCoPoissonClosedRange) :
      inner ℂ g (OriginalKCombCofinalPaAction.E (sourceAdjointField coordinate)) =
        inner ℂ g (paAdjointSource coordinate) := by
    rw [OriginalKCombCofinalPaAction.wholePa_normal_read _ g inside]
    calc
      inner ℂ (g : BurnolL2) (sourceAdjointField coordinate) =
          star (inner ℂ (sourceAdjointField coordinate) (g : BurnolL2)) :=
        (inner_conj_symm (𝕜:=ℂ) (g : BurnolL2) (sourceAdjointField coordinate)).symm
      _ = star (inner ℂ (paAdjointSource coordinate) g) :=
        congrArg star (paAdjointSource_tests coordinate orthogonal g inside)
      _ = inner ℂ g (paAdjointSource coordinate) :=
        inner_conj_symm (𝕜:=ℂ) g (paAdjointSource coordinate)
  have belongs : OriginalKCombCofinalPaAction.E (sourceAdjointField coordinate)-paAdjointSource coordinate ∈
      burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem (Submodule.starProjection_apply_mem _ _)
      (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _ (paCoefficientSource_mem coordinate))
  have zero : inner ℂ
      (OriginalKCombCofinalPaAction.E (sourceAdjointField coordinate)-paAdjointSource coordinate)
      (OriginalKCombCofinalPaAction.E (sourceAdjointField coordinate)-paAdjointSource coordinate) = 0 := by
    rw [inner_sub_right,normal _ belongs,sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp zero)

theorem qAdjointSource_actual (coordinate : BurnolCompletedMellinCoordinate)
    (orthogonal : burnolCompletedMellinRieszVector coordinate ∈
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) :
    (OriginalKCombCofinalPaAction.Q (sourceAdjointField coordinate) : BurnolL2) = qAdjointSource coordinate := by
  have split := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection (sourceAdjointField coordinate))
  have inventory := congrArg (fun field : BurnolPaAmbientCarrier => (field : BurnolL2)) split
  change (OriginalKCombCofinalPaAction.E (sourceAdjointField coordinate) : BurnolL2)+
    (OriginalKCombCofinalPaAction.Q (sourceAdjointField coordinate) : BurnolL2) =
      (burnolEvenAmbientProjection (sourceAdjointField coordinate) : BurnolL2) at inventory
  rw [paAdjointSource_actual coordinate orthogonal] at inventory
  have projected := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (sourceAdjointField coordinate)
  change (burnolEvenAmbientProjection (sourceAdjointField coordinate) : BurnolL2) = _ at projected
  rw [projected] at inventory
  unfold qAdjointSource
  linear_combination (norm := module) inventory

/-- Q is read through both actual orthogonal projections, including the full physical projection. -/
private theorem full_Q_selfAdjoint (left right : BurnolL2) :
    inner ℂ left (OriginalKCombCofinalPaAction.Q right : BurnolL2) =
      inner ℂ (OriginalKCombCofinalPaAction.Q left : BurnolL2) right := by
  have ambient := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    (OriginalKCombCofinalPaAction.Q right) left
  have pa := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_starProjection_left_eq_right
    (burnolEvenAmbientProjection left) (burnolEvenAmbientProjection right)
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (OriginalKCombCofinalPaAction.Q left) right
  exact ambient.symm.trans (pa.symm.trans physical)

theorem qAdjointSource_full_input (coordinate : BurnolCompletedMellinCoordinate)
    (orthogonal : burnolCompletedMellinRieszVector coordinate ∈
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) (value : BurnolL2) :
    inner ℂ (sourceAdjointField coordinate) (OriginalKCombCofinalPaAction.Q value : BurnolL2) =
      inner ℂ (qAdjointSource coordinate) value := by
  rw [←qAdjointSource_actual coordinate orthogonal]
  exact full_Q_selfAdjoint _ _

/-- Actual original Division now consumes the source vector QH on its unprojected next input. -/
theorem actual_nextQ_complete_source (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let coordinate := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    let K := (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    let H := sourceAdjointField coordinate
    inner ℂ K (OriginalKCombCofinalPaAction.Q (D.raw observation nontrivial half depth ((ordinal+1)+1)) : BurnolL2) =
      OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)*
        inner ℂ K (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)+
      inner ℂ (qAdjointSource coordinate) (D.raw observation nontrivial half depth (ordinal+1))+
      inner ℂ (outsideCotest H) (sourceOutsideColumn coordinate (D.raw observation nontrivial half depth ordinal)) := by
  dsimp only
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) observation.mathlibZero
  have actual := actual_nextQ_source_action observation nontrivial half depth ordinal
  rw [qAdjointSource_full_input _ orthogonal] at actual
  exact actual

/-- Dropping the generated Pa term changes the full source by its actual rank-one vector. -/
theorem delete_paAdjointSource_defect (coordinate : BurnolCompletedMellinCoordinate) :
    burnolAmbientExtendedSonineProjectionFormula (sourceAdjointField coordinate)-qAdjointSource coordinate =
      (paAdjointSource coordinate : BurnolL2) := by
  unfold qAdjointSource
  abel

theorem zero_wholeUnitSourcePrice_override (coordinate : BurnolCompletedMellinCoordinate)
    (zero : wholeUnitSourcePrice coordinate=0) :
    paAdjointSource coordinate=0 ∧ qAdjointSource coordinate=
      burnolAmbientExtendedSonineProjectionFormula (sourceAdjointField coordinate) := by
  have actual : paAdjointSource coordinate=0 := by
    simp only [paAdjointSource,zero,star_zero,zero_smul]
  exact ⟨actual, by rw [qAdjointSource,actual];simp only [ZeroMemClass.coe_zero,sub_zero]⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
