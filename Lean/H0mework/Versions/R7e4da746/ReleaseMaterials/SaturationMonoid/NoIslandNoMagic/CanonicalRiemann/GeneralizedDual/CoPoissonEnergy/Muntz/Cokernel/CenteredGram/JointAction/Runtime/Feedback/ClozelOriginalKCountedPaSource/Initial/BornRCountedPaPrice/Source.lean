import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRFiniteOrderPrice.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalReentrySourceAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Core

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRCountedPaPrice
open Complex
open CenteredGram.IntegralGraphJointAction
open scoped InnerProductSpace
namespace PA
export OriginalKCombCofinalPaAction (E Q invisible invisible_mem)
end PA
namespace Reentry
export OriginalKDirectRCofinalReentrySourceAction (sourceReentryVector sourceReentryAction full_invisible_reentry)
end Reentry
namespace OldPrices
export OriginalKFiniteOrderRelease.UnitPowerMaterialConsumer (actualPaFee)
end OldPrices
open OriginalPaPhysicalGreen
local instance paComplete:CompleteSpace BurnolPaAmbientCarrier:=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R"=>burnolDirectRightResolventCLM c
local notation "bc"=>burnolPaResolventSourceCoefficient c
local notation "feedback"=>OriginalKFiniteOrderRelease.UnitPowerSource.feedbackCoefficient observation half

def pa (value:BurnolL2):BurnolPaAmbientCarrier:=PA.E value

theorem pa_member (value:BurnolL2):pa value∈burnolCompactCoPoissonClosedRange:=
 Submodule.starProjection_apply_mem _ _

def unit:BurnolPaAmbientCarrier:=burnolZeroOwnedUnitTailState observation nontrivial half.down

def correction (value:BurnolL2):BurnolPaAmbientCarrier:=
 burnolPaSourceCorrection c ⟨pa value,pa_member value⟩

def alpha (value:BurnolL2):ℂ:=bc (pa value)

def returning:BurnolPaAmbientCarrier:=(Reentry.sourceReentryVector c:BurnolPaAmbientCarrier)

def eta (value:BurnolL2):ℂ:=
 inner ℂ (fourierL2 (burnolUnitTailResponse (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4))
  (PA.invisible value)

def outside (value:BurnolL2):BurnolL2:=value-(burnolEvenAmbientProjection value:BurnolL2)

def paResponse (value:BurnolL2):BurnolPaAmbientCarrier:=
 burnolPaResolventPhysicalResponse observation nontrivial half.down (pa value) (pa_member value)

theorem correction_read (value:BurnolL2):
 (correction observation half value:BurnolL2)=R (pa value:BurnolL2)-
  alpha observation half value • (unit observation nontrivial half:BurnolL2):=rfl

theorem correction_mem (value:BurnolL2):correction observation half value∈burnolCompactCoPoissonClosedRange:=
 burnolPaSourceCorrection_mem c _

theorem correction_E (value:BurnolL2):
 PA.E (correction observation half value:BurnolL2)=correction observation half value:=by
 change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  (burnolEvenAmbientProjection (correction observation half value:BurnolL2))=_
 have physical:burnolEvenAmbientProjection (correction observation half value:BurnolL2)=
  correction observation half value:=Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 rw [physical]
 exact Submodule.starProjection_eq_self_iff.mpr (correction_mem observation half value)

theorem correction_Q (value:BurnolL2):PA.Q (correction observation half value:BurnolL2)=0:=by
 change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (burnolEvenAmbientProjection (correction observation half value:BurnolL2))=0
 have physical:burnolEvenAmbientProjection (correction observation half value:BurnolL2)=
  correction observation half value:=Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 rw [physical]
 exact Submodule.starProjection_orthogonal_apply_eq_zero (correction_mem observation half value)

theorem invisible_inventory (value:BurnolL2):
 PA.invisible value=(PA.Q value:BurnolL2)+outside value:=by
 have split:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
  (burnolEvenAmbientProjection value)
 have read:=congrArg (fun field:BurnolPaAmbientCarrier=>(field:BurnolL2)) split
 change (pa value:BurnolL2)+(PA.Q value:BurnolL2)=(burnolEvenAmbientProjection value:BurnolL2) at read
 unfold PA.invisible outside
 rw [←read]
 unfold pa
 abel

theorem eta_inventory (value:BurnolL2):
 eta observation half value=
  inner ℂ (fourierL2 (burnolUnitTailResponse (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4)) (PA.Q value:BurnolL2)+
  inner ℂ (fourierL2 (burnolUnitTailResponse (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4)) (outside value):=by
 unfold eta
 rw [invisible_inventory,inner_add_right]

theorem reentry_read (value:BurnolL2):
 PA.E (R (PA.invisible value))=eta observation half value • returning observation half:=
 Reentry.full_invisible_reentry c value

-- All three generated output fields use this current source, before an actual successor is read.
def wholeNext (value:BurnolL2):BurnolL2:=
 (correction observation half value:BurnolL2)+alpha observation half value • (unit observation nontrivial half:BurnolL2)+
  R (PA.invisible value)

def paNext (value:BurnolL2):BurnolPaAmbientCarrier:=
 correction observation half value+alpha observation half value • PA.E (unit observation nontrivial half:BurnolL2)+
  eta observation half value • returning observation half

def qNext (value:BurnolL2):BurnolPaAmbientCarrier:=
 alpha observation half value • PA.Q (unit observation nontrivial half:BurnolL2)+PA.Q (R (PA.invisible value))

def outsideNext (value:BurnolL2):BurnolL2:=outside (R (PA.invisible value))

theorem whole_next_actual (value:BurnolL2):wholeNext observation nontrivial half value=R value:=by
 have split:(pa value:BurnolL2)+PA.invisible value=value:=by unfold pa PA.invisible;abel
 calc
  _=R (pa value:BurnolL2)+R (PA.invisible value):=by rw [wholeNext,correction_read observation nontrivial half value];abel
  _=R ((pa value:BurnolL2)+PA.invisible value):=(map_add R _ _).symm
  _=R value:=congrArg R split

theorem pa_next_actual (value:BurnolL2):paNext observation nontrivial half value=PA.E (R value):=by
 rw [←whole_next_actual observation nontrivial half value,wholeNext,map_add,map_add,map_smul,correction_E,reentry_read]
 rfl

theorem q_next_actual (value:BurnolL2):qNext observation nontrivial half value=PA.Q (R value):=by
 rw [←whole_next_actual observation nontrivial half value,wholeNext,map_add,map_add,map_smul,correction_Q,zero_add]
 rfl

theorem pa_response_value (value:BurnolL2):
 (paResponse observation nontrivial half value:BurnolL2)=R (pa value:BurnolL2):=rfl

theorem pa_response_unit_rank (value:BurnolL2):
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection (paResponse observation nontrivial half value)=
 alpha observation half value •
  burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection (unit observation nontrivial half):=
 burnolPaResolventPhysicalResponse_Q observation nontrivial half.down (pa value) (pa_member value)

include nontrivial in
theorem outside_next_actual (value:BurnolL2):outsideNext observation half value=outside (R value):=by
 have physical:(burnolEvenAmbientProjection (R (pa value:BurnolL2)):BurnolL2)=R (pa value:BurnolL2):=
  Submodule.starProjection_eq_self_iff.mpr (burnolPaResolvent_physical observation nontrivial half.down _ (pa_member value))
 have split:R value=R (pa value:BurnolL2)+R (PA.invisible value):=by
  rw [←map_add]
  congr 1
  unfold pa PA.invisible
  abel
 unfold outsideNext outside
 rw [split,map_add,Submodule.coe_add,physical]
 abel

def tateNext (value:BurnolL2):BurnolL2:=
 sourceVolterraWindow c (burnolTateReciprocalL2 (burnolMobiusSourceL2 (pa value)))+
 alpha observation half value • burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (unit observation nontrivial half:BurnolL2)))+
 eta observation half value • burnolTateReciprocalL2 (burnolMobiusSourceL2 (returning observation half))

theorem tate_next_actual (value:BurnolL2):
 tateNext observation nontrivial half value=burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (R value))):=by
 rw [←pa_next_actual observation nontrivial half value,paNext,map_add,map_add,map_smul,map_smul,map_add,map_add,map_smul,map_smul]
 have window:sourceVolterraWindow c (burnolTateReciprocalL2 (burnolMobiusSourceL2 (pa value)))=
  burnolTateReciprocalL2 (burnolMobiusSourceL2 (correction observation half value)):=
  sourceVolterraWindow_original_pa c (pa value) (pa_member value)
 rw [←window]
 rfl

-- The fee reads only current Pa correction, original unit feet, and the whole invisible reentry.
def sourceFee (value:BurnolL2):ℂ:=feedback*(
 bc (correction observation half value)+alpha observation half value*(bc (PA.E (unit observation nontrivial half:BurnolL2))-1)+
 eta observation half value*bc (returning observation half))

theorem source_fee_actual (value:BurnolL2):
 sourceFee observation nontrivial half value=OldPrices.actualPaFee observation half (R value-value):=by
 have scalar:bc (PA.E (R value-value))=
  bc (correction observation half value)+alpha observation half value*bc (PA.E (unit observation nontrivial half:BurnolL2))+
   eta observation half value*bc (returning observation half)-alpha observation half value:=by
  rw [map_sub,map_sub,←pa_next_actual observation nontrivial half value,paNext,map_add,map_add,map_smul,map_smul]
  rfl
 unfold sourceFee OldPrices.actualPaFee
 rw [scalar]
 ring

end CountedPaInitial.BornRCountedPaPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
