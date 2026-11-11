import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactFloor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.KPaired

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.OriginalK
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
local notation "T" => burnolTateReciprocalL2
local notation "F" => fourierL2
local notation "leading" => ForcingPrimitive.leadingCoefficient

/-- The original complete dual grid and original position grid share their actual counted log return. -/
theorem actual_original_C_position_count (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    fullFloorValue c zero=PositionCounting.value c zero+leading c • poissonPair (logProgramme c):=by
  apply Lp.ext
  filter_upwards [actual_full_floor_raw c zero,PositionCounting.value_coeFn c zero,
    actual_log_return_count_field c,
    Lp.coeFn_add (PositionCounting.value c zero) (leading c • poissonPair (logProgramme c)),
    Lp.coeFn_smul (leading c) (poissonPair (logProgramme c))]
    with x original position returned added scalar
  rw [original,actual_counted_position_source,added,Pi.add_apply,scalar,Pi.smul_apply,smul_eq_mul,
    position,returned]
  rfl

/-- The same full C is an actual source leg of the original K counting value, including the independent B leg. -/
theorem actual_original_K_counted_field (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    F (KCountingGram.value c)= -T (fullFloorValue c zero)+
      leading c • F (logProgramme c)-CountingDual.value c:=by
  have cSource:=congrArg T (actual_original_C_position_count c zero)
  rw [map_add,map_smul] at cSource
  have paid:T (poissonPair (logProgramme c))=F (logProgramme c):=by
    change T (T (F (logProgramme c)))=F (logProgramme c)
    exact burnolTateReciprocalL2_involutive _
  rw [paid] at cSource
  have original:=congrArg T (actual_original_K_paired_value c zero)
  rw [map_sub,map_neg,burnolTateReciprocalL2_involutive] at original
  have kernelPaid:T (poissonPair (KCountingGram.value c))=F (KCountingGram.value c):=by
    change T (T (F (KCountingGram.value c)))=F (KCountingGram.value c)
    exact burnolTateReciprocalL2_involutive _
  rw [kernelPaid] at original
  rw [←original,cSource]
  module

/-- The actual whole original K value is determined before a fixed shift or cut is applied. -/
theorem actual_original_K_counted_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    KCountingGram.value c=fourierL2.symm (-T (fullFloorValue c zero)+
      leading c • F (logProgramme c)-CountingDual.value c):=by
  apply fourierL2.injective
  rw [actual_original_K_counted_field c zero,fourierL2.apply_symm_apply]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.OriginalK
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
