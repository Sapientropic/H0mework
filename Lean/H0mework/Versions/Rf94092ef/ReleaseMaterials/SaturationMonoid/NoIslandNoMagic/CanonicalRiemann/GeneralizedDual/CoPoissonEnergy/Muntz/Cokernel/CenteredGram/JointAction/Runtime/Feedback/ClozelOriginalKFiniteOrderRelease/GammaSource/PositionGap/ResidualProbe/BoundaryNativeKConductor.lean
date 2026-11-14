import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKConductorSource
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LogHeadInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryNativeKConductor

open BurnolPhysicalState
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.FiniteLogCounting
open OriginalGamma.Source.KGamma
open scoped InnerProductSpace

namespace CS
export BoundaryNativeKConductorSource (Source sub action action_value action_gamma)
end CS
namespace KAction
export BoundaryNativeKAction (physical originalResult configuration actual_equation material_raw actual_paid
  input_from_original_receipt source_trace_in_next_stock actual_receipt_next whole_first generated_next
  actual_born_K actual_born_fixed_price)
end KAction
namespace Read
export BoundaryNativeKRead (input input_source amplitude field field_apply)
end Read

open private physical_field from
  H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKAction
open private conductor_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "factory" => OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half
local notation "nativeAt" => OriginalKCofinalFullBranchFibre.KernelWrite.originalNative observation nontrivial half depth
local notation "amount" => Read.amplitude observation nontrivial half depth

/-- Both logarithmic fields are generated at the original literal Division index. -/
def rawSource (ordinal : Nat) : CS.Source where
  value := raw ordinal
  position := DivisionConductor.positionLogAt observation half ordinal
  inverse := DivisionConductor.inverseLogAt observation half ordinal
  even := mem_evenL2ClosedFace_iff.mp
    (HilbertInventory.LogStock.field_mem (HilbertInventory.LogStock.actualAt observation nontrivial half depth ordinal)).2
  position_graph := (DivisionConductor.actual_division_conductor observation nontrivial half depth ordinal).2.1
  inverse_graph := (DivisionConductor.actual_division_conductor observation nontrivial half depth ordinal).2.2

/-- The exact decoded beta uses the two complete source differences from its original receipt. -/
def inputSource (ordinal : Nat) : CS.Source :=
  CS.sub (rawSource observation nontrivial half depth (ordinal+3))
    (rawSource observation nontrivial half depth (ordinal+1))

theorem input_value (ordinal n : Nat) :
    (inputSource observation nontrivial half depth ordinal).value = Read.input observation nontrivial half depth ordinal n :=
  (Read.input_source observation nontrivial half depth ordinal n).symm

/-- Apply the original physical program while retaining both log graphs and its projection commutators. -/
def sourceAction (ordinal : Nat) : CS.Source :=
  CS.action c m (inputSource observation nontrivial half depth ordinal)

theorem source_action_value (ordinal n : Nat) :
    (sourceAction observation nontrivial half depth ordinal).value = KAction.physical observation nontrivial half depth ordinal n :=
  (CS.action_value c m (inputSource observation nontrivial half depth ordinal)).trans
    ((Read.field_apply c m (inputSource observation nontrivial half depth ordinal).value).symm.trans
    ((congrArg (Read.field c m) (input_value observation nontrivial half depth ordinal n)).trans
      (physical_field observation nontrivial half depth ordinal n).symm))

theorem actual_born_log_sources (ordinal n : Nat) :
    LogPair (KAction.physical observation nontrivial half depth ordinal n)
      (sourceAction observation nontrivial half depth ordinal).position ∧
    LogPair ((fourierL2).symm (KAction.physical observation nontrivial half depth ordinal n))
      (sourceAction observation nontrivial half depth ordinal).inverse := by
  rw [← source_action_value observation nontrivial half depth ordinal n]
  exact ⟨(sourceAction observation nontrivial half depth ordinal).position_graph,
    (sourceAction observation nontrivial half depth ordinal).inverse_graph⟩

theorem actual_born_conductor (ordinal n : Nat) :
    GammaPair (KAction.physical observation nontrivial half depth ordinal n)
      (sourceAction observation nontrivial half depth ordinal).gamma := by
  rw [← source_action_value observation nontrivial half depth ordinal n]
  exact (sourceAction observation nontrivial half depth ordinal).graph

/-- Original Gamma-K recognizes the conductor after the source action has generated it. -/
theorem actual_original_Gamma (ordinal n : Nat) :
    (sourceAction observation nontrivial half depth ordinal).gamma =
      amount ordinal • actualGammaKernel c := by
  have actual := actual_born_conductor observation nontrivial half depth ordinal n
  rw [KAction.actual_born_K observation nontrivial half depth ordinal n] at actual
  have original : GammaPair
      (amount ordinal • (burnolCompletedMellinRieszVector c : BurnolL2))
      (amount ordinal • actualGammaKernel c) := by
    intro test
    rw [inner_smul_right, inner_smul_right, actual_gamma_original_kernel c test]
  exact conductor_unique _ _ _ actual original

/-- The same beta, physical execution, born inventory, whole write and literal next consume the complete conductor. -/
theorem actual_conductor_writeback (ordinal n : Nat) :
    type_of% (input_value observation nontrivial half depth ordinal n) ∧
    type_of% (actual_born_log_sources observation nontrivial half depth ordinal n) ∧
    type_of% (actual_born_conductor observation nontrivial half depth ordinal n) ∧
    type_of% (CS.action_gamma c m (inputSource observation nontrivial half depth ordinal)) ∧
    type_of% (actual_original_Gamma observation nontrivial half depth ordinal n) ∧
    type_of% (KAction.input_from_original_receipt c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (KAction.actual_equation c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (KAction.source_trace_in_next_stock c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (KAction.actual_receipt_next c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (KAction.whole_first c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (KAction.generated_next c n m factory (nativeAt (ordinal+1))) :=
  ⟨input_value observation nontrivial half depth ordinal n,
    actual_born_log_sources observation nontrivial half depth ordinal n,
    actual_born_conductor observation nontrivial half depth ordinal n,
    CS.action_gamma c m (inputSource observation nontrivial half depth ordinal),
    actual_original_Gamma observation nontrivial half depth ordinal n,
    KAction.input_from_original_receipt c n m factory (nativeAt (ordinal+1)),
    KAction.actual_equation c n m factory (nativeAt (ordinal+1)),
    KAction.source_trace_in_next_stock c n m factory (nativeAt (ordinal+1)),
    KAction.actual_receipt_next c n m factory (nativeAt (ordinal+1)),
    KAction.whole_first c n m factory (nativeAt (ordinal+1)),
    KAction.generated_next c n m factory (nativeAt (ordinal+1))⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryNativeKConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
