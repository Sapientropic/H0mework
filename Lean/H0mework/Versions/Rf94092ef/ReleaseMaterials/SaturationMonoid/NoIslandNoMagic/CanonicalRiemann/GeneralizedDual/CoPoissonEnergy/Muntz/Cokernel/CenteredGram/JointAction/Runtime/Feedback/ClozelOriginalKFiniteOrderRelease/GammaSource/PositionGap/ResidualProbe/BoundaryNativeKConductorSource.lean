import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointWholeStock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Physical

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryNativeKConductorSource

open BurnolPhysicalState MeasureTheory OriginalRieszSource
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.ConductorDual OriginalGamma.Source.WindowLog
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open BurnolPhysicalState.OriginalRSourceJointContact.LogAction
open scoped InnerProductSpace

open private centeredCut centeredPositionLog centeredFourierLog centered_position_log_pair centered_fourier_log_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Physical
open private log_pair_reflect log_pair_add from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
open private logPair_sub logPair_smul from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource
open private adjoint_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.GammaOutsideDomain
open private gamma_acted from
  H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointWholeStock
open private position_from_frequency from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.CrossPrice
open private inverse_log_from_complete_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
open private cayley_even adjoint_even right_quarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley

local notation "F" => fourierL2
local notation "T" => sourceCayley
local notation "R" => burnolDirectRightResolventCLM
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Ppos" => HilbertInventory.positionSpace.toSubmodule.starProjection
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "Rq" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "MZ" => burnolQuarterMeanZeroProjection
local notation "q" => (1/4 : ℝ)

/-- The two closed logarithmic graphs accompany their literal even source field. -/
structure Source where
  value : BurnolL2
  position : BurnolL2
  inverse : BurnolL2
  even : reflectL2 value = value
  position_graph : LogPair value position
  inverse_graph : LogPair ((F).symm value) inverse

def Source.gamma (x : Source) : BurnolL2 := x.position + F x.inverse

theorem Source.graph (x : Source) : GammaPair x.value x.gamma :=
  gamma_pair_of_log_pairs _ _ _ x.position_graph x.inverse_graph

private theorem even_part (v : BurnolL2) (even : reflectL2 v=v) : burnolAmbientEvenPart v=v := by
  unfold burnolAmbientEvenPart
  rw [even]
  module

private theorem centered_even (v : BurnolL2) (even : reflectL2 v=v) :
    reflectL2 (centeredCut v)=centeredCut v := by
  change reflectL2 (burnolRadiusZeroExtension q (MZ (Rq v))) = _
  rw [burnolRadiusZeroExtension_reflect]
  have fixed : reflectRestricted q (Rq v)=Rq v :=
    (restrictToInterval_reflectL2 q v).symm.trans (congrArg Rq even)
  change E (reflectRestricted q (MZ (Rq v))) = E (MZ (Rq v))
  exact (congrArg E (burnolQuarterMeanZeroProjection_reflect (Rq v)).symm).trans
    (congrArg (fun state => E (MZ state)) fixed)

/-- The position projection keeps the original quarter mean and removes only the centered cut. -/
theorem position_projection (v : BurnolL2) (even : reflectL2 v=v) :
    Ppos v = v-centeredCut v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · constructor
    · apply mem_locallyConstantFace_iff_exists.mpr
      refine ⟨burnolQuarterMeanCoefficient (Rq v), ?_⟩
      change burnolQuarterMeanCoefficient (Rq v) • intervalConstant q = Rq (v-E (MZ (Rq v)))
      rw [map_sub, burnolQuarterRestriction_zeroExtension, burnolMeanZeroProjection_eq_sub_constant]
      module
    · apply mem_evenL2ClosedFace_iff.mpr
      rw [map_sub, even, centered_even v even]
  · intro w belongs
    have restricted := (mem_locallyConstantFace_iff_exists.mp belongs.1)
    obtain ⟨a, ha⟩ := restricted
    have zero : inner ℂ (MZ (Rq v)) (intervalConstant q) = 0 :=
      inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp
        (burnolQuarterMeanZeroProjection_mem (Rq v)) (intervalConstant q) (Submodule.mem_span_singleton_self _))
    rw [show v-(v-centeredCut v)=centeredCut v by abel]
    change inner ℂ (E (MZ (Rq v))) w = 0
    calc
      _ = inner ℂ (MZ (Rq v)) (Rq w) :=
        ContinuousLinearMap.adjoint_inner_left Rq w (MZ (Rq v))
      _ = 0 := by
        change a • intervalConstant q = Rq w at ha
        rw [← ha, inner_smul_right, zero, mul_zero]

private theorem forward_frequency (x : Source) : LogPair (F x.value) (reflectL2 x.inverse) := by
  have paid := log_pair_reflect _ _ x.inverse_graph
  rw [fourierL2_symm_eq_reflect_fourierL2, reflectL2_reflectL2] at paid
  exact paid

private def positionP (x : Source) := x.position-centeredPositionLog x.value x.position
private def positionF (x : Source) := x.inverse-reflectL2 (centeredFourierLog x.value (reflectL2 x.inverse))

def position (x : Source) : Source where
  value := Ppos x.value
  position := positionP x
  inverse := positionF x
  even := by
    exact mem_evenL2ClosedFace_iff.mp (Submodule.starProjection_apply_mem
      HilbertInventory.positionSpace.toSubmodule x.value).2
  position_graph := by
    rw [position_projection x.value x.even]
    exact logPair_sub _ _ _ _ x.position_graph (centered_position_log_pair _ _ x.position_graph)
  inverse_graph := by
    have centered := log_pair_reflect _ _ (centered_fourier_log_pair _ _ (forward_frequency x))
    rw [← fourierL2_symm_eq_reflect_fourierL2] at centered
    rw [position_projection x.value x.even, map_sub]
    exact logPair_sub _ _ _ _ x.inverse_graph centered

def sub (x y : Source) : Source where
  value := x.value-y.value
  position := x.position-y.position
  inverse := x.inverse-y.inverse
  even := by rw [map_sub, x.even, y.even]
  position_graph := logPair_sub _ _ _ _ x.position_graph y.position_graph
  inverse_graph := by
    rw [map_sub]
    exact logPair_sub _ _ _ _ x.inverse_graph y.inverse_graph

private def adjointInverse (c : BurnolCompletedMellinCoordinate) (x : Source) : BurnolL2 :=
  x.inverse + (sourceDamping c : ℂ) •
    (R (C c) x.inverse - directLogMoment ((C c).value/2) ((F).symm x.value))

private theorem adjoint_inverse_graph (c : BurnolCompletedMellinCoordinate) (x : Source) :
    LogPair ((F).symm ((T c).adjoint x.value)) (adjointInverse c x) := by
  have paid := actual_direct_R_log ((C c).value/2) (right_quarter (C c)) _ _ x.inverse_graph
  have split (v : BurnolL2) : (T c).adjoint v =
      v+(sourceDamping c : ℂ) • F (R (C c) ((F).symm v)) := by
    rw [sourceCayley_actual_adjoint, sourceAdjointCayley]
    congr 1
    exact congrArg (fun value : BurnolL2 => (sourceDamping c : ℂ) • value) (adjoint_source c v).symm
  rw [split, map_add, map_smul, LinearIsometryEquiv.symm_apply_apply]
  exact log_pair_add _ _ _ _ x.inverse_graph (logPair_smul _ _ _ paid)

def adjoint (c : BurnolCompletedMellinCoordinate) (x : Source) : Source where
  value := (T c).adjoint x.value
  position := (T c).adjoint x.gamma-F (adjointInverse c x)
  inverse := adjointInverse c x
  even := adjoint_even c x.value x.even
  position_graph := position_from_frequency _ _ _ (gamma_acted c x.graph) (adjoint_inverse_graph c x)
  inverse_graph := adjoint_inverse_graph c x

def iterate (c : BurnolCompletedMellinCoordinate) (k : Nat) : Source → Source :=
  Nat.rec (motive := fun _ => Source → Source) id (fun _ previous x => adjoint c (previous x)) k

theorem iterate_value (c : BurnolCompletedMellinCoordinate) (k : Nat) (x : Source) :
    (iterate c k x).value = ((T c).adjoint^k) x.value := by
  induction k with
  | zero => rfl
  | succ k previous =>
    change (T c).adjoint (iterate c k x).value = _
    rw [previous, pow_succ', mul_apply_eq_comp]

private def forwardPosition (c : BurnolCompletedMellinCoordinate) (x : Source) : BurnolL2 :=
  x.position + (sourceDamping c : ℂ) •
    (R c x.position-directLogMoment (c.value/2) x.value)

private theorem forward_position_graph (c : BurnolCompletedMellinCoordinate) (x : Source) :
    LogPair (T c x.value) (forwardPosition c x) := by
  rw [sourceCayley_apply]
  exact log_pair_add _ _ _ _ x.position_graph
    (logPair_smul _ _ _ (actual_direct_R_log (c.value/2) (right_quarter c) _ _ x.position_graph))

private theorem forward_graph (c : BurnolCompletedMellinCoordinate) (x : Source) :
    GammaPair (T c x.value) (T c x.gamma) := by
  have paid := OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower.actual_Gamma_R c _ _ x.graph
  intro test
  rw [sourceCayley_apply, sourceCayley_apply, inner_add_right, inner_smul_right,
    inner_add_right, inner_smul_right, x.graph test]
  exact congrArg (fun value : ℂ => inner ℂ (test.toLp 2 volume) x.gamma +
    (sourceDamping c : ℂ)*value) (paid test)

def forward (c : BurnolCompletedMellinCoordinate) (x : Source) : Source where
  value := T c x.value
  position := forwardPosition c x
  inverse := (F).symm (T c x.gamma-forwardPosition c x)
  even := cayley_even c x.value x.even
  position_graph := forward_position_graph c x
  inverse_graph := inverse_log_from_complete_source _ _ _ (forward_graph c x) (forward_position_graph c x)

def physical (x : Source) : Source where
  value := P x.value
  position := physicalProjectionPositionLog x.value x.position
  inverse := reflectL2 (physicalProjectionFourierLog x.value (reflectL2 x.inverse))
  even := mem_evenL2ClosedFace_iff.mp (Submodule.starProjection_apply_mem
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule x.value).2
  position_graph := (actual_physical_projection_log_pairs _ _ _ x.position_graph (forward_frequency x)).1
  inverse_graph := by
    have paid := log_pair_reflect _ _
      (actual_physical_projection_log_pairs _ _ _ x.position_graph (forward_frequency x)).2
    rw [← fourierL2_symm_eq_reflect_fourierL2] at paid
    exact paid

/-- The original adjoints, position projection, return, subtraction and ambient projection act on both log graphs. -/
def action (c : BurnolCompletedMellinCoordinate) (k : Nat) (x : Source) : Source :=
  let z := iterate (C c) k x
  physical (sub z (forward (C c) (position (adjoint (C c) z))))

theorem action_value (c : BurnolCompletedMellinCoordinate) (k : Nat) (x : Source) :
    (action c k x).value =
      let z := ((T (C c)).adjoint^k) x.value
      P (z-T (C c) (Ppos ((T (C c)).adjoint z))) := by
  change P ((iterate (C c) k x).value-T (C c) (Ppos ((T (C c)).adjoint (iterate (C c) k x).value))) = _
  rw [iterate_value]


/-- Both projection commutators retain the generated logarithmic fields. -/
def positionCommutator (x : Source) : BurnolL2 := (position x).gamma-Ppos x.gamma

def physicalCommutator (x : Source) : BurnolL2 := (physical x).gamma-P x.gamma

theorem adjoint_gamma (c : BurnolCompletedMellinCoordinate) (x : Source) :
    (adjoint c x).gamma = (T c).adjoint x.gamma := by
  change (T c).adjoint x.gamma-F (adjointInverse c x)+F (adjointInverse c x) = _
  exact sub_add_cancel _ _

theorem forward_gamma (c : BurnolCompletedMellinCoordinate) (x : Source) :
    (forward c x).gamma = T c x.gamma := by
  change forwardPosition c x+F ((F).symm (T c x.gamma-forwardPosition c x)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  abel

theorem sub_gamma (x y : Source) : (sub x y).gamma=x.gamma-y.gamma := by
  change x.position-y.position+F (x.inverse-y.inverse) = _
  rw [map_sub]
  unfold Source.gamma
  abel

theorem iterate_gamma (c : BurnolCompletedMellinCoordinate) (k : Nat) (x : Source) :
    (iterate c k x).gamma = ((T c).adjoint^k) x.gamma := by
  induction k with
  | zero => rfl
  | succ k previous =>
    change (adjoint c (iterate c k x)).gamma = _
    rw [adjoint_gamma, previous, pow_succ', mul_apply_eq_comp]

theorem action_gamma (c : BurnolCompletedMellinCoordinate) (k : Nat) (x : Source) :
    let z := iterate (C c) k x
    let y := adjoint (C c) z
    let difference := sub z (forward (C c) (position y))
    (action c k x).gamma =
      P (((T (C c)).adjoint^k) x.gamma - T (C c)
        (Ppos (((T (C c)).adjoint^(k+1)) x.gamma)+positionCommutator y))+
          physicalCommutator difference := by
  dsimp only
  have p (u : Source) : (position u).gamma=Ppos u.gamma+positionCommutator u := by
    unfold positionCommutator
    abel
  have a (u : Source) : (physical u).gamma=P u.gamma+physicalCommutator u := by
    unfold physicalCommutator
    abel
  change (physical (sub (iterate (C c) k x)
    (forward (C c) (position (adjoint (C c) (iterate (C c) k x)))))).gamma = _
  rw [a, sub_gamma, forward_gamma, p, adjoint_gamma, iterate_gamma, pow_succ', mul_apply_eq_comp]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryNativeKConductorSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
