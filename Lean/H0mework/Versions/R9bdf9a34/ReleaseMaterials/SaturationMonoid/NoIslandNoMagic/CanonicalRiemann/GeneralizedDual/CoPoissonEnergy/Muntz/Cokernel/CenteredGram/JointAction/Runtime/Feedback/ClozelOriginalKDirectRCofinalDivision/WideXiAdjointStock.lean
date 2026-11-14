import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WidePaOverlapConsumer
import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointWholeStock
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedTransport

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 150000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn.XiContact

open BurnolPhysicalState
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped Topology InnerProductSpace

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner
private def project {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Submodule ℂ H) [CompleteSpace S] : H →L[ℂ] S :=
  S.orthogonalProjectionOnto

private theorem projection_cost {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Submodule ℂ H) [CompleteSpace S] (x : H) (y : S) :
    ‖(project S x : H)-(y : H)‖ ≤ ‖x-(y : H)‖ ∧
    ‖x-(project S x : H)‖ ≤ ‖x-(y : H)‖ := by
  have kept : S.starProjection (y : H) = (y : H) := Submodule.starProjection_eq_self_iff.mpr y.property
  have gone : Sᗮ.starProjection (y : H) = 0 := by
    rw [Submodule.starProjection_orthogonal_val, kept, sub_self]
  change ‖S.starProjection x-(y : H)‖ ≤ ‖x-(y : H)‖ ∧
    ‖x-S.starProjection x‖ ≤ ‖x-(y : H)‖
  constructor
  · have bound := S.norm_starProjection_apply_le (x-(y : H))
    rw [map_sub, kept] at bound
    exact bound
  · have bound := Sᗮ.norm_starProjection_apply_le (x-(y : H))
    rw [map_sub, gone, sub_zero, Submodule.starProjection_orthogonal_val] at bound
    exact bound

open private readField from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualPaReturn
open private adjoint_even right_quarter below_half from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private original_unit_gap writeStock from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointWholeStock
open private chart from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryXiSlot

local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "J" => fun c : BurnolCompletedMellinCoordinate => ContinuousLinearMap.adjoint (sourceCayley c)
local notation "Resolvent" => burnolDirectRightResolventCLM

/-- Each finite condition is the original conjugate price after its actual adjoint prefix. -/
def contactRead (anchor : BurnolCompletedMellinCoordinate) (n : Nat) :
    Wide →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i : Fin n => (M (C anchor)).comp
    ((((J anchor)^i.val) : BurnolL2 →L[ℂ] BurnolL2).comp readField)

def contact (anchor : BurnolCompletedMellinCoordinate) (n : Nat) : Submodule ℂ Wide :=
  (contactRead anchor n).ker

theorem contact_iff (anchor : BurnolCompletedMellinCoordinate) (n : Nat) (x : Wide) :
    x ∈ contact anchor n ↔ ∀ i < n, M (C anchor) (((J anchor)^i) (readField x)) = 0 := by
  change ((fun i : Fin n => M (C anchor) (((J anchor)^i.val) (readField x))) = 0) ↔ _
  constructor
  · intro source i earlier
    exact congrFun source ⟨i,earlier⟩
  · intro source
    funext i
    exact source i.val i.isLt

private theorem contact_closed (anchor : BurnolCompletedMellinCoordinate) (n : Nat) :
    IsClosed (contact anchor n : Set Wide) := (contactRead anchor n).isClosed_ker

private theorem contactComplete (anchor : BurnolCompletedMellinCoordinate) (n : Nat) :
    CompleteSpace ↥(contact anchor n) := (contact_closed anchor n).isComplete.completeSpace_coe

def qualify (anchor : BurnolCompletedMellinCoordinate) (n : Nat) :
    Wide →L[ℂ] ↥(contact anchor n) :=
  @project Wide (inferInstanceAs (NormedAddCommGroup Wide)) wideInner (contact anchor n)
    (contactComplete anchor n)

def rejected (anchor : BurnolCompletedMellinCoordinate) (n : Nat) : Wide →L[ℂ] Wide :=
  1 - (contact anchor n).subtypeL.comp (qualify anchor n)

theorem qualify_self (anchor : BurnolCompletedMellinCoordinate) (n : Nat) (x : contact anchor n) :
    qualify anchor n (x : Wide) = x :=
  @Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ℂ Wide _ _ wideInner (contact anchor n)
    (@Submodule.HasOrthogonalProjection.ofCompleteSpace ℂ Wide _ _ wideInner (contact anchor n)
      (contactComplete anchor n)) x

theorem qualify_split (anchor : BurnolCompletedMellinCoordinate) (n : Nat) (x : Wide) :
    (qualify anchor n x : Wide) + rejected anchor n x = x := by
  change (qualify anchor n x : Wide) + (x-(qualify anchor n x : Wide)) = x
  exact add_sub_cancel _ _

theorem qualification_cost (anchor : BurnolCompletedMellinCoordinate) (n : Nat) (x : Wide)
    (y : contact anchor n) :
    ‖(qualify anchor n x : Wide)-(y : Wide)‖ ≤ ‖x-(y : Wide)‖ ∧
    ‖rejected anchor n x‖ ≤ ‖x-(y : Wide)‖ :=
  @projection_cost Wide (inferInstanceAs (NormedAddCommGroup Wide)) wideInner (contact anchor n)
    (contactComplete anchor n) x y

private theorem first_price_zero (anchor : BurnolCompletedMellinCoordinate) (n : Nat)
    (x : contact anchor (n+1)) : M (C anchor) (readField (x : Wide)) = 0 := by
  have lower := (contact_iff anchor (n+1) (x : Wide)).mp x.property 0 (Nat.zero_lt_succ n)
  simpa only [pow_zero, one_apply_eq_self] using lower

private def singleWrite (anchor : BurnolCompletedMellinCoordinate) (zero : riemannZeta (C anchor).value = 0)
    (n : Nat) (x : contact anchor (n+1)) : Wide := by
  let old := toWhole (x : Wide)
  let v := readField (x : Wide)
  have inside : v ∈ PositionField := LogStock.field_mem (base old)
  have parity := mem_evenL2ClosedFace_iff.mp inside.2
  have price := first_price_zero anchor n x
  have wrote : J anchor v ∈ PositionField :=
    ⟨(actual_gap_cayley_adjoint_iff anchor v inside.1 parity).mpr price,
      mem_evenL2ClosedFace_iff.mpr (adjoint_even anchor v parity)⟩
  let result := writeStock anchor zero old wrote
  refine ⟨(result : Ambient),result.property,?_⟩
  change J anchor v ∈ locallyConstantFace 1
  exact original_unit_gap anchor (x : Wide).property.2 parity price

private theorem single_write_field (anchor : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta (C anchor).value = 0) (n : Nat) (x : contact anchor (n+1)) :
    readField (singleWrite anchor zero n x) = J anchor (readField (x : Wide)) := rfl

/-- One native adjoint letter consumes one contact equation and writes the closed-graph fields. -/
def advanceAdjoint (anchor : BurnolCompletedMellinCoordinate) (zero : riemannZeta (C anchor).value = 0)
    (n : Nat) (x : contact anchor (n+1)) : contact anchor n :=
  ⟨singleWrite anchor zero n x, (contact_iff anchor n _).mpr fun i lower => by
    have source := (contact_iff anchor (n+1) _).mp x.property (i+1) (Nat.succ_lt_succ lower)
    rw [pow_succ, mul_apply_eq_comp] at source
    rw [single_write_field]
    exact source⟩

def terminal (anchor : BurnolCompletedMellinCoordinate) (zero : riemannZeta (C anchor).value = 0) :
    (n : Nat) → contact anchor n → Wide
  | 0, x => (x : Wide)
  | n+1, x => terminal anchor zero n (advanceAdjoint anchor zero n x)

theorem terminal_field (anchor : BurnolCompletedMellinCoordinate) (zero : riemannZeta (C anchor).value = 0)
    (n : Nat) (x : contact anchor n) :
    readField (terminal anchor zero n x) = ((J anchor)^n) (readField (x : Wide)) := by
  induction n with
  | zero => simp only [terminal, pow_zero, one_apply_eq_self]
  | succ n previous =>
    change readField (terminal anchor zero n (advanceAdjoint anchor zero n x)) = _
    rw [previous, pow_succ, mul_apply_eq_comp]
    exact congrArg (fun v : BurnolL2 => ((J anchor)^n) v) (single_write_field anchor zero n x)

theorem raw_injective : Function.Injective readField := by
  intro x y same
  apply Subtype.ext
  change (toWhole x : Ambient) = (toWhole y : Ambient)
  exact congrArg (fun z : Whole => (z : Ambient))
    (base_injective (LogStock.field_injective same))

private theorem native_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (x : Wide) : readField (advanceWide c zero x) = Resolvent c (readField x) :=
  advance_raw c zero (toWhole x)

private theorem price_advance (c coordinate : BurnolCompletedMellinCoordinate)
    (v : BurnolL2) (gap : v ∈ locallyConstantFace burnolUnscaledCommonGapRadius) :
    M coordinate (Resolvent c v) =
      (-(1/(c.value/2+coordinate.value/2-1/2))) * M coordinate v := by
  have action := CombSource.Pricing.ambient_R_scalar_action (c.value/2) (right_quarter c)
    v gap (coordinate.value/2) (right_quarter coordinate) (below_half coordinate)
  rw [chart coordinate] at action
  exact action

theorem forward_contact (anchor c : BurnolCompletedMellinCoordinate)
    (conjugateZero : riemannZeta (C anchor).value = 0) (zero : riemannZeta c.value = 0)
    (n : Nat) (x : contact anchor n) : advanceWide c zero (x : Wide) ∈ contact anchor n := by
  apply (contact_iff anchor n _).mpr
  intro i earlier
  let input := readField (x : Wide)
  let v := ((J anchor)^i) input
  let prior : contact anchor i :=
    ⟨(x : Wide), (contact_iff anchor i _).mpr fun j hj =>
      (contact_iff anchor n _).mp x.property j (hj.trans earlier)⟩
  let stock := terminal anchor conjugateZero i prior
  have inside := LogStock.field_mem (base (toWhole stock))
  have raw : readField stock = v := terminal_field anchor conjugateZero i prior
  have gap : v ∈ locallyConstantFace burnolUnscaledCommonGapRadius := raw ▸ inside.1
  have commute := congrArg (fun op : BurnolL2 →L[ℂ] BurnolL2 => op input)
    ((BoundaryCountedTransport.adjoint_commutes c anchor).pow_right i).eq
  change Resolvent c v = ((J anchor)^i) (Resolvent c input) at commute
  rw [native_read, ← commute, price_advance c (C anchor) v gap,
    (contact_iff anchor n _).mp x.property i earlier, mul_zero]

end WideResidualReturn.XiContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
