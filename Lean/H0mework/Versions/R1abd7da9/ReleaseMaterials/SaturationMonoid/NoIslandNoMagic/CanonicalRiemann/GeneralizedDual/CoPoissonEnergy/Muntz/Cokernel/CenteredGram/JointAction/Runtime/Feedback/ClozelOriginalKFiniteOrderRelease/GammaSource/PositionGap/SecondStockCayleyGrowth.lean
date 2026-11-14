import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalTwoLogRecovery
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SecondConductorAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock

open BurnolPhysicalState OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped lp

open private gamma_written log_written from
  H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalTwoLogRecovery

local instance baseNormedGroup : NormedAddCommGroup Base := inferInstance
local instance ambientNormedGroup : NormedAddCommGroup Ambient := inferInstance
local instance stockNormedGroup : NormedAddCommGroup Whole := inferInstance
local instance baseNormedSpace : NormedSpace ℂ Base := inferInstance

@[instance_reducible] private def closedStockNormed : NormedSpace ℂ Whole := by
  letI : NormedSpace ℂ Ambient :=
    WithLp.instProdNormedSpace (𝕜 := ℂ) (α := Base) (β := SecondSlots) (p := 2)
  exact Submodule.normedSpace carrier

attribute [local instance] closedStockNormed

local notation "R" => burnolDirectRightResolventCLM
local notation "d" => sourceDamping

private def rawRead : Whole →L[ℂ] BurnolL2 := LogStock.field.comp base
private def posRead : Whole →L[ℂ] BurnolL2 := LogStock.positionLog.comp base
private def freqRead : Whole →L[ℂ] BurnolL2 :=
  fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp (LogStock.inverseLog.comp base)

private def logDrive (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (-(1/2:ℂ)) • (R c)^2

private def secondDrive (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (H.writeSecond c).comp ((1 : BurnolL2 →L[ℂ] BurnolL2).prod 0)

/-- The original full-stock advance has its literal raw R action. -/
theorem advance_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (x : Whole) :
    LogStock.field (base (advance c zero x)) = R c (LogStock.field (base x)) :=
  LogStock.advance_field c (base x)

private theorem pos_written (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (x : Whole) :
    posRead (advance c zero x) = R c (posRead x) + logDrive c (rawRead x) :=
  log_written c (base x)

private theorem freq_read (x : Whole) : freqRead x = LogStock.gamma (base x) - posRead x := by
  change fourierL2 (LogStock.inverseLog (base x)) =
    posRead x + fourierL2 (LogStock.inverseLog (base x)) - posRead x
  rw [add_sub_cancel_left]

private theorem freq_written (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (x : Whole) :
    freqRead (advance c zero x) = R c (freqRead x) + (-logDrive c) (rawRead x) := by
  rw [freq_read, freq_read, pos_written, map_sub, neg_apply]
  change LogStock.gamma (LogStock.advance c (base x)) - _ = _
  rw [gamma_written]
  abel

private theorem second_sum (c : BurnolCompletedMellinCoordinate) (v g : BurnolL2) :
    H.writeSecond c (v,g) = R c g + secondDrive c v := by
  have zero : H.writeSecond c (0,g) = R c g := by
    simp [OriginalKCrossParameterRAdjointSource.GammaOutsideHistory.Second.writeSecond]
  have pair : (v,g) = (0,g)+(v,0) := by simp
  rw [pair, map_add, zero]
  rfl

private theorem outside_written (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (x : Whole) :
    outsideSecond (advance c zero x) = R c (outsideSecond x) + secondDrive c (rawRead x) := by
  have write := congrArg Prod.snd (advance_second_fields c zero x)
  exact write.trans (second_sum c _ _)

private theorem physical_written (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (x : Whole) :
    physicalSecond (advance c zero x) = R c (physicalSecond x) + (-secondDrive c) (rawRead x) := by
  have write := congrArg Prod.fst (advance_second_fields c zero x)
  change physicalSecond (advance c zero x) = R c (physicalSecond x + outsideSecond x) -
    H.writeSecond c (rawRead x,outsideSecond x) at write
  rw [write, second_sum, map_add, neg_apply]
  abel

/-- The full-stock Cayley letter uses the same original advance. -/
def liftedCayley (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) : Whole →L[ℂ] Whole :=
  1 + (d c : ℂ) • advance c zero

private theorem raw_cayley (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (x : Whole) :
    rawRead (liftedCayley c zero x) = sourceCayley c (rawRead x) := by
  simp only [liftedCayley, add_apply, one_apply_eq_self, smul_apply, map_add, map_smul,
    show rawRead (advance c zero x) = R c (rawRead x) from advance_raw c zero x]
  rfl

private theorem raw_norm (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (n : Nat) (x : Whole) :
    ‖rawRead (((liftedCayley c zero)^n) x)‖ = ‖rawRead x‖ := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ n previous =>
    rw [pow_succ', mul_apply_eq_comp, raw_cayley, sourceCayley_norm, previous]

private theorem coordinate_growth (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (read : Whole →L[ℂ] BurnolL2) (drive : BurnolL2 →L[ℂ] BurnolL2)
    (source : ∀ x, read (advance c zero x) = R c (read x) + drive (rawRead x))
    (n : Nat) (x : Whole) :
    ‖read (((liftedCayley c zero)^n) x)‖ ≤
      (‖read‖ + (n:ℝ) * ‖(d c:ℂ) • drive‖ * ‖rawRead‖)*‖x‖ := by
  let U := liftedCayley c zero
  let W := (d c:ℂ) • drive
  have step (y : Whole) : read (U y) = sourceCayley c (read y) + W (rawRead y) := by
    simp only [U, liftedCayley, add_apply, one_apply_eq_self, smul_apply, map_add, map_smul, source, W]
    change read y + (d c:ℂ) • (R c (read y) + drive (rawRead y)) =
      (read y + (d c:ℂ) • R c (read y)) + (d c:ℂ) • drive (rawRead y)
    rw [smul_add, add_assoc]
  change ‖read ((U^n) x)‖ ≤ (‖read‖+(n:ℝ)*‖W‖*‖rawRead‖)*‖x‖
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, Nat.cast_zero, zero_mul, add_zero] using read.le_opNorm x
  | succ n prior =>
    rw [pow_succ', mul_apply_eq_comp, step]
    have feed : ‖W (rawRead ((U^n) x))‖ ≤ ‖W‖ * (‖rawRead‖ * ‖x‖) := by
      have bound := W.le_opNorm (rawRead ((U^n) x))
      change ‖W (rawRead ((U^n) x))‖ ≤ ‖W‖ * ‖rawRead ((U^n) x)‖ at bound
      rw [raw_norm c zero n x] at bound
      exact bound.trans (mul_le_mul_of_nonneg_left (rawRead.le_opNorm x) (norm_nonneg _))
    calc
      _ ≤ ‖sourceCayley c (read ((U^n) x))‖ + ‖W (rawRead ((U^n) x))‖ := norm_add_le _ _
      _ ≤ (‖read‖+(n:ℝ)*‖W‖*‖rawRead‖)*‖x‖ + ‖W‖*(‖rawRead‖*‖x‖) := by
        rw [sourceCayley_norm]
        exact add_le_add prior feed
      _ = _ := by rw [Nat.cast_succ]; ring

private theorem lp_pair_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (x : WithLp 2 (E × F)) : ‖x‖ ≤ ‖x.fst‖+‖x.snd‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  have one := norm_nonneg x.fst
  have two := norm_nonneg x.snd
  exact (Real.sqrt_le_iff).2 ⟨add_nonneg one two, by nlinarith [mul_nonneg one two]⟩

private theorem norm_ports (x : Whole) :
    ‖x‖ ≤ ‖rawRead x‖+‖posRead x‖+‖freqRead x‖+‖physicalSecond x‖+‖outsideSecond x‖ := by
  let b := (base x : LogStock.AmbientStock)
  have frequency : ‖freqRead x‖ = ‖b.snd.snd‖ := fourierL2.norm_map _
  have baseBound : ‖base x‖ ≤ ‖rawRead x‖+(‖posRead x‖+‖freqRead x‖) := by
    rw [frequency]
    exact (lp_pair_bound b).trans (add_le_add le_rfl (lp_pair_bound b.snd))
  have second : ‖(x : Ambient).snd‖ ≤ ‖physicalSecond x‖+‖outsideSecond x‖ :=
    lp_pair_bound (x : Ambient).snd
  calc
    ‖x‖ ≤ ‖base x‖+‖(x : Ambient).snd‖ := lp_pair_bound (x : Ambient)
    _ ≤ _ := (add_le_add baseBound second).trans (le_of_eq (by abel))

private def initialBudget : ℝ :=
  ‖rawRead‖+‖posRead‖+‖freqRead‖+‖physicalSecond‖+‖outsideSecond‖

private def driveBudget (c : BurnolCompletedMellinCoordinate) : ℝ :=
  (2*‖(d c:ℂ) • logDrive c‖+2*‖(d c:ℂ) • secondDrive c‖)*‖rawRead‖

def linearBudget (c : BurnolCompletedMellinCoordinate) : ℝ := initialBudget + driveBudget c

theorem linearBudget_nonnegative (c : BurnolCompletedMellinCoordinate) : 0 ≤ linearBudget c := by
  unfold linearBudget initialBudget driveBudget
  positivity

/-- Both original directed log slots and both native Γ² slots pay the same linear Cayley budget. -/
theorem lifted_power_bound (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (n : Nat) (x : Whole) :
    ‖((liftedCayley c zero)^n) x‖ ≤ ((n:ℝ)+1) * linearBudget c * ‖x‖ := by
  let y := ((liftedCayley c zero)^n) x
  have a : ‖rawRead y‖ ≤ ‖rawRead‖ * ‖x‖ := by
    change ‖rawRead (((liftedCayley c zero)^n) x)‖ ≤ _
    rw [raw_norm]
    exact rawRead.le_opNorm x
  have b := coordinate_growth c zero posRead (logDrive c) (pos_written c zero) n x
  have f := coordinate_growth c zero freqRead (-logDrive c) (freq_written c zero) n x
  have p := coordinate_growth c zero physicalSecond (-secondDrive c) (physical_written c zero) n x
  have o := coordinate_growth c zero outsideSecond (secondDrive c) (outside_written c zero) n x
  rw [smul_neg, norm_neg] at f p
  have all := add_le_add (add_le_add (add_le_add (add_le_add a b) f) p) o
  calc
    _ ≤ ‖rawRead y‖+‖posRead y‖+‖freqRead y‖+‖physicalSecond y‖+‖outsideSecond y‖ := norm_ports y
    _ ≤ _ := all
    _ = (initialBudget+(n:ℝ)*driveBudget c)*‖x‖ := by
      unfold initialBudget driveBudget
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have first : 0 ≤ initialBudget := by unfold initialBudget; positivity
      have second : 0 ≤ driveBudget c := by unfold driveBudget; positivity
      have extra := add_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) first) second
      unfold linearBudget
      nlinarith

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
