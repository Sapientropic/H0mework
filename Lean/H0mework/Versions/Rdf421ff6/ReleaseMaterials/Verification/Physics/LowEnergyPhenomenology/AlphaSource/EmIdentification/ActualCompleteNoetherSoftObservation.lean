import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCoupledNoetherSourceFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open ActualElectronPhysicalJointInverse ActualElectronWholeChargeSoft ActualDressedFullCoulomb ActualDressedNoether
open PreparationVacuumSourcePreparedResponse GaussComposite.SourceGraph ActualQuantitativePreparedFrameOwn
open SourceFamilyHilbert SourceFamilyOperator Filter PreparationVacuumMixedFieldReturn
open CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open scoped InnerProductSpace Topology
attribute [local irreducible] dressedNoetherKernel actualElectronPhysicalUnit actualCoupledNoetherTransfer
  actualPhysicalEulerObserver actualElectronPhysicalState chargeReader actualNoetherBackground

private theorem family_observer_return {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (U b : Family E u) (A : Operator I E) :
    Tendsto (fun F=>-inner ℂ (value U F) (A.component F (value U F))+
      inner ℂ (value b F) (A.component F (value b F))) u
      (𝓝 (-inner ℂ (U : Hilbert E u) (lift u A (U : Hilbert E u))+
        inner ℂ (b : Hilbert E u) (lift u A (b : Hilbert E u)))) := by
  rw [lift_coe,lift_coe,inner_coe,inner_coe]
  exact (pair_tendsto u U (act u A U)).neg.add (pair_tendsto u b (act u A b))

private theorem inner_operator_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E→L[ℂ]E) (x y : E) :‖inner ℂ x (A y)‖≤‖x‖*‖A‖*‖y‖ :=
  (norm_inner_le_norm x (A y)).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (A.le_opNorm y) (norm_nonneg x))

private theorem prepared_operator_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E→L[ℂ]E) (a x : E) (anorm : ‖a‖=1) (xnorm : ‖x‖=1) :
    ‖inner ℂ a (A a)-inner ℂ x (B x)‖≤‖A-B‖+2*‖B‖*‖a-x‖ := by
  have identity : inner ℂ a (A a)-inner ℂ x (B x)=
      inner ℂ a ((A-B) a)+inner ℂ (a-x) (B a)+inner ℂ x (B (a-x)) := by
    simp only [sub_apply,inner_sub_right,inner_sub_left,map_sub]
    abel
  rw [identity]
  calc
    _≤(‖inner ℂ a ((A-B) a)‖+‖inner ℂ (a-x) (B a)‖)+‖inner ℂ x (B (a-x))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _≤(‖a‖*‖A-B‖*‖a‖+‖a-x‖*‖B‖*‖a‖)+‖x‖*‖B‖*‖a-x‖ :=
      add_le_add (add_le_add (inner_operator_bound _ _ _) (inner_operator_bound _ _ _)) (inner_operator_bound _ _ _)
    _=_ := by rw [anorm,xnorm];ring

def actualCompleteNoetherFrameRead (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (m : ℕ) (F : GaussUnitaryHistory.Index) : ℂ:=
  let k:=actualCoupledNoetherTransfer event reader age F leg direction m
  let psi:=actualElectronPhysicalUnit (event.momentum+k) F event.energy leg
  let K:=dressedNoetherKernel event (-k) reader age 0
  let b:=prepared (sourceProfile event.epsilon event.precision);
  -inner ℂ psi (K psi)+inner ℂ b (K b)

def actualCompleteNoetherBaseFrameRead (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (F : GaussUnitaryHistory.Index) : ℂ:=
  let psi:=actualElectronPhysicalUnit event.momentum F event.energy leg
  let K:=dressedNoetherKernel event 0 reader age 0
  let b:=prepared (sourceProfile event.epsilon event.precision);
  -inner ℂ psi (K psi)+inner ℂ b (K b)

def actualCompleteNoetherRead (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) : ℂ:=
  let psi:=actualCoupledPhysicalState event reader age leg direction m
  let K:=actualCoupledNoetherOperator event reader age leg direction unit m;
  -inner ℂ psi (K psi)+inner ℂ (actualNoetherBackground event) (K (actualNoetherBackground event))

attribute [local irreducible] actualCompleteNoetherFrameRead actualCompleteNoetherBaseFrameRead actualCompleteNoetherRead

theorem actual_complete_noether_frame_error (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) (F : GaussUnitaryHistory.Index) :
    ‖actualCompleteNoetherFrameRead event reader age leg direction m F-
      actualCompleteNoetherBaseFrameRead event reader age leg F‖≤
      (2+2*‖dressedNoetherKernel event 0 reader age 0‖)*actualSoftBudget m := by
  let a:=actualElectronPhysicalUnit (event.momentum+actualCoupledNoetherTransfer event reader age F leg direction m) F event.energy leg
  let x:=actualElectronPhysicalUnit event.momentum F event.energy leg
  let b:=prepared (sourceProfile event.epsilon event.precision)
  let A:=dressedNoetherKernel event (-actualCoupledNoetherTransfer event reader age F leg direction m) reader age 0
  let B:=dressedNoetherKernel event 0 reader age 0
  have anorm : ‖a‖=1:=actual_electron_physical_unit_norm _ F event.energy event.nonreal leg
  have xnorm : ‖x‖=1:=actual_electron_physical_unit_norm _ F event.energy event.nonreal leg
  have bnorm : ‖b‖=1:=by simpa only [b,actualPrepared] using actualPrepared_norm event.epsilon event.precision
  have paid:=actual_coupled_noether_frame_error event reader age F leg direction unit m
  have primary:=prepared_operator_error A B a x anorm xnorm
  have background:=prepared_operator_error A B b b bnorm bnorm
  have identity : actualCompleteNoetherFrameRead event reader age leg direction m F-
      actualCompleteNoetherBaseFrameRead event reader age leg F=
    -(inner ℂ a (A a)-inner ℂ x (B x))+(inner ℂ b (A b)-inner ℂ b (B b)) := by
      unfold actualCompleteNoetherFrameRead actualCompleteNoetherBaseFrameRead
      dsimp only [a,x,b,A,B]
      abel
  rw [identity]
  calc
    _≤‖inner ℂ a (A a)-inner ℂ x (B x)‖+‖inner ℂ b (A b)-inner ℂ b (B b)‖ := by
      simpa only [norm_neg] using norm_add_le (-(inner ℂ a (A a)-inner ℂ x (B x))) (inner ℂ b (A b)-inner ℂ b (B b))
    _≤(‖A-B‖+2*‖B‖*‖a-x‖)+(‖A-B‖+2*‖B‖*‖b-b‖) := add_le_add primary background
    _≤(actualSoftBudget m+2*‖B‖*actualSoftBudget m)+actualSoftBudget m := by
      simp only [sub_self,norm_zero,mul_zero,add_zero]
      exact add_le_add (add_le_add paid.2 (mul_le_mul_of_nonneg_left paid.1 (by positivity))) paid.2
    _=_ := by dsimp only [B];ring

/-- The new physical observer keeps the actual electron correction and the original background charge calibration. -/
theorem actual_physical_noether_observer_charge (event : DressedEvent) (leg : CompositeLeg) :
    actualPhysicalEulerObserver event leg (chargeReader sourcePhaseGaugeLie)=
      -actualElectronSign leg-
        inner ℂ (actualElectronPhysicalState event.momentum event.energy event.nonreal leg)
          (actualWholeElectronCorrection event.momentum event.energy event.nonreal leg)+
      inner ℂ (actualNoetherBackground event)
        (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie) (actualNoetherBackground event)) := by
  have observed:=actual_physical_euler_observer_value event leg (chargeReader sourcePhaseGaugeLie)
  have charged:=actual_whole_electron_diagonal_charge event.momentum event.energy event.nonreal leg
  exact observed.trans ((congrArg (fun v : ℂ=>-v+
    inner ℂ (actualNoetherBackground event)
      (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie) (actualNoetherBackground event))) charged).trans (by ring))

/-- Both the varying complete insertion and the actual prepared state are completed on the same original sourceFilter. -/
theorem actual_complete_noether_history_return (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    Tendsto (actualCompleteNoetherFrameRead event reader age leg direction m) GaussUnitaryHistory.sourceFilter
      (𝓝 (actualCompleteNoetherRead event reader age leg direction unit m)) := by
  unfold actualCompleteNoetherRead actualCoupledPhysicalState actualCoupledNoetherOperator actualNoetherBackground
  unfold actualCompleteNoetherFrameRead
  exact family_observer_return GaussUnitaryHistory.sourceFilter
    (actualCoupledPhysicalFamily event reader age leg direction m)
    (constant GaussUnitaryHistory.sourceFilter (prepared (sourceProfile event.epsilon event.precision)))
    (actualCoupledNoetherOperators event reader age leg direction unit m)

private theorem noether_base_history_return (event : DressedEvent) (reader : Field289) (age : ℝ) (leg : CompositeLeg) :
    Tendsto (actualCompleteNoetherBaseFrameRead event reader age leg) GaussUnitaryHistory.sourceFilter
      (𝓝 (actualPhysicalEulerObserver event leg (dressedNoetherKernel event 0 reader age 0))) := by
  rw [actual_physical_euler_observer_value]
  unfold actualElectronPhysicalState actualNoetherBackground actualCompleteNoetherBaseFrameRead
  exact family_observer_return GaussUnitaryHistory.sourceFilter
    (actualElectronPhysicalStateFamily event.momentum event.energy event.nonreal leg)
    (constant GaussUnitaryHistory.sourceFilter (prepared (sourceProfile event.epsilon event.precision)))
    (constant (dressedNoetherKernel event 0 reader age 0))

theorem actual_complete_noether_whole_soft_error (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualCompleteNoetherRead event reader age leg direction unit m-
      actualPhysicalEulerObserver event leg (dressedNoetherKernel event 0 reader age 0)‖≤
      (2+2*‖dressedNoetherKernel event 0 reader age 0‖)*actualSoftBudget m := by
  have convergence:=((actual_complete_noether_history_return event reader age leg direction unit m).sub
    (noether_base_history_return event reader age leg)).norm
  exact le_of_tendsto convergence (Eventually.of_forall (actual_complete_noether_frame_error event reader age leg direction unit m))

theorem actual_complete_noether_whole_soft_return (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) :
    Tendsto (actualCompleteNoetherRead event reader age leg direction unit) atTop
      (𝓝 (actualPhysicalEulerObserver event leg (dressedNoetherKernel event 0 reader age 0))) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  have decay:=(actual_soft_budget_tendsto.const_mul (2+2*‖dressedNoetherKernel event 0 reader age 0‖))
  rw [mul_zero] at decay
  exact (decay.eventually (eventually_lt_nhds positive)).mono (fun m small=>by
    rw [dist_eq_norm]
    exact (actual_complete_noether_whole_soft_error event reader age leg direction unit m).trans_lt small)

end LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver
