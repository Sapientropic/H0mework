import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeNoetherPhysicalObserver

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open ActualElectronPhysicalJointInverse ActualElectronWholeChargeSoft ActualDressedFullCoulomb ActualDressedNoether
open SourceFamilyHilbert SourceFamilyOperator Filter PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open scoped InnerProductSpace Topology
attribute [local irreducible] dressedNoetherKernel actualElectronPhysicalUnit

/-- Both actual producers choose one common positive radius; no uniform operator witness is supplied. -/
private theorem coupled_radius_exists (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (m : ℕ) :
    ∃r : ℝ,0<r ∧ ∀k : PhysicalMomentum,‖k‖<r→
      ‖actualElectronPhysicalUnit (event.momentum+k) F event.energy leg-
        actualElectronPhysicalUnit event.momentum F event.energy leg‖≤actualSoftBudget m ∧
      ‖dressedNoetherKernel event (-k) reader age 0-dressedNoetherKernel event 0 reader age 0‖≤actualSoftBudget m := by
  have u : ContinuousAt (fun k : PhysicalMomentum=>actualElectronPhysicalUnit (event.momentum+k) F event.energy leg) 0 :=
    ((actual_electron_physical_unit_continuous F event.energy event.nonreal leg).comp
      ((continuous_const (y:=event.momentum)).add continuous_id)).continuousAt
  have K :=(actual_full_noether_transfer_continuous event reader age).continuousAt (x:=0)
  obtain ⟨ru,pu,bu⟩:=Metric.continuousAt_iff.mp u (actualSoftBudget m) (actual_soft_budget_positive m)
  obtain ⟨rk,pk,bk⟩:=Metric.continuousAt_iff.mp K (actualSoftBudget m) (actual_soft_budget_positive m)
  refine ⟨min ru rk,lt_min pu pk,fun k small=>⟨?_,?_⟩⟩
  · simpa only [add_zero,dist_eq_norm] using (bu (x:=k)
      (by simpa only [dist_eq_norm,sub_zero] using small.trans_le (min_le_left ru rk))).le
  · simpa only [neg_zero,dist_eq_norm] using (bk (x:=k)
      (by simpa only [dist_eq_norm,sub_zero] using small.trans_le (min_le_right ru rk))).le

def actualCoupledNoetherRadius (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (m : ℕ) : ℝ:=
  (coupled_radius_exists event reader age F leg m).choose

def actualCoupledNoetherScale (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (m : ℕ) : ℝ:=
  min (actualCoupledNoetherRadius event reader age F leg m/2) (actualSoftBudget m)

def actualCoupledNoetherTransfer (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (direction : PhysicalMomentum) (m : ℕ) : PhysicalMomentum:=
  actualCoupledNoetherScale event reader age F leg m • direction

theorem actual_coupled_noether_scale_positive (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (m : ℕ) :
    0<actualCoupledNoetherScale event reader age F leg m :=
  lt_min (half_pos (coupled_radius_exists event reader age F leg m).choose_spec.1) (actual_soft_budget_positive m)

theorem actual_coupled_noether_transfer_norm (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualCoupledNoetherTransfer event reader age F leg direction m‖=actualCoupledNoetherScale event reader age F leg m := by
  rw [actualCoupledNoetherTransfer,norm_smul,unit,mul_one,Real.norm_eq_abs,
    abs_of_pos (actual_coupled_noether_scale_positive event reader age F leg m)]

theorem actual_coupled_noether_transfer_nonzero (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    actualCoupledNoetherTransfer event reader age F leg direction m≠0 := by
  apply norm_ne_zero_iff.mp
  rw [actual_coupled_noether_transfer_norm event reader age F leg direction unit m]
  exact (actual_coupled_noether_scale_positive event reader age F leg m).ne'

theorem actual_coupled_noether_transfer_bound (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualCoupledNoetherTransfer event reader age F leg direction m‖≤actualSoftBudget m := by
  rw [actual_coupled_noether_transfer_norm event reader age F leg direction unit m]
  exact min_le_right _ _

theorem actual_coupled_noether_frame_error (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualElectronPhysicalUnit (event.momentum+actualCoupledNoetherTransfer event reader age F leg direction m) F event.energy leg-
      actualElectronPhysicalUnit event.momentum F event.energy leg‖≤actualSoftBudget m ∧
    ‖dressedNoetherKernel event (-actualCoupledNoetherTransfer event reader age F leg direction m) reader age 0-
      dressedNoetherKernel event 0 reader age 0‖≤actualSoftBudget m := by
  apply (coupled_radius_exists event reader age F leg m).choose_spec.2
  rw [actual_coupled_noether_transfer_norm event reader age F leg direction unit m]
  exact (min_le_left _ _).trans_lt (half_lt_self (coupled_radius_exists event reader age F leg m).choose_spec.1)

def actualCoupledPhysicalFamily (event : DressedEvent) (reader : Field289) (age : ℝ) (leg : CompositeLeg)
    (direction : PhysicalMomentum) (m : ℕ) : ElectronFamily:=
  ⟨fun F=>actualElectronPhysicalUnit (event.momentum+actualCoupledNoetherTransfer event reader age F leg direction m) F event.energy leg,
    1,zero_le_one,fun F=>(actual_electron_physical_unit_norm _ F event.energy event.nonreal leg).le⟩

def actualCoupledPhysicalState (event : DressedEvent) (reader : Field289) (age : ℝ) (leg : CompositeLeg)
    (direction : PhysicalMomentum) (m : ℕ) : ElectronHistory:=
  (actualCoupledPhysicalFamily event reader age leg direction m : ElectronHistory)

theorem actual_coupled_physical_state_norm (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (m : ℕ) :‖actualCoupledPhysicalState event reader age leg direction m‖=1 := by
  have convergence:=norm_tendsto GaussUnitaryHistory.sourceFilter (actualCoupledPhysicalFamily event reader age leg direction m)
  have constant : Tendsto (fun _ : GaussUnitaryHistory.Index=>(1:ℝ)) GaussUnitaryHistory.sourceFilter
      (𝓝 ‖actualCoupledPhysicalFamily event reader age leg direction m‖):=
    convergence.congr' (Eventually.of_forall (fun F=>actual_electron_physical_unit_norm _ F event.energy event.nonreal leg))
  have norm : (1:ℝ)=‖actualCoupledPhysicalFamily event reader age leg direction m‖:=
    tendsto_nhds_unique (tendsto_const_nhds (x:=(1:ℝ))) constant
  rw [actualCoupledPhysicalState,UniformSpace.Completion.norm_coe,←norm]

theorem actual_coupled_physical_state_error (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualCoupledPhysicalState event reader age leg direction m-
      actualElectronPhysicalState event.momentum event.energy event.nonreal leg‖≤actualSoftBudget m := by
  rw [actualCoupledPhysicalState,actualElectronPhysicalState,←UniformSpace.Completion.coe_sub,UniformSpace.Completion.norm_coe]
  exact norm_le_of_eventually GaussUnitaryHistory.sourceFilter _ _
    (Eventually.of_forall (fun F=>(actual_coupled_noether_frame_error event reader age F leg direction unit m).1))

private theorem kernel_frame_bound (event : DressedEvent) (reader : Field289) (age : ℝ)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖dressedNoetherKernel event (-actualCoupledNoetherTransfer event reader age F leg direction m) reader age 0‖≤
      ‖dressedNoetherKernel event 0 reader age 0‖+actualSoftBudget m := by
  calc
    _=‖(dressedNoetherKernel event (-actualCoupledNoetherTransfer event reader age F leg direction m) reader age 0-
      dressedNoetherKernel event 0 reader age 0)+dressedNoetherKernel event 0 reader age 0‖ :=
      (congrArg norm (sub_add_cancel _ _)).symm
    _≤_ :=(norm_add_le _ _).trans (by
      have paid:=(actual_coupled_noether_frame_error event reader age F leg direction unit m).2
      linarith)

/-- Its uniform bound comes from the actual varying complete kernel, not a supplied operator-family certificate. -/
def actualCoupledNoetherOperators (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    SourceFamilyOperator.Operator GaussUnitaryHistory.Index H :=
  ⟨fun F=>dressedNoetherKernel event (-actualCoupledNoetherTransfer event reader age F leg direction m) reader age 0,
    ‖dressedNoetherKernel event 0 reader age 0‖+actualSoftBudget m,
    add_nonneg (norm_nonneg _) (actual_soft_budget_positive m).le,
    fun F x=>((dressedNoetherKernel event (-actualCoupledNoetherTransfer event reader age F leg direction m) reader age 0).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (kernel_frame_bound event reader age F leg direction unit m) (norm_nonneg x))⟩

def actualCoupledNoetherOperator (event : DressedEvent) (reader : Field289) (age : ℝ)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) : ElectronHistory→L[ℂ]ElectronHistory :=
  lift GaussUnitaryHistory.sourceFilter (actualCoupledNoetherOperators event reader age leg direction unit m)

end LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver
