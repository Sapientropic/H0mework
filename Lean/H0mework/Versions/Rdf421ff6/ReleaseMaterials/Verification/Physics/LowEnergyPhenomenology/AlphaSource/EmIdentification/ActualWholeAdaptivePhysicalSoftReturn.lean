import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPhysicalMomentumSoftSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronWholeChargeSoft
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open ActualElectronPhysicalJointInverse CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumJointFieldResponse SourceFamilyHilbert SourceFamilyOperator Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] jointResolvent jointGenerator actualElectronPhysicalUnit chargeReader

def actualSoftBudget (m : ℕ) : ℝ:=(1/2:ℝ)^m

theorem actual_soft_budget_positive (m : ℕ) : 0<actualSoftBudget m:=pow_pos (by norm_num) m

theorem actual_soft_budget_tendsto : Tendsto actualSoftBudget atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The actual finite-frame physical inverse normalization generates its own positive transfer radius. -/
private theorem physical_soft_radius_exists (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (m : ℕ) :
    ∃r : ℝ,0<r ∧ ∀k : PhysicalMomentum,‖k‖<r→
      ‖actualElectronPhysicalUnit (p+k) F z leg-actualElectronPhysicalUnit p F z leg‖<actualSoftBudget m := by
  have continuous : ContinuousAt (fun k : PhysicalMomentum=>actualElectronPhysicalUnit (p+k) F z leg) 0 :=
    ((actual_electron_physical_unit_continuous F z hz leg).comp ((continuous_const (y:=p)).add continuous_id)).continuousAt
  obtain ⟨r,positive,bound⟩:=Metric.continuousAt_iff.mp continuous (actualSoftBudget m) (actual_soft_budget_positive m)
  refine ⟨r,positive,fun k hk=>?_⟩
  simpa only [add_zero,dist_eq_norm,sub_zero] using bound (x:=k) (by simpa only [dist_eq_norm,sub_zero] using hk)

def actualPhysicalSoftRadius (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (m : ℕ) : ℝ:=
  (physical_soft_radius_exists p F z hz leg m).choose

theorem actual_physical_soft_radius_positive (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (m : ℕ) :0<actualPhysicalSoftRadius p F z hz leg m :=
  (physical_soft_radius_exists p F z hz leg m).choose_spec.1

def actualPhysicalSoftScale (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (m : ℕ) : ℝ:=
  min (actualPhysicalSoftRadius p F z hz leg m/2) (actualSoftBudget m)

def actualPhysicalSoftTransfer (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (direction : PhysicalMomentum) (m : ℕ) : PhysicalMomentum:=
  actualPhysicalSoftScale p F z hz leg m • direction

theorem actual_physical_soft_scale_positive (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (m : ℕ) :0<actualPhysicalSoftScale p F z hz leg m :=
  lt_min (half_pos (actual_physical_soft_radius_positive p F z hz leg m)) (actual_soft_budget_positive m)

theorem actual_physical_soft_transfer_norm (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualPhysicalSoftTransfer p F z hz leg direction m‖=actualPhysicalSoftScale p F z hz leg m := by
  rw [actualPhysicalSoftTransfer,norm_smul,unit,mul_one,Real.norm_eq_abs,
    abs_of_pos (actual_physical_soft_scale_positive p F z hz leg m)]

theorem actual_physical_soft_transfer_nonzero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    actualPhysicalSoftTransfer p F z hz leg direction m≠0 := by
  apply norm_ne_zero_iff.mp
  rw [actual_physical_soft_transfer_norm p F z hz leg direction unit m]
  exact (actual_physical_soft_scale_positive p F z hz leg m).ne'

theorem actual_physical_soft_transfer_bound (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualPhysicalSoftTransfer p F z hz leg direction m‖≤actualSoftBudget m := by
  rw [actual_physical_soft_transfer_norm p F z hz leg direction unit m]
  exact min_le_right _ _

theorem actual_physical_soft_transfer_tendsto (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) :
    Tendsto (actualPhysicalSoftTransfer p F z hz leg direction) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  exact (actual_soft_budget_tendsto.eventually (eventually_lt_nhds positive)).mono (fun m small=>by
    rw [dist_eq_norm,sub_zero]
    exact (actual_physical_soft_transfer_bound p F z hz leg direction unit m).trans_lt small)

theorem actual_physical_soft_unit_error (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualElectronPhysicalUnit (p+actualPhysicalSoftTransfer p F z hz leg direction m) F z leg-
      actualElectronPhysicalUnit p F z leg‖≤actualSoftBudget m := by
  apply le_of_lt
  apply (physical_soft_radius_exists p F z hz leg m).choose_spec.2
  rw [actual_physical_soft_transfer_norm p F z hz leg direction unit m]
  exact (min_le_left _ _).trans_lt (half_lt_self (actual_physical_soft_radius_positive p F z hz leg m))

/-- Every frame uses its generated radius; the physical direction and actual endpoint are unchanged. -/
def actualAdaptivePhysicalFamily (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg)
    (direction : PhysicalMomentum) (m : ℕ) : ElectronFamily :=
  ⟨fun F=>actualElectronPhysicalUnit (p+actualPhysicalSoftTransfer p F z hz leg direction m) F z leg,
    1,zero_le_one,fun F=>(actual_electron_physical_unit_norm _ F z hz leg).le⟩

def actualAdaptivePhysicalState (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg)
    (direction : PhysicalMomentum) (m : ℕ) : ElectronHistory:=
  (actualAdaptivePhysicalFamily p z hz leg direction m : ElectronHistory)

theorem actual_adaptive_physical_state_norm (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (m : ℕ) :
    ‖actualAdaptivePhysicalState p z hz leg direction m‖=1 := by
  have convergence:=norm_tendsto GaussUnitaryHistory.sourceFilter
    (actualAdaptivePhysicalFamily p z hz leg direction m)
  have constant : Tendsto (fun _ : GaussUnitaryHistory.Index=>(1:ℝ)) GaussUnitaryHistory.sourceFilter
      (𝓝 ‖actualAdaptivePhysicalFamily p z hz leg direction m‖):=
    convergence.congr' (Eventually.of_forall (fun F=>actual_electron_physical_unit_norm
      (p+actualPhysicalSoftTransfer p F z hz leg direction m) F z hz leg))
  have norm : (1:ℝ)=‖actualAdaptivePhysicalFamily p z hz leg direction m‖:=
    tendsto_nhds_unique (tendsto_const_nhds (x:=(1:ℝ))) constant
  rw [actualAdaptivePhysicalState,UniformSpace.Completion.norm_coe,←norm]

theorem actual_adaptive_physical_state_error (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg)
    (direction : PhysicalMomentum) (unit : ‖direction‖=1) (m : ℕ) :
    ‖actualAdaptivePhysicalState p z hz leg direction m-actualElectronPhysicalState p z hz leg‖≤actualSoftBudget m := by
  rw [actualAdaptivePhysicalState,actualElectronPhysicalState,←UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.norm_coe]
  exact norm_le_of_eventually GaussUnitaryHistory.sourceFilter _ _
    (Eventually.of_forall (actual_physical_soft_unit_error p · z hz leg direction unit m))

theorem actual_adaptive_physical_state_soft_return (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0)
    (leg : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) :
    Tendsto (actualAdaptivePhysicalState p z hz leg direction) atTop (𝓝 (actualElectronPhysicalState p z hz leg)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  have near:=actual_soft_budget_tendsto.eventually (eventually_lt_nhds positive)
  exact near.mono (fun m small=>by rw [dist_eq_norm];exact (actual_adaptive_physical_state_error p z hz leg direction unit m).trans_lt small)

/-- The two genuine physical inverses amputate on their actual output endpoints; the paired source dual is retained as supplied by the left leg. -/
def actualAdaptiveAmputatedChargeRead (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z w : ℂ)
    (hz : z.im≠0) (left right : CompositeLeg) (direction : PhysicalMomentum) (m : ℕ) : ℂ:=
  let k:=actualPhysicalSoftTransfer p F z hz left direction m
  inner ℂ ((jointGenerator (p+k) F z 0).adjoint (actualElectronPhysicalUnit (p+k) F z left))
    (actualElectronPhysicalChargeVertex p k F z w (jointGenerator p F w 0 (actualElectronPhysicalUnit p F w right)))

attribute [local irreducible] actualAdaptiveAmputatedChargeRead

theorem actual_adaptive_amputated_charge_value (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (left right : CompositeLeg) (direction : PhysicalMomentum) (m : ℕ) :
    actualAdaptiveAmputatedChargeRead p F z w hz left right direction m=
      inner ℂ (actualElectronPhysicalUnit (p+actualPhysicalSoftTransfer p F z hz left direction m) F z left)
        (chargeReader sourcePhaseGaugeLie (actualElectronPhysicalUnit p F w right)) := by
  unfold actualAdaptiveAmputatedChargeRead
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ _ ((jointGenerator _ F z 0*actualElectronPhysicalChargeVertex p _ F z w*jointGenerator p F w 0) _)=_
  rw [actual_electron_physical_charge_amputation p _ F z w hz hw]

theorem actual_adaptive_amputated_charge_history_return (p : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (left right : CompositeLeg) (direction : PhysicalMomentum) (m : ℕ) :
    Tendsto (fun F=>actualAdaptiveAmputatedChargeRead p F z w hz left right direction m)
      GaussUnitaryHistory.sourceFilter (𝓝 (inner ℂ (actualAdaptivePhysicalState p z hz left direction m)
        (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie) (actualElectronPhysicalState p w hw right)))) := by
  change Tendsto (fun F=>actualAdaptiveAmputatedChargeRead p F z w hz left right direction m)
    GaussUnitaryHistory.sourceFilter (𝓝 (inner ℂ
      (actualAdaptivePhysicalFamily p z hz left direction m : ElectronHistory)
      (SourceFamilyOperator.lift GaussUnitaryHistory.sourceFilter
        (SourceFamilyOperator.constant (chargeReader sourcePhaseGaugeLie))
        (actualElectronPhysicalStateFamily p w hw right : ElectronHistory))))
  rw [SourceFamilyOperator.lift_coe,inner_coe]
  exact (pair_tendsto GaussUnitaryHistory.sourceFilter (actualAdaptivePhysicalFamily p z hz left direction m)
    (act GaussUnitaryHistory.sourceFilter (constant (chargeReader sourcePhaseGaugeLie))
      (actualElectronPhysicalStateFamily p w hw right))).congr'
    (Eventually.of_forall (fun F=>(actual_adaptive_amputated_charge_value p F z w hz hw left right direction m).symm))

/-- The source-owned nonzero physical transfer curve returns the original whole-carrier charge read, retaining the actual output mixing correction. -/
theorem actual_adaptive_amputated_charge_soft_return (p : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (left right : CompositeLeg) (direction : PhysicalMomentum) (unit : ‖direction‖=1) :
    Tendsto (fun m=>inner ℂ (actualAdaptivePhysicalState p z hz left direction m)
      (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie) (actualElectronPhysicalState p w hw right))) atTop
      (𝓝 (actualElectronSign right*inner ℂ (actualElectronPhysicalState p z hz left) (actualElectronPhysicalState p w hw right)+
        inner ℂ (actualElectronPhysicalState p z hz left) (actualWholeElectronCorrection p w hw right))) := by
  rw [←actual_whole_electron_paired_charge p p z w hz hw left right]
  exact (actual_adaptive_physical_state_soft_return p z hz left direction unit).inner tendsto_const_nhds

end LowEnergy.GaussComposite.ActualElectronWholeChargeSoft
