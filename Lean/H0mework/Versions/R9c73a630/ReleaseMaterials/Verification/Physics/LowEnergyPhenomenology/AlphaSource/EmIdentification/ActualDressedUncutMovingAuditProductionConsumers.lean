import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutMomentum
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutMovingCoulomb

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUncutMovingAudit
elab "checked_dressed_uncut_current_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous).type
theorem checked_dressed_uncut_current_continuous : checked_dressed_uncut_current_continuousContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous

elab "checked_dressed_uncut_matrix_joint_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous).type
theorem checked_dressed_uncut_matrix_joint_continuous : checked_dressed_uncut_matrix_joint_continuousContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous

elab "checked_dressed_uncut_moving_potentialContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_moving_potential).type
theorem checked_dressed_uncut_moving_potential : checked_dressed_uncut_moving_potentialContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_moving_potential

elab "checked_dressed_moving_static_uniformContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform).type
theorem checked_dressed_moving_static_uniform : checked_dressed_moving_static_uniformContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform

elab "checked_dressed_moving_static_dominationContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination).type
theorem checked_dressed_moving_static_domination : checked_dressed_moving_static_dominationContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination

elab "checked_moving_coulomb_radius_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_radius_positive).type
theorem checked_moving_coulomb_radius_positive : checked_moving_coulomb_radius_positiveContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_radius_positive

elab "checked_moving_cut_symbol_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_cut_symbol_return).type
theorem checked_moving_cut_symbol_return : checked_moving_cut_symbol_returnContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_cut_symbol_return

elab "checked_moving_coulomb_symbol_boundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound).type
theorem checked_moving_coulomb_symbol_bound : checked_moving_coulomb_symbol_boundContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound

elab "checked_moving_coulomb_packet_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_integrable).type
theorem checked_moving_coulomb_packet_integrable : checked_moving_coulomb_packet_integrableContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_integrable

elab "checked_moving_coulomb_packet_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit).type
theorem checked_moving_coulomb_packet_limit : checked_moving_coulomb_packet_limitContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit

elab "checked_moving_coulomb_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit).type
theorem checked_moving_coulomb_spatial_limit : checked_moving_coulomb_spatial_limitContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit

elab "checked_moving_coulomb_origin_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_origin_spatial_limit).type
theorem checked_moving_coulomb_origin_spatial_limit : checked_moving_coulomb_origin_spatial_limitContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_origin_spatial_limit

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumStaticPoleResponse
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic ActualEMCarrierOwn
open PreparationVacuumOriginalGreenFeedback MeasureTheory Filter Set
open ActualDressedFullCoulomb ActualDressedUncutCurrent ActualDressedUncutCoulomb
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩
open ActualDressedUncutMoving
attribute [local irreducible] wholeCoulombIRSymbol wholeStaticLimit dressedUncutCurrent

theorem checked_true_fourier_endpoints (detector source : DressedEvent) (scale : ℝ) (k : PhysicalMomentum) :
    dressedUncutMatrixRead detector source (scale • k) (wholeCoulombIRSymbol scale k)=
      dotProduct (dressedUncutCurrent detector (-(scale • k)))
        (wholeCoulombIRSymbol scale k*ᵥdressedUncutCurrent source (scale • k)) := by
  exact dressed_uncut_matrix_read detector source (scale • k) (wholeCoulombIRSymbol scale k)

theorem checked_actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp }⟩

theorem checked_actual_active_window_nonempty (detector source : DressedEvent) :
    ∃scale : ℝ,0 < scale ∧ ∃k : PhysicalMomentum,0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source := by
  have oneNotZero : (1:Fin 3)≠0 := by decide
  have twoNotZero : (2:Fin 3)≠0 := by decide
  refine ⟨movingCoulombRadius detector source/2,half_pos (moving_coulomb_radius_positive detector source),
    (fun i=>if i=0 then 1 else 0),?_,?_⟩
  · norm_num [spatialSquare,oneNotZero,twoNotZero]
  · norm_num [spatialSquare,oneNotZero,twoNotZero]
    linarith [moving_coulomb_radius_positive detector source]

theorem checked_zero_momentum_inactive (detector source : DressedEvent) (scale : ℝ) : movingCoulombSymbol detector source scale 0=0 := by
  norm_num [movingCoulombSymbol,spatialSquare]

end LowEnergy.GaussComposite.ActualDressedUncutMovingAudit

