import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMMovingCoulombPacket

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMMovingCoulombAudit
elab "checked_moving_coulomb_radius_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_radius_positive).type
theorem checked_moving_coulomb_radius_positive : checked_moving_coulomb_radius_positiveContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_radius_positive

elab "checked_moving_coulomb_symbol_boundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_symbol_bound).type
theorem checked_moving_coulomb_symbol_bound : checked_moving_coulomb_symbol_boundContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_symbol_bound

elab "checked_moving_coulomb_packet_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_integrable).type
theorem checked_moving_coulomb_packet_integrable : checked_moving_coulomb_packet_integrableContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_integrable

elab "checked_moving_coulomb_packet_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit).type
theorem checked_moving_coulomb_packet_limit : checked_moving_coulomb_packet_limitContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit

elab "checked_moving_coulomb_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit).type
theorem checked_moving_coulomb_spatial_limit : checked_moving_coulomb_spatial_limitContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit

elab "checked_moving_coulomb_spatial_limit_restContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit_rest).type
theorem checked_moving_coulomb_spatial_limit_rest : checked_moving_coulomb_spatial_limit_restContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit_rest

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open LowEnergy.GaussComposite.ActualEMCarrierOwn LowEnergy.GaussComposite.ActualEMMovingCoulombPacket
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumFullOriginResponse
open PreparationVacuumFullPoleContinuation PreparationVacuumElectromagneticIdentity

theorem checked_packet_same_fourier (d s : ActualEMObservationEnd) (branch : Fin 2)
    (hdz : d.q.z.im≠0) (hdw : d.q.w.im≠0) (hsz : s.q.z.im≠0) (hsw : s.q.w.im≠0)
    (scale : ℝ) (k : PhysicalMomentum)
    (active : 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) <
        (movingCoulombRadius d s branch hdz hdw hsz hsw : ℝ)) :
    movingCoulombSymbol d s branch hdz hdw hsz hsw scale k=
      emMovingWholeRead d s branch (scale • k,0) (wholeCoulombIRSymbol scale k) ∧
    actualMomentum (s.momentum+(-1:ℝ) • (scale • k)) s.momentum 0=sourceStaticSpatialMomentum k scale ∧
    actualMomentum (d.momentum+(1:ℝ) • (scale • k)) d.momentum 0= -sourceStaticSpatialMomentum k scale := by
  exact ⟨by simp only [movingCoulombSymbol,if_pos active],em_moving_static_same_fourier d s scale k⟩

theorem checked_zero_scale_symbol (d s : ActualEMObservationEnd) (branch : Fin 2)
    (hdz : d.q.z.im≠0) (hdw : d.q.w.im≠0) (hsz : s.q.z.im≠0) (hsw : s.q.w.im≠0) (k : PhysicalMomentum) :
    movingCoulombSymbol d s branch hdz hdw hsz hsw 0 k=0 := by
  rw [movingCoulombSymbol,if_neg (by
    intro h
    exact (lt_irrefl (0:ℝ)) h.1)]

theorem checked_zero_momentum_symbol (d s : ActualEMObservationEnd) (branch : Fin 2)
    (hdz : d.q.z.im≠0) (hdw : d.q.w.im≠0) (hsz : s.q.z.im≠0) (hsw : s.q.w.im≠0) (scale : ℝ) :
    movingCoulombSymbol d s branch hdz hdw hsz hsw scale 0=0 := by
  have zero : spatialSquare (0:PhysicalMomentum)=0 := by norm_num [spatialSquare]
  rw [movingCoulombSymbol,if_neg (by
    rintro ⟨_,h,_⟩
    rw [zero] at h
    exact (lt_irrefl (0:ℝ)) h)]

theorem checked_outside_window (d s : ActualEMObservationEnd) (branch : Fin 2)
    (hdz : d.q.z.im≠0) (hdw : d.q.w.im≠0) (hsz : s.q.z.im≠0) (hsw : s.q.w.im≠0)
    (scale : ℝ) (k : PhysicalMomentum)
    (outside : movingCoulombRadius d s branch hdz hdw hsz hsw ≤ scale * Real.sqrt (spatialSquare k)) :
    movingCoulombSymbol d s branch hdz hdw hsz hsw scale k=0 := by
  rw [movingCoulombSymbol,if_neg (by
    rintro ⟨_,_,h⟩
    exact (not_lt.mpr outside) h)]

elab "originalMovingActionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_once_action).type
theorem checked_original_all64_single_hc : originalMovingActionContract :=
  @LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_once_action

theorem checked_original_frequency (frequency : PhysicalMomentum) (j : Fin 3) :
    sourceSpatialMomentum frequency j=(2*Real.pi)*frequency j := rfl
end LowEnergy.GaussComposite.ActualEMMovingCoulombAudit

