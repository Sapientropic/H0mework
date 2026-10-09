import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeCoulombDressing

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit
elab "checked_composite_bottom_overlap_boundsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_overlap_bounds).type
theorem checked_composite_bottom_overlap_bounds : checked_composite_bottom_overlap_boundsContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_overlap_bounds

elab "checked_composite_bottom_born_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_read).type
theorem checked_composite_bottom_born_read : checked_composite_bottom_born_readContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_read

elab "checked_composite_bottom_born_boundsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_bounds).type
theorem checked_composite_bottom_born_bounds : checked_composite_bottom_born_boundsContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_bounds

elab "checked_composite_sharp_bottom_overlapContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_sharp_bottom_overlap).type
theorem checked_composite_sharp_bottom_overlap : checked_composite_sharp_bottom_overlapContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_sharp_bottom_overlap

elab "checked_composite_weight_born_dressingContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing).type
theorem checked_composite_weight_born_dressing : checked_composite_weight_born_dressingContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing

elab "checked_composite_coulomb_overlap_boundsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_overlap_bounds).type
theorem checked_composite_coulomb_overlap_bounds : checked_composite_coulomb_overlap_boundsContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_overlap_bounds

elab "checked_composite_coulomb_coefficient_dressingContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing).type
theorem checked_composite_coulomb_coefficient_dressing : checked_composite_coulomb_coefficient_dressingContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing

elab "checked_composite_coulomb_dressing_errorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_dressing_error).type
theorem checked_composite_coulomb_dressing_error : checked_composite_coulomb_dressing_errorContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_dressing_error

elab "checked_composite_coulomb_spatial_dressingContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_spatial_dressing).type
theorem checked_composite_coulomb_spatial_dressing : checked_composite_coulomb_spatial_dressingContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_spatial_dressing

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open LowEnergy.GaussComposite.ActualCompositeFieldCurrent
open LowEnergy.GaussComposite.ActualCompositeCoulombDressing

theorem checked_all_sharp_dressing (dL dR sL sR : CompositeLeg)
    (hdL : dL.sharp=true) (hdR : dR.sharp=true) (hsL : sL.sharp=true) (hsR : sR.sharp=true) :
    compositeCoulombOverlap dL dR sL sR=1 := by
  simp only [compositeCoulombOverlap,(composite_sharp_bottom_overlap dL hdL).1,
    (composite_sharp_bottom_overlap dR hdR).1,(composite_sharp_bottom_overlap sL hsL).1,
    (composite_sharp_bottom_overlap sR hsR).1,one_mul]

theorem checked_born_nonzero (leg : CompositeLeg) : compositeBottomBornWeight leg≠0 :=
  (composite_bottom_born_bounds leg).1.ne'

theorem checked_complete_overlap_nonzero (dL dR sL sR : CompositeLeg) :
    compositeCoulombOverlap dL dR sL sR≠0 :=
  (composite_coulomb_overlap_bounds dL dR sL sR).1.ne'
end LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit

