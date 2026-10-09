import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Partner
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.ChargePayment

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath

structure EnzymeBathContract : Prop where
  actualSource : type_of% Actual.actual_live_capture
  generatedPartner : type_of% Partner.actual_generated_partner
  templateMaterial : type_of% Primary.original_formula
  templateCharge : type_of% Primary.original_charge
  sourceBonds : type_of% Joint.source_bonds
  noDangling : type_of% Joint.no_dangling
  wholeMaterial : type_of% Joint.whole_material
  wholeCharge : type_of% Joint.whole_charge
  particleCharge : type_of% Joint.particle_charge
  oldParticles : type_of% Joint.old_particle_retained
  actualComponentPayment : type_of% source_component_paid
  jointField : type_of% Joint.joint_field
  actualPulse : type_of% source_joint_pulse
  energyPayment : type_of% Joint.returned_energy
  wholeCarrier : type_of% Joint.pulse_whole
  inventory : type_of% whole_inventory
  cut : type_of% actual_cut
  guardCut : type_of% Source.guard_cut
  rawNoGuard : type_of% Source.advance_no_guard
  pendingMaterial : type_of% Actual.initial_pending_material
  sourceResume : type_of% Source.source_preserved

theorem sourceGeneratedEnzymeBath : EnzymeBathContract :=
  ⟨Actual.actual_live_capture,Partner.actual_generated_partner,Primary.original_formula,Primary.original_charge,
    Joint.source_bonds,Joint.no_dangling,Joint.whole_material,Joint.whole_charge,Joint.particle_charge,
    Joint.old_particle_retained,source_component_paid,Joint.joint_field,source_joint_pulse,
    Joint.returned_energy,Joint.pulse_whole,whole_inventory,actual_cut,Source.guard_cut,
    Source.advance_no_guard,Actual.initial_pending_material,Source.source_preserved⟩

end CPS1EnzymeBath
