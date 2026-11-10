import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMClockResidue

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMSpatialClockPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumSourcePreparedResponse PreparationVacuumActionFieldLift SourceGraph
open ActualDressedFullCoulomb ActualDressedLeftFreeJet ActualDressedEMTemporal ActualDressedNumberField
open ActualSourcePreparedJointNoetherSourcePrice ActualSourcePreparedEMClockResidue
open ActualSourcePreparedEMTemporalFreeReturn LowEnergy.ActualMixedNoetherTimePriceOwn
attribute [local irreducible] emTemporalPrice freeCompressionCurrent jointCResolvent jointCurrent
  emTemporalReader prepared sourceProfile originalFreeCurrentPrice sourceEMClockResidue

def sourceEMSpatialClockBudget (event : DressedEvent) (n : PhysicalMomentum)
    (radius : ℝ) (j : Fin 289) : ℝ :=
  let current:=2*originalFreeCurrentPrice (fieldUnit j) event.momentum event.frame+
    radius*‖jointCurrent n event.frame 0 0 (fieldUnit j)-jointCurrent 0 event.frame 0 0 (fieldUnit j)‖
  let green:=1/|event.energy.im|
  let reader:=‖emTemporalReader event.momentum event.frame‖
  (current*green^2*reader+current*green^3*reader)*
    (1+‖prepared (sourceProfile event.epsilon event.precision)‖^2)

private theorem core_price (a b l r W Q A B c : ℝ)
    (a0 : 0≤a) (b0 : 0≤b) (l0 : 0≤l) (r0 : 0≤r) (w0 : 0≤W) (q0 : 0≤Q)
    (a1 : a≤A) (b1 : b≤B) (l1 : l≤c) (r1 : r≤c) :
    ((a+b)*l*W*r+l^2*a*W*r+l*W*r^2*b)*Q≤
      ((A+B)*c^2*W+(A+B)*c^3*W)*Q := by
  have A0:=a0.trans a1
  have B0:=b0.trans b1
  have c0:=l0.trans l1
  have upper : ((a+b)*l*W*r+l^2*a*W*r+l*W*r^2*b)*Q≤
      ((A+B)*c*W*c+c^2*A*W*c+c*W*c^2*B)*Q := by
    gcongr
  exact upper.trans_eq (by ring)

/-- The same actual moving current and both free Green legs pay one explicit
spatial-ball price; its source energy and prepared state are unchanged. -/
theorem source_em_spatial_temporal_price (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (radius : ℝ) (small : eps^2≤radius) (j : Fin 289) :
    emTemporalPrice event (eps^2 • n) (fieldUnit j)≤ sourceEMSpatialClockBudget event n radius j := by
  have moving:=source_moving_free_current_price event eps n (fieldUnit j)
  have left : ‖freeCompressionCurrent (event.momentum-eps^2 • n) event.frame (fieldUnit j)‖≤
      originalFreeCurrentPrice (fieldUnit j) event.momentum event.frame+
        radius*‖jointCurrent n event.frame 0 0 (fieldUnit j)-jointCurrent 0 event.frame 0 0 (fieldUnit j)‖ :=
    moving.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right small (norm_nonneg _)))
  have right:=originalFreeCurrent_price (fieldUnit j) event.momentum event.frame
  have leftGreen:=originalFreeResolvent_price (event.momentum-eps^2 • n) event.frame event.energy event.nonreal
  have rightGreen:=originalFreeResolvent_price event.momentum event.frame event.energy event.nonreal
  have source:=core_price
    ‖freeCompressionCurrent (event.momentum-eps^2 • n) event.frame (fieldUnit j)‖
    ‖freeCompressionCurrent event.momentum event.frame (fieldUnit j)‖
    ‖jointCResolvent (event.momentum-eps^2 • n) event.frame event.energy 0‖
    ‖jointCResolvent event.momentum event.frame event.energy 0‖
    ‖emTemporalReader event.momentum event.frame‖
    (1+‖prepared (sourceProfile event.epsilon event.precision)‖^2)
    (originalFreeCurrentPrice (fieldUnit j) event.momentum event.frame+
      radius*‖jointCurrent n event.frame 0 0 (fieldUnit j)-jointCurrent 0 event.frame 0 0 (fieldUnit j)‖)
    (originalFreeCurrentPrice (fieldUnit j) event.momentum event.frame) (1/|event.energy.im|)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (by positivity) left right leftGreen rightGreen
  unfold emTemporalPrice sourceEMSpatialClockBudget
  exact source.trans_eq (by ring)

/-- Both independent scales consume the same source price on the full EM row;
there is no relation between epsilon and sigma in this bound. -/
theorem source_em_spatial_clock_uniform_price (event : DressedEvent) (eps sigma : ℝ)
    (n : PhysicalMomentum) (radius : ℝ) (small : eps^2≤radius)
    (positive : 0<sigma) (clockSmall : sigma≤1) (j : Fin 289) :
    sigma^2*‖sourcePreparedEMTemporalPi event (eps^2 • n) (sigma:ℂ) j‖≤
      2*sourceEMSpatialClockBudget event n radius j :=
  (source_prepared_em_temporal_pi_two_clock_price event (eps^2 • n) sigma positive clockSmall j).trans
    (mul_le_mul_of_nonneg_left (source_em_spatial_temporal_price event eps n radius small j) (by norm_num))

/-- The generated finite clock residue receives the same spatial-ball price
without replacing it by a zero-transfer coefficient or an experimental target. -/
theorem source_em_spatial_residue_uniform_price (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (radius : ℝ) (small : eps^2≤radius) (j : Fin 289) :
    ‖sourceEMClockResidue event eps n j‖≤2*sourceEMSpatialClockBudget event n radius j :=
  (source_em_clock_residue_price event eps n j).trans
    (mul_le_mul_of_nonneg_left (source_em_spatial_temporal_price event eps n radius small j) (by norm_num))

end LowEnergy.GaussComposite.ActualSourcePreparedEMSpatialClockPrice
