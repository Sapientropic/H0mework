import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.NoetherSourceCoefficientPrices

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualMixedNoetherTimePriceOwn
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse PreparationVacuumFullFieldRiesz
open PreparationVacuumJointFieldResponse PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalHalfAxis PreparationVacuumSourcePreparedResponse PreparationVacuumActionFieldLift
open GaussComposite.ActualDressedLeftFreeJet GaussComposite.ActualDressedCubicPrice GaussComposite.ActualDressedNumberField
open GaussComposite.ActualDressedSylvester
open GaussComposite.ActualDressedNoether GaussComposite.ActualDressedFullCoulomb GaussComposite.SourceGraph
open ActualSourceMixed289ResponseOwn ActualQuantitativePreparedFrameOwn
open scoped BigOperators Topology InnerProductSpace
attribute [local irreducible] jointCurrent jointResolvent noetherReader noetherReaderContact freeCompressionCurrent
  jointCResolvent actualA completeCubicNoetherPrice prepared sourceProfile actualPrepared

private def cubicCore (cp b c d contact jg jt a : ℝ) : ℝ :=
  (cp*b*c*d + b^2*cp*c*d + b*contact*d + b*c*(d^2*jg))*(1+a)^2 + b*c*d*(3*jt*(1+a)^2)

private theorem cubicCore_mono (cp b c d contact jg jt a CP B C D CONTACT JG JT A : ℝ)
    (h0cp : 0 ≤ cp) (h0b : 0 ≤ b) (h0c : 0 ≤ c) (h0d : 0 ≤ d)
    (h0contact : 0 ≤ contact) (h0jg : 0 ≤ jg) (h0jt : 0 ≤ jt) (h0a : 0 ≤ a)
    (hcp : cp ≤ CP) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D)
    (hcontact : contact ≤ CONTACT) (hjg : jg ≤ JG) (hjt : jt ≤ JT) (ha : a ≤ A) :
    cubicCore cp b c d contact jg jt a ≤ cubicCore CP B C D CONTACT JG JT A := by
  have cp0 := h0cp.trans hcp
  have b0 := h0b.trans hb
  have c0 := h0c.trans hc
  have d0 := h0d.trans hd
  have contact0 := h0contact.trans hcontact
  have jg0 := h0jg.trans hjg
  have jt0 := h0jt.trans hjt
  have a0 := h0a.trans ha
  unfold cubicCore
  gcongr

private theorem original_complete_cubic_formula (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) :
    completeCubicNoetherPrice event transfer reader force =
      cubicCore ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖
        ‖noetherReader reader event.momentum event.frame 0‖
        ‖jointResolvent event.momentum event.frame event.energy 0‖
        ‖noetherReaderContact reader force event.momentum event.frame‖
        ‖jointCurrent event.momentum event.frame event.energy 0 force‖
        ‖jointCurrent event.momentum event.frame 0 0 force‖ ‖actualA event.momentum event.frame‖ *
      (1 + ‖prepared (sourceProfile event.epsilon event.precision)‖^2) := by
  unfold completeCubicNoetherPrice
  rfl

-- All five original product derivatives and the actual corrected Noether contact are paid here.
def sourceCompleteCubicNoetherPrice (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) : ℝ :=
  2 * cubicCore (originalFreeCurrentPrice force (event.momentum-transfer) event.frame) (1 / |event.energy.im|)
    (originalNoetherReaderPrice reader event.momentum event.frame)
    (originalJointResolventPrice event.momentum event.frame event.energy)
    (originalNoetherContactPrice reader force event.momentum event.frame)
    (originalJointCurrentPrice force event.momentum event.frame)
    (originalJointCurrentPrice force event.momentum event.frame)
    (originalCompactYPrice 0 event.momentum event.frame 0)

private theorem normalized_factor (price x : ℝ) (unit : x = 1) : price * (1+x^2) = 2*price := by
  rw [unit]
  ring

private theorem original_complete_cubic_normalized (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) :
    completeCubicNoetherPrice event transfer reader force =
      2 * cubicCore ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖
        ‖noetherReader reader event.momentum event.frame 0‖
        ‖jointResolvent event.momentum event.frame event.energy 0‖
        ‖noetherReaderContact reader force event.momentum event.frame‖
        ‖jointCurrent event.momentum event.frame event.energy 0 force‖
        ‖jointCurrent event.momentum event.frame 0 0 force‖ ‖actualA event.momentum event.frame‖ := by
  have background : ‖prepared (sourceProfile event.epsilon event.precision)‖ = 1 := by
    simpa only [actualPrepared] using actualPrepared_norm event.epsilon event.precision
  exact (original_complete_cubic_formula event transfer reader force).trans (normalized_factor _ _ background)

theorem original_complete_cubic_source_enclosure (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) :
    completeCubicNoetherPrice event transfer reader force ≤ sourceCompleteCubicNoetherPrice event transfer reader force := by
  rw [original_complete_cubic_normalized]
  unfold sourceCompleteCubicNoetherPrice
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  have hA : ‖actualA event.momentum event.frame‖ ≤ originalCompactYPrice 0 event.momentum event.frame 0 := by
    simpa only [actualA] using originalCompactY_price 0 event.momentum event.frame 0
  exact cubicCore_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (originalFreeCurrent_price force (event.momentum-transfer) event.frame)
    (originalFreeResolvent_price (event.momentum-transfer) event.frame event.energy event.nonreal)
    (originalNoetherReader_price reader event.momentum event.frame)
    (originalJointResolvent_price event.momentum event.frame event.energy event.nonreal)
    (originalNoetherContact_price reader force event.momentum event.frame)
    (originalJointCurrent_price force event.momentum event.frame event.energy)
    (originalJointCurrent_price force event.momentum event.frame 0)
    hA

theorem sourceCompleteCubicNoetherPrice_nonnegative (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) :
    0 ≤ sourceCompleteCubicNoetherPrice event transfer reader force :=
  (complete_cubic_noether_price_nonneg event transfer reader force).trans
    (original_complete_cubic_source_enclosure event transfer reader force)

theorem actual_complete_noether_source_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (i : Fin 289) :
    ‖(dressedNoetherJet event transfer (fun _ => ⟨force,0,0⟩) age i).value‖ ≤
      sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) force * (1+|age|)^3 :=
  (actual_complete_noether_cubic_jet_price event transfer force age i).trans
    (mul_le_mul_of_nonneg_right (original_complete_cubic_source_enclosure event transfer (fieldUnit i) force) (by positivity))

theorem actual_static_polarization_source_laplace_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer lambda i j‖ ≤
      sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) *
        (∫ age : ℝ in Set.Ioi 0, Real.exp (-(lambda.re*age))*(1+age)^3) :=
  (actual_static_polarization_cubic_laplace_price event transfer lambda positive i j).trans
    (mul_le_mul_of_nonneg_right (original_complete_cubic_source_enclosure event transfer (fieldUnit i) (fieldUnit j))
      (MeasureTheory.integral_nonneg_of_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with age future
        have age0 : 0 ≤ age := future.le
        positivity)))

theorem actual_static_polarization_source_sigma_four_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (sigma : ℝ) (positive : 0 < sigma) (small : sigma ≤ 1) (i j : Fin 289) :
    sigma^4 * ‖dressedStaticPolarization event transfer (sigma : ℂ) i j‖ ≤
      56 * sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) :=
  (actual_static_polarization_sigma_four_price event transfer sigma positive small i j).trans
    (mul_le_mul_of_nonneg_left (original_complete_cubic_source_enclosure event transfer (fieldUnit i) (fieldUnit j)) (by norm_num))

end LowEnergy.ActualMixedNoetherTimePriceOwn
