import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFullCoulomb
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePreparedPhotonAmplitude

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceEMEventFeed
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumFieldCovector PreparationVacuumFullFieldRiesz
open PreparationVacuumMixedFieldReturn PreparationVacuumSourcePreparedResponse
open PreparationVacuumFieldConstraintResponse
open CanonicalPhysicalYResolvent GaussComposite.SourceGraph
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedSourceResponse
open PreparationPhysicalDressedPhotonCouplingReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalSourcePreparedPhotonReturn
open scoped BigOperators InnerProductSpace
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceDressedAddition
  sourceProfile completedLeg currentVertex finiteFull sourcePhotonWholePair sourcePreparedPhotonAmplitude
  sourceNativeFrequencyPolarization sourcePhotonWholeConfiguration sourcePhotonConfigurationRead sourceTestApprox

private theorem whole_pair_from_vertex (branch : Fin 2) (epsilon s : ℝ)
    (n p k : PhysicalMomentum) (nonzero : epsilon≠0) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (x y : H) :
    (∑i,sourceNativeFrequencyPolarization branch epsilon s n i*
      inner ℂ x (currentVertex (fieldBasis i) p k F cut z w y))=
      sourcePhotonWholePair branch epsilon s n p k F cut z w x y := by
  let a := sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x)
  let b := sourceTestApprox F (finiteFull p F cut w y)
  have original : (∑i,sourceNativeFrequencyPolarization branch epsilon s n i*
      inner ℂ x (currentVertex (fieldBasis i) p k F cut z w y))=
      sourcePhotonConfigurationRead p a b (sourceNativeFrequencyPolarization branch epsilon s n) := by
    unfold sourcePhotonConfigurationRead
    change _=∑i,sourceNativeFrequencyPolarization branch epsilon s n i*(fieldJets (fieldBasis i) p a b).first 0
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun v : ℂ=>sourceNativeFrequencyPolarization branch epsilon s n i*v)
      (currentVertex_original_pair (fieldBasis i) p k F cut z w x y)
  unfold sourcePhotonWholePair
  exact original.trans (sourcePhotonWholeConfiguration_generated branch epsilon s n p nonzero a b)

private theorem whole_pair_smul (branch : Fin 2) (epsilon s : ℝ)
    (n p k : PhysicalMomentum) (nonzero : epsilon≠0) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (c : ℂ) (x : H) :
    sourcePhotonWholePair branch epsilon s n p k F cut z w (c • x) (c • x)=
      (star c*c)*sourcePhotonWholePair branch epsilon s n p k F cut z w x x := by
  rw [←whole_pair_from_vertex branch epsilon s n p k nonzero F cut z w,
    ←whole_pair_from_vertex branch epsilon s n p k nonzero F cut z w]
  simp only [map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def actualPreparationLeg (event : DressedEvent) : H :=
  completedLeg true 1 0 (sourceProfile event.epsilon event.precision)

def actualPreparationScale (event : DressedEvent) : ℂ :=
  ((‖sourceDressedExcitation event.epsilon event.precision‖:ℂ)⁻¹*
    PhysicalEMDressedCharacter.emDressedCharacter true)

attribute [local irreducible] actualPreparationScale actualPreparationLeg

private theorem actual_unit_from_leg (event : DressedEvent) :
    sourceDressedUnit event.epsilon event.precision=
      actualPreparationScale event • actualPreparationLeg event := by
  simpa only [sourceDressedAddition,actualPreparationScale,actualPreparationLeg] using
    source_dressed_unit_original event.epsilon event.precision

/-- The actual Hilbert norm removes the dressing phase, before any Green or photon read. -/
theorem actual_preparation_weight (event : DressedEvent) :
    star (actualPreparationScale event)*actualPreparationScale event=
      ((‖actualPreparationLeg event‖^2:ℝ):ℂ)⁻¹ := by
  have unit := source_dressed_unit_norm event.epsilon event.precision
  rw [actual_unit_from_leg,norm_smul] at unit
  have legPositive : 0<‖actualPreparationLeg event‖ := by
    by_contra h
    have zero : ‖actualPreparationLeg event‖=0:=le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [zero,mul_zero] at unit
    exact zero_ne_one unit
  have normSquare : (‖actualPreparationScale event‖*‖actualPreparationLeg event‖)^2=1:=by
    rw [unit,one_pow]
  have scalar : (star (actualPreparationScale event)*actualPreparationScale event)*
      ((‖actualPreparationLeg event‖^2:ℝ):ℂ)=1 := by
    have normIdent : star (actualPreparationScale event)*actualPreparationScale event=
        (‖actualPreparationScale event‖^2:ℂ) := by
      simpa only [starRingEnd_apply] using Complex.conj_mul' (actualPreparationScale event)
    rw [normIdent]
    exact_mod_cast (show ‖actualPreparationScale event‖^2*‖actualPreparationLeg event‖^2=1 by
      simpa only [mul_pow] using normSquare)
  have nonzero : ((‖actualPreparationLeg event‖^2:ℝ):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 legPositive.ne')
  calc
    _=(star (actualPreparationScale event)*actualPreparationScale event)*
        (((‖actualPreparationLeg event‖^2:ℝ):ℂ)*((‖actualPreparationLeg event‖^2:ℝ):ℂ)⁻¹):=by
      rw [mul_inv_cancel₀ nonzero,mul_one]
    _=((‖actualPreparationLeg event‖^2:ℝ):ℂ)⁻¹:=by rw [←mul_assoc,scalar,one_mul]

/-- The actual connected current directly consumes the original prepared photon amplitude.
    The background is the same source profile, and both complete finite Green legs are unchanged. -/
theorem actual_dressed_photon_connected_feed (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (nonzero : epsilon≠0) :
    (∑i,sourceNativeFrequencyPolarization branch epsilon s n i*dressedCurrent event transfer i)=
      ((‖actualPreparationLeg event‖^2:ℝ):ℂ)⁻¹*
        sourcePreparedPhotonAmplitude branch epsilon s n event.momentum (-transfer)
          event.frame event.cut event.energy event.energy event.epsilon event.precision true true 1 1 0 0-
      sourcePhotonWholePair branch epsilon s n event.momentum (-transfer)
        event.frame event.cut event.energy event.energy
        (prepared (sourceProfile event.epsilon event.precision))
        (prepared (sourceProfile event.epsilon event.precision)) := by
  let u:=sourceDressedUnit event.epsilon event.precision
  let b:=prepared (sourceProfile event.epsilon event.precision)
  let pair (x y : H):=sourcePhotonWholePair branch epsilon s n event.momentum (-transfer)
    event.frame event.cut event.energy event.energy x y
  have excited : pair u u=((‖actualPreparationLeg event‖^2:ℝ):ℂ)⁻¹*
      sourcePreparedPhotonAmplitude branch epsilon s n event.momentum (-transfer)
        event.frame event.cut event.energy event.energy event.epsilon event.precision true true 1 1 0 0 := by
    have same:=congrArg₂ pair (actual_unit_from_leg event) (actual_unit_from_leg event)
    have scale:=whole_pair_smul branch epsilon s n event.momentum (-transfer) nonzero
      event.frame event.cut event.energy event.energy (actualPreparationScale event) (actualPreparationLeg event)
    have weight:=congrArg (fun c : ℂ=>c*pair (actualPreparationLeg event) (actualPreparationLeg event))
      (actual_preparation_weight event)
    have result:=same.trans (scale.trans weight)
    unfold sourcePreparedPhotonAmplitude actualPreparationLeg at result ⊢
    exact result
  have first:=whole_pair_from_vertex branch epsilon s n event.momentum (-transfer) nonzero
    event.frame event.cut event.energy event.energy u u
  have second:=whole_pair_from_vertex branch epsilon s n event.momentum (-transfer) nonzero
    event.frame event.cut event.energy event.energy b b
  have both:=congrArg₂ Sub.sub first second
  apply Eq.trans _ (both.trans (congrArg (fun q : ℂ=>q-pair b b) excited))
  unfold dressedCurrent sourceDressedConnectedCurrent sourceDressedCurrent
  simp only [mul_sub,Finset.sum_sub_distrib]
  rfl

end LowEnergy.GaussComposite.ActualSourceEMEventFeed
