import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVelocity

/-! Native charge of the original prepared fiber, then of its actual field
insertions. The source preparation is unchanged; no configuration profile
or propagation-level charge symmetry is supplied by these identities. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open SaturationMonoid.PhysicsCore
open DiracExteriorMatterAction SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra StageNineHolonomicField
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussQuantumMultiplier GaussCoreHilbert GaussCoreDifferential
open CanonicalGradedCharge CanonicalCompletedSector
open scoped Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder

theorem source_doublet_charge (state : Fin 2) :
    exteriorSpinorMotherLieAction (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection)
      (sourceColorDoubletMatter state)=Complex.I • sourceColorDoubletMatter state := by
  change (exteriorMotherLieAction 6 _ 0,
    exteriorMotherLieAction 2 _ (su7ExteriorBasis 2 (sourceColorDoubletIndex state)),
    exteriorMotherLieAction 4 _ 0) = _
  rw [map_zero,map_zero,Stage10.HyperchargeResponse.exterior_charge_basis]
  have h : exteriorHyperchargeWeight (sourceColorDoubletIndex state)=1 := by
    fin_cases state <;> decide
  simp only [h,Int.cast_one,one_mul,sourceColorDoubletMatter,Prod.smul_mk,smul_zero]

theorem source_embedding_charge (values : Source.Index → ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection)
      (Stage9DEF.Compatibility.embed values)=Complex.I • Stage9DEF.Compatibility.embed values := by
  funext spin
  change exteriorSpinorMotherLieAction _ (∑ state : Fin 2, values (spin,state) • sourceColorDoubletMatter state) =
    Complex.I • (∑ state : Fin 2, values (spin,state) • sourceColorDoubletMatter state)
  rw [map_sum]
  simp only [map_smul,source_doublet_charge,Finset.smul_sum,smul_comm Complex.I]

theorem original_preparation_charge :
    diracExteriorMotherLieAction (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection)
      (Stage10.ChargedPreparation.CanonicalParticle.normalizedPreparation 0
        (Stage9DEF.Compatibility.embed (Source.vector 0))) =
    Complex.I • (Stage10.ChargedPreparation.CanonicalParticle.normalizedPreparation 0
      (Stage9DEF.Compatibility.embed (Source.vector 0))) := by
  rw [Stage10.ChargedPreparation.CanonicalParticle.normalized_source]
  exact source_embedding_charge _

theorem original_seed_coordinates_charge : chargeMatrix nativeY*ᵥseedCoordinates = -seedCoordinates := by
  let v := Stage10.ChargedPreparation.CanonicalParticle.normalizedPreparation 0
    (Stage9DEF.Compatibility.embed (Source.vector 0))
  let u := LowEnergy.Quantum.coordinates v
  have primal : GaussNativeMatter.nativePrimal nativeY*ᵥu=Complex.I • u := by
    have h := congrArg LowEnergy.Quantum.coordinates original_preparation_charge
    rw [←LowEnergy.Quantum.matrix_action,map_smul] at h
    change LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction
      (p286LieBlockEmbed (p286CoordinateEquiv.symm nativeY))) *ᵥ u = _
    simpa only [nativeY,p286CoordinateEquiv.symm_apply_apply] using h
  change (Complex.I • Matrix.fromBlocks (GaussNativeMatter.nativePrimal nativeY) 0 0
    ((GaussNativeMatter.nativePrimal nativeY).map (starRingEnd ℂ))) *ᵥ Sum.elim u (fun _ => 0) = _
  rw [Matrix.smul_mulVec,Matrix.fromBlocks_mulVec]
  have left : (Sum.elim u (fun _ : LowEnergy.Quantum.Index => (0 : ℂ))) ∘ Sum.inl = u := rfl
  have right : (Sum.elim u (fun _ : LowEnergy.Quantum.Index => (0 : ℂ))) ∘ Sum.inr = 0 := rfl
  rw [left,right,Matrix.zero_mulVec,Matrix.zero_mulVec,Matrix.mulVec_zero,add_zero,zero_add,primal]
  funext i
  cases i with
  | inl i =>
    change Complex.I*(Complex.I*u i)=-(u i)
    rw [←mul_assoc,Complex.I_mul_I,neg_one_mul]
  | inr i => simp [seedCoordinates]

theorem original_seed_charge : quantized (chargeMatrix nativeY) CanonicalCompletedSector.seed = -CanonicalCompletedSector.seed := by
  change quantized (chargeMatrix nativeY) (oneParticleFiber seedCoordinates) = -oneParticleFiber seedCoordinates
  rw [quantized_oneParticle,original_seed_coordinates_charge]
  change fiberCoordinates.symm (LowEnergy.Fermion.oneParticleLinear (-seedCoordinates)) = _
  rw [map_neg,map_neg]
  rfl

theorem source_section_charge (f : QuantumTest) (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) : chargeAction nativeY f = -f := by
  apply DFunLike.ext
  intro z
  change quantized (chargeMatrix nativeY) (f z)=-(f z)
  rw [sameSource,map_smul,original_seed_charge,smul_neg]

theorem created_core_charge (channel spin : Fin 2) (f : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ) (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    chargeAction nativeY (creationTest channel spin f)=(-2 : ℂ) • creationTest channel spin f := by
  have h := creation_charge_core channel spin f
  change chargeAction nativeY (creationTest channel spin f)-creationTest channel spin (chargeAction nativeY f)=
    -creationTest channel spin f at h
  rw [source_section_charge f profile sameSource,map_neg] at h
  calc
    _ = -creationTest channel spin f + -creationTest channel spin f := sub_eq_iff_eq_add.mp h
    _ = _ := by module

end LowEnergy.GaussComposite
