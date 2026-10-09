import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedPhotonSample

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalDressedPhotonCouplingReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalDressedGTVertexReturn PreparationPhysicalDressedSpinChargeReturn
open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalFirstGaugeMaterialDifference
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNormalizedFullField
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumSourceActionJets PreparationVacuumSourceFieldFamily PreparationVacuumActionDecomposition
open PreparationVacuumFieldConstraintResponse PreparationVacuumFieldCovector PreparationVacuumMixedFieldReturn
open PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussFockPair
open CanonicalGradedSpatialSource CanonicalPhysicalYResolvent GaussComposite GaussComposite.SourceGraph
open MeasureTheory Filter Set
open GaussUnitaryHistory (Index)
open scoped BigOperators InnerProductSpace Topology Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

/-- Complexification uses precisely the already-generated real field jets. -/
def sourcePhotonConfigurationRead (p : PhysicalMomentum) (a b : QuantumTest) : (Fin 289→ℂ)→ₗ[ℂ]ℂ where
  toFun V:=∑i,V i*(fieldJets (fieldBasis i) p a b).first 0
  map_add' V W:=by simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c V:=by simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum,RingHom.id_apply]

private theorem real_read (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    sourcePhotonConfigurationRead p a b (fun i=>(f i:ℂ))=(fieldJets f p a b).first 0 :=
  (field_first_coordinates f p a b).symm

/-- This is the G+R integral of the actual first literal column, not a decomposition of the whole polarization into a gauge mode. -/
theorem sourcePhotonFirstColumn_generated (omega : ℝ) (k p : PhysicalMomentum) (a b : QuantumTest) :
    sourcePhotonConfigurationRead p a b (fun i=>sourceChargedNativeFrameJet (physicalFrequencyMomentum omega k) i 1)=
      sourcePhotonModeConfiguration false omega k p a b+Complex.I*sourcePhotonModeConfiguration true omega k p a b := by
  have field : (fun i=>sourceChargedNativeFrameJet (physicalFrequencyMomentum omega k) i 1)=
      (fun i=>(sourceFirstModeField false omega k 0 i:ℂ))+Complex.I •
        (fun i=>(sourceFirstModeField true omega k 0 i:ℂ)) := by
    funext i
    have paid:=sourceFirstModeField_complex omega k 0 i
    simpa only [sourceFirstHarmonicPhase,map_zero,Complex.exp_zero,one_mul,Pi.add_apply,
      Pi.smul_apply,smul_eq_mul] using paid.symm
  rw [field,map_add,map_smul,real_read,real_read,sourcePhotonModeConfiguration_generated,
    sourcePhotonModeConfiguration_generated]
  rfl

/-- Every original frame column survives, including both fast columns; only column one receives the computed integral return. -/
def sourcePhotonWholeConfiguration (branch : Fin 2) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (a b : QuantumTest) : ℂ :=
  sourcePhotonConfigurationRead p a b (sourcePoleOriginField branch epsilon s n)+
    (epsilon:ℂ)^2*(∑j : Fin 289,sourcePoleCoordinates branch epsilon s n j*
      (if j=1 then sourcePhotonModeConfiguration false s n p a b+
        Complex.I*sourcePhotonModeConfiguration true s n p a b
      else sourcePhotonConfigurationRead p a b (fun i=>sourceChargedNativeFrameJet (physicalFrequencyMomentum s n) i j)))+
  sourcePhotonConfigurationRead p a b (sourcePoleFrameResidual branch epsilon s n)

theorem sourcePhotonWholeConfiguration_generated (branch : Fin 2) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (nonzero : epsilon≠0) (a b : QuantumTest) :
    sourcePhotonConfigurationRead p a b (sourceNativeFrequencyPolarization branch epsilon s n)=
      sourcePhotonWholeConfiguration branch epsilon s n p a b := by
  have field:=sourceNativeFrequencyPolarization_firstReturn branch epsilon s n nonzero
  have read:=congrArg (sourcePhotonConfigurationRead p a b) field
  simp only [map_sub,map_smul,smul_eq_mul] at read
  have columns : sourcePhotonConfigurationRead p a b (sourcePoleJetField branch epsilon s n)=
      ∑j : Fin 289,sourcePoleCoordinates branch epsilon s n j*
        (if j=1 then sourcePhotonModeConfiguration false s n p a b+
          Complex.I*sourcePhotonModeConfiguration true s n p a b
        else sourcePhotonConfigurationRead p a b (fun i=>sourceChargedNativeFrameJet (physicalFrequencyMomentum s n) i j)) := by
    change (∑i,(∑j,sourceChargedNativeFrameJet (physicalFrequencyMomentum s n) i j*
      sourcePoleCoordinates branch epsilon s n j)*(fieldJets (fieldBasis i) p a b).first 0)=_
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have entry : (∑i,sourceChargedNativeFrameJet (physicalFrequencyMomentum s n) i j*
        sourcePoleCoordinates branch epsilon s n j*(fieldJets (fieldBasis i) p a b).first 0)=
        sourcePoleCoordinates branch epsilon s n j*
          sourcePhotonConfigurationRead p a b (fun i=>sourceChargedNativeFrameJet (physicalFrequencyMomentum s n) i j) := by
      simp only [sourcePhotonConfigurationRead,LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [entry]
    by_cases h : j=1
    · subst j
      rw [if_pos rfl,sourcePhotonFirstColumn_generated]
    · rw [if_neg h]
  unfold sourcePhotonWholeConfiguration
  rw [columns] at read
  linear_combination read

/-- Original two inverses and the original source-test frames feed the calculated whole configuration integral. -/
def sourcePhotonWholePair (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (x y : H) : ℂ :=
  sourcePhotonWholeConfiguration branch epsilon s n p
    (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
    (sourceTestApprox F (finiteFull p F cut w y))

private theorem vertex_read (V : Fin 289→ℂ) (p k : PhysicalMomentum) (F : Index)
    (cut : ℕ) (z w : ℂ) (x y : H) :
    (∑i,V i*inner ℂ x (currentVertex (fieldBasis i) p k F cut z w y))=
      sourcePhotonConfigurationRead p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
        (sourceTestApprox F (finiteFull p F cut w y)) V := by
  change _=∑i,V i*(fieldJets (fieldBasis i) p _ _).first 0
  apply Finset.sum_congr rfl
  intro i _
  rw [currentVertex_original_pair]

/-- The generated integral retains the original two independent leg norms and full finite-reader prices. -/
theorem sourcePhotonWholePair_price (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (nonzero : epsilon≠0) (F : Index) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (x y : H) :
    ‖sourcePhotonWholePair branch epsilon s n p k F cut z w x y‖≤
      ∑i,‖sourceNativeFrequencyPolarization branch epsilon s n i‖*
        (‖x‖*(normBound cut z*currentPrice (fieldBasis i) p F*normBound cut w)*‖y‖) := by
  unfold sourcePhotonWholePair
  rw [←sourcePhotonWholeConfiguration_generated branch epsilon s n p nonzero,←vertex_read]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (vertex_pair_price _ _ (currentVertex_price (fieldBasis i) p k F cut z w hz hw) x y) (norm_nonneg _)

/-- Both terms are original G+R integrals with the actual GT acting on the respective external input. -/
def sourcePhotonWholeTorque (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (x y : H) : ℂ :=
  sourcePhotonWholePair branch epsilon s n p k F cut z w x (sourceFirstCharge y)-
    sourcePhotonWholePair branch epsilon s n p k F cut z w (sourceFirstCharge x) y

theorem sourcePhotonWholeTorque_generated (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (nonzero : epsilon≠0) (F : Index) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (x y : H) :
    (∑i,sourceNativeFrequencyPolarization branch epsilon s n i*
      sourceGTVertexRead (fieldBasis i) p k F cut z w x y)=
      sourcePhotonWholeTorque branch epsilon s n p k F cut z w x y := by
  simp only [←sourceGTVertexRead_generated _ _ _ _ _ _ _ hz hw,
    sub_apply,mul_apply_eq_comp,inner_sub_right,
    ←sourceFirstCharge_pair,mul_sub,Finset.sum_sub_distrib]
  rw [vertex_read,vertex_read,sourcePhotonWholeConfiguration_generated branch epsilon s n p nonzero,
    sourcePhotonWholeConfiguration_generated branch epsilon s n p nonzero]
  rfl

attribute [local irreducible] sourceGTVertexRead currentVertex completedLeg sourceProfile finiteFull sourceFirstCharge

/-- The ordinary interaction consumes the calculated whole G+R integral, with independent composite source and detector data. -/
theorem sourceDressedPhotonInteraction_generated
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
        (completedLeg lD aD sD (sourceProfile epsD precD)) (completedLeg rD bD tD (sourceProfile epsD precD)) := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  have frequency (v : Fin 289→ℂ) : sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥv=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n v •
        sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
    rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor v,sourceNativeFrequencyPolarization,smul_comm]
  let U:=sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n
  let B:=sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
    (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)
  have one := vertex_read U pD kD FD cutD zD wD
    (completedLeg lD aD sD (sourceProfile epsD precD)) (completedLeg rD bD tD (sourceProfile epsD precD))
  rw [sourcePhotonWholeConfiguration_generated branch e.val (sourceSheet branch n unit e.val) n pD e.property.1.ne'] at one
  have read : (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*U i)=
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
        (completedLeg lD aD sD (sourceProfile epsD precD)) (completedLeg rD bD tD (sourceProfile epsD precD)) := by
    calc
      _=∑i,U i*inner ℂ (completedLeg lD aD sD (sourceProfile epsD precD))
          (currentVertex (fieldBasis i) pD kD FD cutD zD wD (completedLeg rD bD tD (sourceProfile epsD precD))) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [preparedCovector,preparedCurrent]
        exact mul_comm _ _
      _=_ := one
  rw [frequency]
  change (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*(B*U i))/_=B/_*_
  have scaled : (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*(B*U i))=
      B*(∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*U i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [scaled,read]
  ring

/-- Emission and detection data are independent original composite preparations. -/
theorem sourceDressedPhotonCoupling_generated
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (hzD : zD.im≠0) (hwD : wD.im≠0) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      (∑i,sourceDressedCompleteGTRead epsD precD (fieldBasis i) pD kD FD cutD zD wD lD rD aD sD bD tD*
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
      ((star (sourceDressedCharacter lD)+sourceDressedCharacter rD)*
        sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
          (completedLeg lD aD sD (sourceProfile epsD precD)) (completedLeg rD bD tD (sourceProfile epsD precD))-
        Complex.I*sourcePhotonWholeTorque branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
          (completedLeg lD aD sD (sourceProfile epsD precD)) (completedLeg rD bD tD (sourceProfile epsD precD))) := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  have frequency (v : Fin 289→ℂ) : sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥv=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n v •
        sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
    rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor v,sourceNativeFrequencyPolarization,smul_comm]
  let U:=sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n
  let B:=sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
    (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)
  let x:=completedLeg lD aD sD (sourceProfile epsD precD)
  let y:=completedLeg rD bD tD (sourceProfile epsD precD)
  let chi:=star (sourceDressedCharacter lD)+sourceDressedCharacter rD
  have one := vertex_read U pD kD FD cutD zD wD x y
  rw [sourcePhotonWholeConfiguration_generated branch e.val (sourceSheet branch n unit e.val) n pD e.property.1.ne'] at one
  have two := sourcePhotonWholeTorque_generated branch e.val (sourceSheet branch n unit e.val) n pD kD
    e.property.1.ne' FD cutD zD wD hzD hwD x y
  have calculated : (∑i,sourceDressedCompleteGTRead epsD precD (fieldBasis i)
      pD kD FD cutD zD wD lD rD aD sD bD tD*U i)=
      chi*sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD x y-
        Complex.I*sourcePhotonWholeTorque branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD x y := by
    calc
      _=chi*(∑i,U i*inner ℂ x (currentVertex (fieldBasis i) pD kD FD cutD zD wD y))-
          Complex.I*(∑i,U i*sourceGTVertexRead (fieldBasis i) pD kD FD cutD zD wD x y) := by
        rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [sourceDressedCompleteGTRead,preparedCurrent]
        change (chi*inner ℂ x (currentVertex (fieldBasis i) pD kD FD cutD zD wD y)-
          Complex.I*sourceGTVertexRead (fieldBasis i) pD kD FD cutD zD wD x y)*U i=_
        ring
      _=_ := by rw [one,two];rfl
  rw [frequency]
  change (∑i,sourceDressedCompleteGTRead epsD precD (fieldBasis i)
      pD kD FD cutD zD wD lD rD aD sD bD tD*(B*U i))/_=B/_*_
  have scaled : (∑i,sourceDressedCompleteGTRead epsD precD (fieldBasis i)
      pD kD FD cutD zD wD lD rD aD sD bD tD*(B*U i))=
      B*(∑i,sourceDressedCompleteGTRead epsD precD (fieldBasis i)
        pD kD FD cutD zD wD lD rD aD sD bD tD*U i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [scaled,calculated]
  ring

end LowEnergy.PreparationPhysicalDressedPhotonCouplingReturn
