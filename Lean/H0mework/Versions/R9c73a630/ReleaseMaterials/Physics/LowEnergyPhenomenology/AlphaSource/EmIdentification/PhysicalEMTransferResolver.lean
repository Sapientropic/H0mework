import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMCompleteStaticCharge

/-! The actual transfer resolvent producer: the original
`CanonicalPhysicalSpatial.compression` is affine in the physical momentum
through the original graded-compression linearization, so the local
`emSourceVelocity` is generated as its derivative and the original
full-Y57 inverse carries the `+R*V*R` first return. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMTransferResolver
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussQuantumMultiplier
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussFockLabel
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge CanonicalGradedSpatialSource
open NativeHistoryGrade
open GaussGradedCompression GaussUnitaryHistory PreparationVacuumPhysicalHalfAxis
open PreparationVacuumRestModeCoupling PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open SourceQuantumConfigurationHilbert PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullFieldRiesz
open FullYSourceCutoffVolterra (cutoff)
open GaussUnitaryHistory (Index)
open GaussComposite GaussComposite.SourceGraph
open MeasureTheory Filter Set
open scoped BigOperators Topology Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℚ ℂ _

set_option maxHeartbeats 10000 in
set_option maxRecDepth 128 in
private theorem sharedCompression_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D : Submodule ℂ E) (A B : D→ₗ[ℂ] E) (F : Finset D) (x : E) :
    FiniteCoreEvolution.compression ({domain:=D,toFun:=A}:E→ₗ.[ℂ] E) F x=
      ((FiniteCoreEvolution.coreSpan ({domain:=D,toFun:=B}:E→ₗ.[ℂ] E) F).orthogonalProjectionOnto
        (A ⟨((FiniteCoreEvolution.coreSpan ({domain:=D,toFun:=B}:E→ₗ.[ℂ] E) F).orthogonalProjectionOnto x:E),
          FiniteCoreEvolution.coreSpan_le ({domain:=D,toFun:=B}:E→ₗ.[ℂ] E) F ((FiniteCoreEvolution.coreSpan ({domain:=D,toFun:=B}:E→ₗ.[ℂ] E) F).orthogonalProjectionOnto x).property⟩):E):=by
  rfl

private def fixedCompressionLinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D : Submodule ℂ E) (F : Finset D) : (D→ₗ[ℂ] E)→ₗ[ℂ] (E→L[ℂ] E) where
  toFun := fun A=>FiniteCoreEvolution.compression ({domain:=D,toFun:=A}:E→ₗ.[ℂ] E) F
  map_add' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    rw [add_apply,sharedCompression_apply D (A+B) 0 F x,sharedCompression_apply D A 0 F x,sharedCompression_apply D B 0 F x]
    simp only [LinearMap.add_apply,map_add,Submodule.coe_add]
  map_smul' := by
    intro c A
    apply ContinuousLinearMap.ext
    intro x
    rw [smul_apply,sharedCompression_apply D (c • A) 0 F x,sharedCompression_apply D A 0 F x]
    simp only [LinearMap.smul_apply,map_smul,Submodule.coe_smul,RingHom.id_apply]

private def realizedCoreLinear : (QuantumTest→ₗ[ℂ] QuantumTest)→ₗ[ℂ] (Core→ₗ[ℂ] H) where
  toFun := fun A=>GaussCoreHilbert.embed.comp (A.comp GaussCoreHilbert.coreEquiv.symm.toLinearMap)
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply,LinearMap.add_apply,map_add]
  map_smul' := by
    intro c A
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,map_smul,RingHom.id_apply]

private def coreCompressionLinear (F : GaussUnitaryHistory.Index) : (QuantumTest→ₗ[ℂ] QuantumTest)→ₗ[ℂ] (H→L[ℂ] H):=
  (fixedCompressionLinear Core F).comp realizedCoreLinear

private def gradedCompressionLinear (F : GaussUnitaryHistory.Index) : (QuantumTest→ₗ[ℂ] QuantumTest)→ₗ[ℂ] (H→L[ℂ] H) where
  toFun := fun A=>∑g : Label,projection g*coreCompressionLinear F A*projection g
  map_add' := by intro A B;simp only [map_add,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' := by intro c A;simp only [map_smul,mul_smul_comm,smul_mul_assoc,Finset.smul_sum,RingHom.id_apply]

/-- The original `CanonicalPhysicalSpatial.momentumAction` is real-linear in
the physical momentum through the paid `momentumMatrix` algebra. -/
def emSourceMomentumLinear : PhysicalMomentum→ₗ[ℝ] (QuantumTest→ₗ[ℂ] QuantumTest) where
  toFun := CanonicalPhysicalSpatial.momentumAction
  map_add' := by
    intro p k
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change quantizer (momentumMatrix z (p+k)) (f z)=quantizer (momentumMatrix z p) (f z)+quantizer (momentumMatrix z k) (f z)
    rw [momentumMatrix_add,map_add,add_apply]
  map_smul' := by
    intro r p
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change quantizer (momentumMatrix z (r • p)) (f z)=r • (quantizer (momentumMatrix z p) (f z))
    rw [momentumMatrix_smul,map_smul,smul_apply]
    rfl

def emSourceVelocityLinear (F : GaussUnitaryHistory.Index) : PhysicalMomentum→ₗ[ℝ] (H→L[ℂ] H):=
  (gradedCompressionLinear F).restrictScalars ℝ |>.comp emSourceMomentumLinear

/-- The original `actualC` (= `CanonicalPhysicalSpatial.compression`) is
affine in the momentum; `emSourceVelocity` is its generated linear part,
not a presumed source profile. -/
theorem em_actualC_affine (F : GaussUnitaryHistory.Index) (p : PhysicalMomentum) :
    actualC p F=actualC 0 F+emSourceVelocityLinear F p:=by
  have origin : actualC 0 F=gradedCompressionLinear F diagonalAction:=
    (show actualC 0 F=gradedCompressionLinear F (CanonicalPhysicalSpatial.physicalAction 0) from rfl).trans
      (congrArg (gradedCompressionLinear F) CanonicalPhysicalSpatial.physicalAction_zero)
  calc
    _=gradedCompressionLinear F (diagonalAction+CanonicalPhysicalSpatial.momentumAction p):=rfl
    _=gradedCompressionLinear F diagonalAction+gradedCompressionLinear F (CanonicalPhysicalSpatial.momentumAction p):=
      map_add (gradedCompressionLinear F) _ _
    _= _:=congrArg₂ HAdd.hAdd origin.symm rfl

def emSourceVelocity (F : GaussUnitaryHistory.Index) : PhysicalMomentum→L[ℝ] (H→L[ℂ] H):=
  (emSourceVelocityLinear F).toContinuousLinearMap

theorem em_actualC_continuous (F : GaussUnitaryHistory.Index) : Continuous (fun p : PhysicalMomentum=>actualC p F):=by
  rw [show (fun p : PhysicalMomentum=>actualC p F)=(fun p=>actualC 0 F+emSourceVelocityLinear F p) from funext (em_actualC_affine F)]
  exact continuous_const.add (emSourceVelocity F).continuous

theorem em_actualC_difference_price (F : GaussUnitaryHistory.Index) (p k : PhysicalMomentum) :
    ‖actualC p F-actualC k F‖ ≤ ‖emSourceVelocity F‖*‖p-k‖:=by
  rw [em_actualC_affine F p,em_actualC_affine F k]
  have difference : actualC 0 F+emSourceVelocityLinear F p-(actualC 0 F+emSourceVelocityLinear F k)=emSourceVelocity F (p-k):=by
    simp only [map_sub,emSourceVelocity]
    abel
  rw [difference]
  exact (emSourceVelocity F).le_opNorm (p-k)

/-- The original finite resolvent is continuous in the physical momentum
through the generated affine structure and `NormedRing.inverse_continuousAt`. -/
theorem em_resolvent_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    Continuous (fun p : PhysicalMomentum=>CanonicalPhysicalResolvent.finiteResolvent p F z):=by
  change Continuous (fun p : PhysicalMomentum=>Ring.inverse (actualC p F-z • 1))
  apply continuous_iff_continuousAt.mpr
  intro p
  have unit:=FullYSourceResolventGraphSplice.resolvent_isUnit (actualC p F) (actualC_symmetric p F) z nonreal
  have inverse : ContinuousAt Ring.inverse (actualC p F-z • 1):=by
    rcases unit with ⟨u,hu⟩
    rw [←hu]
    exact NormedRing.inverse_continuousAt u
  have inner : ContinuousAt (fun k : PhysicalMomentum=>actualC k F-z • 1) p:=
    (em_actualC_continuous F).continuousAt.sub continuousAt_const
  exact inverse.tendsto.comp inner.tendsto

/-- The actual external vertex momentum: `sourcePhysicalTransfer` reads
`right-left`, so a positive physical `r•n` transfer carries `k=-(r•n)`. -/
def emTransferMomentum (n : PhysicalMomentum) (r : ℝ) : PhysicalMomentum := -(r • n)

/-- The original 57-term full-Y finite resolvent is continuous in the
physical momentum through the original series and `finiteResolvent`. -/
theorem em_finiteFull_momentum_continuous (F : GaussUnitaryHistory.Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    Continuous (fun p : PhysicalMomentum => CanonicalPhysicalYResolvent.finiteFull p F cut z) := by
  have resolvent := em_resolvent_continuous F z hz
  have step_continuous : Continuous (fun p : PhysicalMomentum =>
      CanonicalPhysicalYResolvent.step p F cut z) := by
    unfold CanonicalPhysicalYResolvent.step
    exact (resolvent.mul continuous_const).neg
  have series_continuous : Continuous (fun p : PhysicalMomentum =>
      CanonicalPhysicalYResolvent.series p F cut z) := by
    apply continuous_finsetSum
    intro n _
    exact step_continuous.pow n
  unfold CanonicalPhysicalYResolvent.finiteFull
  exact series_continuous.mul resolvent

/-- Generic affine derivative on an abstract real normed space; the concrete
Hilbert operator family is only instantiated through it, so elaboration never
unfolds the Fock model. -/
private theorem affine_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a v : E) :
    HasDerivAt (fun r : ℝ => a + r • v) v 0 := by
  have base : HasDerivAt (fun r : ℝ => r • v) v 0 := by
    simpa only [one_smul] using (hasDerivAt_id' (0:ℝ)).smul_const v
  exact base.const_add a

/-- Generic inverse-of-affine-family derivative on an abstract normed real
algebra: the unit `u` and velocity `V` stay opaque. -/
private theorem inverse_affine_hasDerivAt {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [HasSummableGeomSeries R] (u : Rˣ) (V : R) :
    HasDerivAt (fun r : ℝ => Ring.inverse ((u : R) - r • V)) (u.inv * V * u.inv) 0 := by
  have inverse := hasFDerivAt_ringInverse (𝕜:=ℝ) u
  have family : HasDerivAt (fun r : ℝ => (u : R) + r • (-V)) (-V) 0 :=
    affine_hasDerivAt (u : R) (-V)
  have same : (u : R) = (u : R) + (0:ℝ) • (-V) := by
    simp only [zero_smul, add_zero]
  have generated := inverse.comp_hasDerivAt_of_eq 0 family same
  refine (generated.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun r => congrArg Ring.inverse (by
      rw [sub_eq_add_neg, ← smul_neg])
  · simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      mul_neg, neg_mul, neg_neg]
    rfl

private theorem em_transfer_family_first (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) :
    HasDerivAt (fun r => actualC (p + emTransferMomentum n r) F + cutoff cut - z • 1)
      (-(emSourceVelocity F n)) 0 := by
  have velocity : emSourceVelocityLinear F n = emSourceVelocity F n := rfl
  have pointwise : ∀ r : ℝ, actualC (p + emTransferMomentum n r) F + cutoff cut - z • 1 =
      (actualC p F + cutoff cut - z • 1) + r • (-(emSourceVelocity F n)) := by
    intro r
    have affine := em_actualC_affine F (p + emTransferMomentum n r)
    have affine0 := em_actualC_affine F p
    rw [affine, affine0]
    simp only [emTransferMomentum, map_add, map_neg, map_smul, smul_neg, velocity]
    abel
  exact HasDerivAt.congr_of_eventuallyEq
    (affine_hasDerivAt (actualC p F + cutoff cut - z • 1) (-(emSourceVelocity F n)))
    (Filter.Eventually.of_forall pointwise)

/-- The original full resolvent carries the actual physical-transfer first
return: the family pays `-emSourceVelocity F n` and the inverse returns
`+(R*V*R)` with `R=finiteFull p F cut z`. -/
theorem em_finiteFull_transfer_first (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    HasDerivAt (fun r => CanonicalPhysicalYResolvent.finiteFull (p + emTransferMomentum n r) F cut z)
      (CanonicalPhysicalYResolvent.finiteFull p F cut z*emSourceVelocity F n*
        CanonicalPhysicalYResolvent.finiteFull p F cut z) 0 := by
  have pointwise : ∀ r : ℝ, Ring.inverse (actualC (p + emTransferMomentum n r) F +
      cutoff cut - z • 1) =
      CanonicalPhysicalYResolvent.finiteFull (p + emTransferMomentum n r) F cut z := fun r =>
    Ring.inverse_unit (originalFullUnit (p + emTransferMomentum n r) F cut z hz)
  have family : ∀ r : ℝ,
      actualC (p + emTransferMomentum n r) F + cutoff cut - z • 1 =
      (((originalFullUnit p F cut z hz : (H →L[ℂ] H)ˣ)) : H →L[ℂ] H) - r • emSourceVelocity F n := by
    intro r
    have affine := em_actualC_affine F (p + emTransferMomentum n r)
    have affine0 := em_actualC_affine F p
    have velocity : emSourceVelocityLinear F n = emSourceVelocity F n := rfl
    have uval : (((originalFullUnit p F cut z hz : (H →L[ℂ] H)ˣ)) : H →L[ℂ] H) =
        actualC p F + cutoff cut - z • 1 := rfl
    rw [uval, affine, affine0]
    simp only [emTransferMomentum, map_add, map_neg, map_smul, velocity]
    abel
  have core := inverse_affine_hasDerivAt (originalFullUnit p F cut z hz) (emSourceVelocity F n)
  have transport : (fun r => CanonicalPhysicalYResolvent.finiteFull
      (p + emTransferMomentum n r) F cut z) =ᶠ[𝓝 0]
      (fun r : ℝ => Ring.inverse
        ((((originalFullUnit p F cut z hz : (H →L[ℂ] H)ˣ)) : H →L[ℂ] H) - r • emSourceVelocity F n)) := by
    exact Filter.Eventually.of_forall fun r =>
      (pointwise r).symm.trans (congrArg Ring.inverse (family r))
  have result := core.congr_of_eventuallyEq transport
  simpa only [originalFullUnit] using result

end LowEnergy.GaussComposite.PhysicalEMTransferResolver
