import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTransferResolver

/-! The actual `epsilon^2` physical transfer through the original prepared
current: the negative scaled vertex momentum makes `sourcePhysicalTransfer`
of `(p+m,p)` equal `r•n`, lands `p+m` on the original sheet left momentum,
and the original full-Y `+R*V*R` first return is consumed from
`PhysicalEMTransferResolver`. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMTransferCurrent
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumFullOriginResponse
open PreparationPhysicalStaticSpatialCouplingReturn
open PreparationPhysicalDressedPhotonCouplingReturn PreparationPhysicalJointEMCouplingUnitReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalPhaseGaugeRealization
open CanonicalGradedCharge
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open PreparationVacuumMixedFieldReturn
open CanonicalGradedSpatialSource
open GaussQuantumMultiplier
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussFockLabel
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open NativeHistoryGrade
open GaussGradedCompression PreparationVacuumPhysicalHalfAxis
open PreparationVacuumRestModeCoupling PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalFeedback PreparationVacuumMovingPoleGaussReturn
open GaussComposite.PhysicalEMTransferResolver
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped BigOperators Topology Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℚ ℂ _

attribute [local irreducible] currentVertex CanonicalPhysicalYResolvent.finiteFull
  completedLeg sourceProfile chargeReader sourceJointInputCompleted

private theorem triple_first {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (L : ℝ→A) (D J R : A) (first : HasDerivAt L D 0) :
    HasDerivAt (fun scale : ℝ=>L scale*J*R) (D*J*R) 0 := by
  have product := (first.mul (hasDerivAt_const (0:ℝ) J)).mul
    (hasDerivAt_const (0:ℝ) R)
  have normalized : HasDerivAt ((L*fun _=>J)*fun _=>R) (D*J*R) 0 :=
    product.congr_deriv (by simp only [mul_zero,add_zero])
  exact normalized.congr_of_eventuallyEq (Filter.Eventually.of_forall fun scale=>rfl)

private theorem pair_continuous {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : X→E→L[ℂ]E) (continuous : Continuous T) (x y : E) :
    Continuous (fun input=>inner ℂ x (T input y)) :=
  continuous_const.inner (continuous.clm_apply continuous_const)

theorem emTransferMomentum_sub (p n : PhysicalMomentum) (r : ℝ) :
    p + emTransferMomentum n r = p - r • n := by
  unfold emTransferMomentum
  abel

/-- The physical transfer at the actual vertex endpoints is `r•n`. -/
theorem em_transfer_physical_transfer (p n : PhysicalMomentum) (r : ℝ) :
    sourcePhysicalTransfer (p + emTransferMomentum n r) p = r • n := by
  unfold sourcePhysicalTransfer
  rw [emTransferMomentum_sub]
  abel

/-- The `epsilon^2` transfer lands the vertex left momentum on the original
native sheet. -/
theorem em_transfer_sheet_left (p n : PhysicalMomentum) (epsilon : ℝ) :
    p + emTransferMomentum n (epsilon^2) = sheetLeft epsilon n p := by
  unfold sheetLeft
  exact emTransferMomentum_sub p n (epsilon^2)

/-- The actual momentum on these endpoints with the original sheet lambda is
the original `frequencyRay`, generated from `sheetMomentum_actual`. -/
theorem em_transfer_frequency_ray (epsilon s : ℝ) (n p : PhysicalMomentum) :
    actualMomentum (p + emTransferMomentum n (epsilon^2)) p (sheetLambda epsilon s) =
      frequencyRay epsilon s n := by
  rw [em_transfer_sheet_left]
  exact sheetMomentum_actual epsilon s n p

/-- The actual physical transfer applied at each spatial component is the
original `r * n i` scaling. -/
theorem em_transfer_physical_transfer_apply (p n : PhysicalMomentum) (r : ℝ) (i : Fin 3) :
    (sourcePhysicalTransfer (p + emTransferMomentum n r) p) i = r * n i := by
  rw [em_transfer_physical_transfer]
  rfl

/-- The static spatial Fourier symbol at `kappa=r` is `I` times the physical
transfer `r * n i`, retaining the zero temporal coordinate. -/
theorem em_transfer_static_momentum (n : PhysicalMomentum) (r : ℝ) :
    sourceStaticSpatialMomentum n r =
      ![0, Complex.I*(((r * n 0):ℝ):ℂ), Complex.I*(((r * n 1):ℝ):ℂ),
        Complex.I*(((r * n 2):ℝ):ℂ)] := by
  unfold sourceStaticSpatialMomentum
  rfl

/-- The original 57-term full-Y finite resolvent is continuous in the
physical momentum through the original series and `finiteResolvent`. -/
theorem finiteFull_transfer_continuous (F : GaussUnitaryHistory.Index) (cut : ℕ) (z : ℂ)
    (hz : z.im≠0) :
    Continuous (fun p : PhysicalMomentum => CanonicalPhysicalYResolvent.finiteFull p F cut z) :=
  em_finiteFull_momentum_continuous F cut z hz

/-- The actual vertex with positive physical transfer `r•n` has the original
`finiteFull` first return on its left resolvent; the right `w` leg is kept
arbitrary and constant. -/
theorem currentVertex_transfer_first (f : Field289) (p n : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) :
    HasDerivAt (fun r => currentVertex f p (emTransferMomentum n r) F cut z w)
      (CanonicalPhysicalYResolvent.finiteFull p F cut z*(emSourceVelocity F n)*
        currentVertex f p 0 F cut z w) 0 := by
  have L := em_finiteFull_transfer_first p n F cut z hz
  have produced := triple_first _
    (CanonicalPhysicalYResolvent.finiteFull p F cut z*emSourceVelocity F n*
      CanonicalPhysicalYResolvent.finiteFull p F cut z)
    (currentRestriction f p F 0) (CanonicalPhysicalYResolvent.finiteFull p F cut w) L
  have pointwise (scale : ℝ) :
      currentVertex f p (emTransferMomentum n scale) F cut z w=
      CanonicalPhysicalYResolvent.finiteFull (p+emTransferMomentum n scale) F cut z*
        currentRestriction f p F 0*CanonicalPhysicalYResolvent.finiteFull p F cut w := by
    unfold currentVertex
    rfl
  have result := produced.congr_of_eventuallyEq (Filter.Eventually.of_forall pointwise)
  exact result.congr_deriv (by simp only [currentVertex,add_zero,mul_assoc])

/-- The actual vertex is continuous in its external momentum at fixed
incoming `p`, `F`, `cut` and both Green parameters. -/
theorem currentVertex_transfer_continuous (f : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) :
    Continuous (fun k : PhysicalMomentum => currentVertex f p k F cut z w) := by
  have left : Continuous (fun k : PhysicalMomentum =>
      CanonicalPhysicalYResolvent.finiteFull (p + k) F cut z) :=
    (em_finiteFull_momentum_continuous F cut z hz).comp (continuous_const.add continuous_id)
  have produced : Continuous (fun k : PhysicalMomentum=>
      CanonicalPhysicalYResolvent.finiteFull (p+k) F cut z*
        currentRestriction f p F 0*CanonicalPhysicalYResolvent.finiteFull p F cut w) :=
    (left.mul continuous_const).mul continuous_const
  exact produced.congr (fun k=>by unfold currentVertex; rfl)

/-- The actual prepared covector is continuous in its external momentum at
fixed preparation. -/
theorem preparedCovector_transfer_continuous (eps : ℝ) (prec : 0<eps) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (l r : Bool) (a s b t : Fin 2)
    (hz : z.im≠0) :
    Continuous (fun k : PhysicalMomentum => preparedCovector eps prec p k F cut z w l r a s b t) := by
  apply continuous_pi
  intro i
  have vertex := currentVertex_transfer_continuous (fieldBasis i) p F cut z w hz
  have produced := pair_continuous _ vertex
    (completedLeg l a s (sourceProfile eps prec))
    (completedLeg r b t (sourceProfile eps prec))
  exact produced.congr (fun k=>rfl)

/-- The actual joint `Qa` inserted current is continuous in its external
momentum at fixed preparation; both original `chargeReader` legs and the
original `sourceJointInputCompleted` input legs are kept. -/
theorem sourceJointChargedCurrent_transfer_continuous (eps : ℝ) (prec : 0<eps)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ)
    (l r : Bool) (a s b t : Fin 2) (hz : z.im≠0) :
    Continuous (fun k : PhysicalMomentum =>
      sourceJointChargedCurrent eps prec p k F cut z w l r a s b t) := by
  apply continuous_pi
  intro i
  have vertex := currentVertex_transfer_continuous (fieldBasis i) p F cut z w hz
  have left := pair_continuous _ vertex
    (chargeReader sourcePhaseGaugeLie (completedLeg l a s (sourceProfile eps prec)))
    (completedLeg r b t (sourceProfile eps prec))
  have right := pair_continuous _ vertex
    (completedLeg l a s (sourceProfile eps prec))
    (chargeReader sourcePhaseGaugeLie (completedLeg r b t (sourceProfile eps prec)))
  exact (left.add right).congr (fun k=>rfl)

/-- The actual bounded input/scalar remainder current is continuous in its
external momentum at fixed preparation. -/
theorem sourceJointInputCurrent_transfer_continuous (eps : ℝ) (prec : 0<eps)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ)
    (l r : Bool) (a s b t : Fin 2) (hz : z.im≠0) :
    Continuous (fun k : PhysicalMomentum =>
      sourceJointInputCurrent eps prec p k F cut z w l r a s b t) := by
  apply continuous_pi
  intro i
  have vertex := currentVertex_transfer_continuous (fieldBasis i) p F cut z w hz
  have left := pair_continuous _ vertex
    (sourceJointInputCompleted l a s (sourceProfile eps prec))
    (completedLeg r b t (sourceProfile eps prec))
  have right := pair_continuous _ vertex
    (completedLeg l a s (sourceProfile eps prec))
    (sourceJointInputCompleted r b t (sourceProfile eps prec))
  exact (left.add right).congr (fun k=>rfl)

/-- The direct prepared-current first jet consumes the operator derivative:
`inner x ((R*V*currentVertex0) y)` is the `epsilon^2` physical-transfer
first return on the actual prepared current. -/
theorem em_transfer_prepared_first_jet (f : Field289) (p n : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (x y : H) :
    HasDerivAt (fun r => inner ℂ x
      ((currentVertex f p (emTransferMomentum n r) F cut z w) y))
      (inner ℂ x
        ((CanonicalPhysicalYResolvent.finiteFull p F cut z*(emSourceVelocity F n)*
          currentVertex f p 0 F cut z w) y)) 0 :=
  paired_derivative (currentVertex_transfer_first f p n F cut z w hz) x y

/-- The same jet read on the actual `preparedCurrent` with its original
completed legs and `sourceProfile` preparation. -/
theorem em_transfer_preparedCurrent_first_jet (eps : ℝ) (prec : 0<eps) (f : Field289)
    (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ)
    (l r : Bool) (a s b t : Fin 2) (hz : z.im≠0) :
    HasDerivAt (fun scale => PreparationVacuumFullFieldRiesz.preparedCurrent eps prec f p
      (emTransferMomentum n scale) F cut z w l r a s b t)
      (inner ℂ (completedLeg l a s (sourceProfile eps prec))
        ((CanonicalPhysicalYResolvent.finiteFull p F cut z*(emSourceVelocity F n)*
          currentVertex f p 0 F cut z w)
          (completedLeg r b t (sourceProfile eps prec)))) 0 := by
  unfold PreparationVacuumFullFieldRiesz.preparedCurrent
  exact paired_derivative (currentVertex_transfer_first f p n F cut z w hz) _ _

end LowEnergy.GaussComposite.PhysicalEMTransferCurrent
