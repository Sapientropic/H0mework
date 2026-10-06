import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPhysicalSpatial
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalGradedFullForce
import H0mework.Physics.LowEnergy.Quantum.JointCurrentHeisenberg

/-! Original scalar/gauge covariant momenta have no coframe component. The
unlocalized physical principal consequently commutes with those directions,
including the actual connection, before any completed response is formed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalForce
open SaturationMonoid.PhysicsCore
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart GaussQuantumMultiplier
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open scoped Topology InnerProductSpace ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

theorem momentum_native (z : SourceCoordinateSlice) (p : PhysicalMomentum) (a : NativeLie) :
    momentumMatrix z p*GaussNativeMatter.nativeFull a=GaussNativeMatter.nativeFull a*momentumMatrix z p := by
  simp only [momentumMatrix, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, GaussMatterCore.boost_native_commute]

theorem quantized_commute (A B : Matrix Mode Mode ℂ) (commutes : A*B=B*A) :
    Commute (quantized A) (quantized B) := by
  have original := SourceJointCurrentHeisenberg.quantize_commutator A B
  rw [commutes, sub_self] at original
  have zero : LowEnergy.Fermion.quantize (0 : Matrix Mode Mode ℂ)=0 := by
    apply LinearMap.ext
    intro f
    simp [LowEnergy.Fermion.quantize]
  rw [zero, sub_eq_zero] at original
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  change LowEnergy.Fermion.quantize A (LowEnergy.Fermion.quantize B (fiberCoordinates f)) =
    LowEnergy.Fermion.quantize B (LowEnergy.Fermion.quantize A (fiberCoordinates f))
  exact LinearMap.congr_fun original (fiberCoordinates f)

theorem momentum_connection (p : PhysicalMomentum) (v : Ambient) (z : SourceCoordinateSlice) :
    Commute (CanonicalGradedSpatial.sourceMomentum p z) (connection v z) :=
  quantized_commute _ _ (momentum_native z p (inverseL z v).1)

theorem sourceMomentum_native_line (p : PhysicalMomentum) (z : SourceCoordinateSlice)
    (v : Ambient) (r : ℝ) :
    CanonicalGradedSpatial.sourceMomentum p (z+r • direction v z)=
      CanonicalGradedSpatial.sourceMomentum p z := by
  have first : (z+r • direction v z).1=z.1 := by
    change z.1+r • (0 : SourceQuantumConfigurationHilbert.Coframe)=z.1
    rw [smul_zero, add_zero]
  simp only [CanonicalGradedSpatial.sourceMomentum, momentumMatrix, GaussMatterCore.coefficient, first]

theorem directional_commutes (p : PhysicalMomentum) (v : Ambient) :
    Commute (directional v) (momentumAction p) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let d := direction v z
  have path : HasDerivAt (fun r : ℝ => z+r • d) d 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
  have initial := ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0 path
  have output := (((momentumAction p f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0 path
  simp only [zero_smul, add_zero] at initial output
  let M := (CanonicalGradedSpatial.sourceMomentum p z).restrictScalars ℝ
  have mapped := M.hasFDerivAt.comp_hasDerivAt 0 initial
  simp only [Function.comp_def] at output mapped
  have constant : (fun r : ℝ => momentumAction p f (z+r • d)) =
      (fun r : ℝ => M (f (z+r • d))) := by
    funext r
    change CanonicalGradedSpatial.sourceMomentum p (z+r • direction v z) (f (z+r • d)) = _
    rw [sourceMomentum_native_line]
    rfl
  rw [constant] at output
  exact output.unique mapped

theorem connection_commutes (p : PhysicalMomentum) (v : Ambient) :
    Commute (localMultiplier (connection v) (connection_smooth v)) (momentumAction p) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z)) (momentum_connection p v z).symm.eq

theorem momentum_commutes (p : PhysicalMomentum) (v : Ambient) :
    Commute (covariantMomentum v) (momentumAction p) :=
  ((directional_commutes p v).add_left (connection_commutes p v)).smul_left (-Complex.I)

theorem adjoint_commutes (p : PhysicalMomentum) (v : Ambient) :
    Commute (GaussMomentumAdjoint.adjoint v) (momentumAction p) := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have generated : covariantMomentum v (momentumAction p f)=momentumAction p (covariantMomentum v f) :=
    LinearMap.congr_fun (momentum_commutes p v).eq f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (momentumAction p g)) =
    sourcePair f (momentumAction p (GaussMomentumAdjoint.adjoint v g))
  calc
    _ = sourcePair (covariantMomentum v f) (momentumAction p g) := GaussNativeForm.adjoint_pair v f _
    _ = sourcePair (momentumAction p (covariantMomentum v f)) g := momentumAction_pair p _ _
    _ = sourcePair (covariantMomentum v (momentumAction p f)) g := by rw [generated]
    _ = sourcePair (momentumAction p f) (GaussMomentumAdjoint.adjoint v g) := (GaussNativeForm.adjoint_pair v _ _).symm
    _ = _ := (momentumAction_pair p _ _).symm

theorem physical_force (p : PhysicalMomentum) (v : Ambient) :
    CanonicalGradedFullForce.actionForce (physicalAction p) (covariantMomentum v) =
      CanonicalGradedFullForce.force v := by
  have commute := (momentum_commutes p v).eq
  change covariantMomentum v*momentumAction p=momentumAction p*covariantMomentum v at commute
  change Complex.I • ((GaussDiagonalHistory.diagonalAction+momentumAction p)*covariantMomentum v-
    covariantMomentum v*(GaussDiagonalHistory.diagonalAction+momentumAction p)) =
      Complex.I • (GaussDiagonalHistory.diagonalAction*covariantMomentum v-
        covariantMomentum v*GaussDiagonalHistory.diagonalAction)
  rw [add_mul, mul_add, commute]
  congr 1
  abel

theorem physical_sharpForce (p : PhysicalMomentum) (v : Ambient) :
    CanonicalGradedFullForce.actionForce (physicalAction p) (GaussMomentumAdjoint.adjoint v) =
      CanonicalGradedFullForce.sharpForce v := by
  have commute := (adjoint_commutes p v).eq
  change GaussMomentumAdjoint.adjoint v*momentumAction p=momentumAction p*GaussMomentumAdjoint.adjoint v at commute
  change Complex.I • ((GaussDiagonalHistory.diagonalAction+momentumAction p)*GaussMomentumAdjoint.adjoint v-
    GaussMomentumAdjoint.adjoint v*(GaussDiagonalHistory.diagonalAction+momentumAction p)) =
      Complex.I • (GaussDiagonalHistory.diagonalAction*GaussMomentumAdjoint.adjoint v-
        GaussMomentumAdjoint.adjoint v*GaussDiagonalHistory.diagonalAction)
  rw [add_mul, mul_add, commute]
  congr 1
  abel

theorem physical_force_weak (p : PhysicalMomentum) (v : Ambient) (f g : QuantumTest) :
    sourcePair f (CanonicalGradedFullForce.force v g)=Complex.I*
      (sourcePair (physicalAction p f) (covariantMomentum v g)-
        sourcePair (GaussMomentumAdjoint.adjoint v f) (physicalAction p g)) := by
  rw [← physical_force p v]
  change inner ℂ (embed f) (embed (Complex.I •
    (physicalAction p (covariantMomentum v g)-covariantMomentum v (physicalAction p g)))) = _
  simp only [map_smul, map_sub, inner_smul_right, inner_sub_right]
  change Complex.I*(sourcePair f (physicalAction p (covariantMomentum v g))-
    sourcePair f (covariantMomentum v (physicalAction p g))) = _
  rw [physicalAction_pair p f (covariantMomentum v g), GaussMomentumAdjoint.momentum_pair v f (physicalAction p g)]

def shiftedTest (p : PhysicalMomentum) (z : ℂ) (f : QuantumTest) : QuantumTest := physicalAction p f-z • f

theorem physical_force_endpoints (p : PhysicalMomentum) (v : Ambient) (z w : ℂ) (f g : QuantumTest) :
    sourcePair f (CanonicalGradedFullForce.force v g)=Complex.I*
      (sourcePair (shiftedTest p (star z) f) (covariantMomentum v g)-
        sourcePair (GaussMomentumAdjoint.adjoint v f) (shiftedTest p w g)+
        (z-w)*sourcePair f (covariantMomentum v g)) := by
  rw [physical_force_weak]
  have pair := GaussMomentumAdjoint.momentum_pair v f g
  simp only [sourcePair, shiftedTest, map_sub, map_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_star] at pair ⊢
  rw [← pair]
  ring

end LowEnergy.CanonicalPhysicalForce
