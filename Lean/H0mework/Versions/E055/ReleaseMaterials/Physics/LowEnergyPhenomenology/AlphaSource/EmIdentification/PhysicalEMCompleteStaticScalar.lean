import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticCompositeProjection
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticSpatialCoupling

/-! The complete actual static scalar: the original full-space Green pole
coefficient of the composite source currents, read through both real source
origin projections and the actual paid static inverse on the live `{0,1}`
slice, divided by the source `h_source*c_source` unit. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalStaticSpatialCouplingReturn PreparationPhysicalStaticCompositeProjectionReturn
open PreparationPhysicalDressedSpinChargeReturn CanonicalGradedSpatialSource
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped BigOperators Topology Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

/-- The paid seed of the actual static inverse on the live `{0,1}` source
block: minus the sum of all four entries of the projected `staticInverse`. -/
def emStaticCompleteSeed : ℂ :=
  -(staticInverse 0 0+staticInverse 0 1+staticInverse 1 0+staticInverse 1 1)

/-- The actual paid static inverse on an equal-weight `{0,1}` slice vector,
copied from the actual `staticInverseTerms` normalization (no eigensystem). -/
private theorem emStaticInverse_weight (w : ℂ) :
    staticInverse*ᵥ(Pi.single 0 w+Pi.single 1 w)=
      Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*w)+
      Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*w):=by
  norm_num [staticInverse,staticInverseTerms,sourceMatrix,SourceTerm.matrix,Powers.value,coefficientValue,
    Matrix.add_mulVec,Matrix.zero_mulVec,Matrix.single_mulVec,Pi.add_apply,Pi.single_apply,Fin.ext_iff]
  congr 1

private theorem fin01 : ¬((0:Fin 289)=1):=by decide
private theorem fin10 : ¬((1:Fin 289)=0):=by decide

private theorem single_dot (k : Fin 289) (b : ℂ) (X : Fin 289→ℂ) :
    (∑j : Fin 289,(Pi.single k b : Fin 289→ℂ) j*X j)=b*X k:=by
  have main : (∑j : Fin 289,(Pi.single k b : Fin 289→ℂ) j*X j)=
      (Pi.single k b : Fin 289→ℂ) k*X k:=by
    apply Finset.sum_eq_single k
    · intro j _ ne
      rw [Pi.single_apply,if_neg ne,zero_mul]
    · intro absent
      exact absurd (Finset.mem_univ k) absent
  rw [main,Pi.single_apply,if_pos rfl]

private theorem single_contract (k : Fin 289) (b : ℂ) (X : Fin 289→ℂ) :
    (∑j : Fin 289,X j*(Pi.single k b : Fin 289→ℂ) j)=X k*b:=by
  have main : (∑j : Fin 289,X j*(Pi.single k b : Fin 289→ℂ) j)=
      X k*(Pi.single k b : Fin 289→ℂ) k:=by
    apply Finset.sum_eq_single k
    · intro j _ ne
      rw [Pi.single_apply,if_neg ne,mul_zero]
    · intro absent
      exact absurd (Finset.mem_univ k) absent
  rw [main,Pi.single_apply,if_pos rfl]

/-- The `{0,1}` block column sum of `staticInverse` is its action on the
equal-weight slice vector at rows `0` and `1`. -/
private theorem mulVec_single_pair (M : Matrix (Fin 289) (Fin 289) ℂ) (i : Fin 289) :
    (M*ᵥ((Pi.single 0 (1:ℂ)+Pi.single 1 (1:ℂ) : Fin 289→ℂ))) i=M i 0+M i 1:=by
  simp only [Matrix.mulVec,dotProduct,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  rw [single_contract 0 1 _,single_contract 1 1 _]
  ring

/-- The generated seed value: the paid terms `-9/125` and `-67/72` of the
actual static inverse sum to `9023/9000` times `rootTwo*rootFifteen`. -/
theorem em_static_seed_generated :
    emStaticCompleteSeed=(9023/9000:ℂ)*rootTwo*rootFifteen:=by
  have four : staticInverse 0 0+staticInverse 0 1+staticInverse 1 0+staticInverse 1 1=
      (staticInverse*ᵥ(Pi.single 0 (1:ℂ)+Pi.single 1 (1:ℂ))) 0+
      (staticInverse*ᵥ(Pi.single 0 (1:ℂ)+Pi.single 1 (1:ℂ))) 1:=by
    rw [mulVec_single_pair,mulVec_single_pair]
    ring
  rw [emStaticCompleteSeed,four,emStaticInverse_weight]
  simp only [Pi.add_apply,Pi.single_apply]
  rw [if_pos trivial,if_neg fin01,if_neg fin10,if_pos trivial]
  ring

/-- The generic complex bilinear transpose identity: `dot(D,M*v) =
dot(M.transpose*D,v)` on the actual 289 source coordinates. -/
private theorem contraction_transpose (M : Matrix (Fin 289) (Fin 289) ℂ)
    (u v : Fin 289→ℂ) :
    (∑i,u i*(M*ᵥv) i)=∑j,(M.transpose*ᵥu) j*v j:=by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem single_pair_dot (a b c d : ℂ) :
    (∑j : Fin 289,((Pi.single 0 a : Fin 289→ℂ)+(Pi.single 1 b : Fin 289→ℂ)) j*
      ((Pi.single 0 c : Fin 289→ℂ)+(Pi.single 1 d : Fin 289→ℂ)) j)=
      a*c+b*d:=by
  simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  rw [single_dot 0 a _,single_dot 1 b _]
  simp only [Pi.single_apply]
  rw [if_pos trivial,if_neg fin01,if_neg fin10,if_pos trivial]
  ring

/-- The complete actual static scalar: the generated seed times both original
source-composite weights, on the same independent detector/source
preparations as `sourceStaticSpatialInteraction`. -/
def emCompleteStaticScalar
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  emStaticCompleteSeed*
    sourceStaticCompositeWeight epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD*
    sourceStaticCompositeWeight epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS

/-- The original full-source residue contraction returns minus the complete
actual static scalar: both origin projections land on the same `{0,1}`
slice, the paid inverse sends it to `single0+single1` weights, and the
detector projection reads them back with its own `w_J`. -/
theorem em_complete_static_residue
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
      staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)=
      -emCompleteStaticScalar
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS:=by
  rw [staticResidue,contraction_transpose,
    sourceStaticComposite_origin epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD,
    sourceStaticComposite_origin epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS,
    emStaticInverse_weight,single_pair_dot,emCompleteStaticScalar,
    em_static_seed_generated]
  ring

/-- The actual whole-ordinary interaction scaled by positive `κ²` tends to the
complete actual static scalar (the original pole theorem used `-κ²`). -/
theorem em_complete_static_limit (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      sourceStaticSpatialInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)
      staticApproach (𝓝 (emCompleteStaticScalar
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)):=by
  have generated:=sourceStaticSpatialInteraction_generated direction unit
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS
  rw [em_complete_static_residue
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS] at generated
  have negated:=generated.neg
  rw [neg_neg] at negated
  have shape (kappa : staticDomain) : (kappa.val:ℂ)^2*
      sourceStaticSpatialInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS=
      -((-(kappa.val:ℂ)^2)*
        sourceStaticSpatialInteraction direction unit kappa
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS):=by ring
  simpa only [shape] using negated

/-- The same scalar on the original `h_source*c_source` unit. -/
def emCompleteStaticReducedScalar
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  emCompleteStaticScalar
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS/
    ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed 0:ℝ):ℂ)

/-- The actual full-current scalar read divided by the source `h*c` unit; no
new charge normalizer and no `w_J=e` rename is inserted. -/
theorem em_complete_static_reduced_limit (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      sourceStaticSpatialInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed 0:ℝ):ℂ))
      staticApproach (𝓝 (emCompleteStaticReducedScalar
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)):=by
  unfold emCompleteStaticReducedScalar
  exact (em_complete_static_limit direction unit
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS).div_const _

end LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar
