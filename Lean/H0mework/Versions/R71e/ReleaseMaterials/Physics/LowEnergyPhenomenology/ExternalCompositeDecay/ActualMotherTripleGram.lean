import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorCandidate
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussYukawaCoefficient
import H0mework.Physics.LowEnergy.FullQuantum.NativeHistory.CurrentCAR
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMotherCAR
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=SourceRealScalarFock.branchOrder.toDecidableEq

def delta(i j:Mode):ℂ:=if i=j then 1 else 0

def sourceVacuum : FockFiber := EuclideanSpace.single ∅ 1

def triple (i j k : Mode) : FockFiber :=
  GaussCARHistory.createFiber i (GaussCARHistory.createFiber j (GaussCARHistory.createFiber k sourceVacuum))

private theorem vacuum_annihilates(i:Mode):
    GaussCARHistory.annihilateFiber i sourceVacuum=0:=by
  apply fiberCoordinates.injective
  have hv:fiberCoordinates sourceVacuum=(vacuum:Fock Mode):=by
    funext s
    simp [sourceVacuum,fiberCoordinates,EuclideanSpace.single,vacuum,occupationBasis]
  change fiberCoordinates (SourceCARBound.annihilateOp i sourceVacuum)=fiberCoordinates 0
  rw [SourceCARBound.annihilateOp,SourceCARBound.coordinates_liftOp,LowEnergy.Fermion.annihilation_apply,
    hv,annihilate_vacuum,map_zero]

private theorem vacuum_pair:inner ℂ sourceVacuum sourceVacuum=1:=by
  simp [sourceVacuum]

private theorem actual_ann_create(i j:Mode)(x:FockFiber):
    GaussCARHistory.annihilateFiber i (GaussCARHistory.createFiber j x)=
      delta i j • x-GaussCARHistory.createFiber j
        (GaussCARHistory.annihilateFiber i x):=by
  have h:=congrArg (fun T:FockFiber→L[ℂ]FockFiber=>T x) (GaussCARHistory.fiber_car i j)
  simp only [_root_.add_apply,mul_apply_eq_comp] at h
  by_cases hij:i=j
  · simp only [hij,ite_true,one_apply_eq_self] at h
    simpa only [delta,hij,ite_true,one_smul] using (eq_sub_iff_add_eq.mpr h)
  · simp only [hij,ite_false,_root_.zero_apply] at h
    simpa only [delta,hij,ite_false,zero_smul] using (eq_sub_iff_add_eq.mpr h)

private theorem actual_create_pair(i:Mode)(x y:FockFiber):
    inner ℂ (GaussCARHistory.createFiber i x) y=
      inner ℂ x (GaussCARHistory.annihilateFiber i y):=
  SourceCARBound.create_adjoint _ x y

private def one(i:Mode):FockFiber:=
  GaussCARHistory.createFiber i sourceVacuum
private def two(i j:Mode):FockFiber:=
  GaussCARHistory.createFiber i (one j)

private theorem ann_one(i j:Mode):
    GaussCARHistory.annihilateFiber i (one j)=delta i j • sourceVacuum:=by
  rw [one,actual_ann_create,vacuum_annihilates,map_zero,sub_zero]
private theorem pair_one(i j:Mode):
    inner ℂ (one i) (one j)=delta i j:=by
  rw [one,actual_create_pair]
  rw [ann_one,inner_smul_right,vacuum_pair,mul_one]

private theorem ann_two(i j k:Mode):
    GaussCARHistory.annihilateFiber i (two j k)=
      delta i j • one k-delta i k • one j:=by
  rw [two,actual_ann_create,ann_one,map_smul]
  rfl
private theorem pair_two(i j k l:Mode):
    inner ℂ (two i j) (two k l)=delta i k*delta j l-delta i l*delta j k:=by
  rw [two,actual_create_pair]
  rw [ann_two,inner_sub_right,inner_smul_right,inner_smul_right,pair_one,pair_one]

private theorem ann_triple(i a b c:Mode):
    GaussCARHistory.annihilateFiber i (triple a b c)=
      delta i a • two b c-delta i b • two a c+delta i c • two a b:=by
  change GaussCARHistory.annihilateFiber i
    (GaussCARHistory.createFiber a (two b c))=_
  rw [actual_ann_create,ann_two,map_sub,map_smul,map_smul]
  change delta i a • two b c-(delta i b • two a c-delta i c • two a b)=_
  abel

def tripleGram(i j k a b c:Mode):ℂ:=
  delta i a*(delta j b*delta k c-delta j c*delta k b)-
  delta i b*(delta j a*delta k c-delta j c*delta k a)+
  delta i c*(delta j a*delta k b-delta j b*delta k a)

/-- The original mother CAR and vacuum generate the three-particle Gram, with no ordering or distinctness premise. -/
theorem actual_ordered_triple_pair(i j k a b c:Mode):
    inner ℂ (triple i j k) (triple a b c)=tripleGram i j k a b c:=by
  change inner ℂ (GaussCARHistory.createFiber i (two j k))
    (triple a b c)=_
  rw [actual_create_pair,ann_triple,inner_add_right,inner_sub_right,
    inner_smul_right,inner_smul_right,inner_smul_right,pair_two,pair_two,pair_two]
  rfl

theorem quantized_create (H : Matrix Mode Mode ℂ) (i : Mode) (x : FockFiber) :
    GaussQuantumMultiplier.quantized H (GaussCARHistory.createFiber i x) =
      GaussCARHistory.createFiber i (GaussQuantumMultiplier.quantized H x) +
        ∑j : Mode, H j i • GaussCARHistory.createFiber j x := by
  apply fiberCoordinates.injective
  have h := LinearMap.congr_fun
    (LowEnergy.FullQuantum.NativeHistory.CurrentCAR.creation_quantize H i) (fiberCoordinates x)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] at h
  simp only [map_add,map_sum,map_smul]
  change LowEnergy.Fermion.quantize H (LowEnergy.Fermion.creation i (fiberCoordinates x)) =
    LowEnergy.Fermion.creation i (LowEnergy.Fermion.quantize H (fiberCoordinates x)) +
      ∑j : Mode, H j i • LowEnergy.Fermion.creation j (fiberCoordinates x)
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

private theorem quantized_vacuum (H : Matrix Mode Mode ℂ) :
    GaussQuantumMultiplier.quantized H sourceVacuum = 0 := by
  apply fiberCoordinates.injective
  have hv : fiberCoordinates sourceVacuum = (vacuum : Fock Mode) := by
    funext s
    simp [sourceVacuum,fiberCoordinates,EuclideanSpace.single,vacuum,occupationBasis]
  change LowEnergy.Fermion.quantize H (fiberCoordinates sourceVacuum) = fiberCoordinates 0
  rw [hv,map_zero]
  simp only [LowEnergy.Fermion.quantize,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    LowEnergy.Fermion.annihilation_apply,annihilate_vacuum,map_zero,smul_zero,Finset.sum_const_zero]

theorem actual_quantized_triple (H : Matrix Mode Mode ℂ) (i j k : Mode) :
    GaussQuantumMultiplier.quantized H (triple i j k) =
      (∑r : Mode, H r i • triple r j k) +
      (∑r : Mode, H r j • triple i r k) +
      (∑r : Mode, H r k • triple i j r) := by
  rw [triple,quantized_create,quantized_create,quantized_create,quantized_vacuum]
  simp only [map_zero,zero_add,map_add,map_sum,map_smul,triple]
  abel

theorem actual_quantized_triple_pair (H : Matrix Mode Mode ℂ) (a b c i j k : Mode) :
    inner ℂ (triple a b c) (GaussQuantumMultiplier.quantized H (triple i j k)) =
      (∑r : Mode, H r i * tripleGram a b c r j k) +
      (∑r : Mode, H r j * tripleGram a b c i r k) +
      (∑r : Mode, H r k * tripleGram a b c i j r) := by
  rw [actual_quantized_triple]
  simp only [inner_add_right,inner_sum,inner_smul_right,actual_ordered_triple_pair]

end LowEnergy.ActualMotherCAR
