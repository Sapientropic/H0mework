import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorCAR
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=SourceRealScalarFock.branchOrder.toDecidableEq

def delta(i j:NamedMode):ℂ:=if i=j then 1 else 0

private theorem vacuum_annihilates(dual:Bool)(i:NamedMode):
    GaussCARHistory.annihilateFiber (rootMode dual i) (occupationFiber dual ∅)=0:=by
  apply fiberCoordinates.injective
  have hv:fiberCoordinates (occupationFiber dual ∅)=(vacuum:Fock Mode):=by
    funext s
    simp [occupationFiber,occupation,fiberCoordinates,EuclideanSpace.single,vacuum,occupationBasis]
  change fiberCoordinates (SourceCARBound.annihilateOp (rootMode dual i) (occupationFiber dual ∅))=fiberCoordinates 0
  rw [SourceCARBound.annihilateOp,SourceCARBound.coordinates_liftOp,LowEnergy.Fermion.annihilation_apply,
    hv,annihilate_vacuum,map_zero]

private theorem vacuum_pair(dual:Bool):inner ℂ (occupationFiber dual ∅) (occupationFiber dual ∅)=1:=by
  simp [occupationFiber]

private theorem actual_ann_create(dual:Bool)(i j:NamedMode)(x:FockFiber):
    GaussCARHistory.annihilateFiber (rootMode dual i) (GaussCARHistory.createFiber (rootMode dual j) x)=
      delta i j • x-GaussCARHistory.createFiber (rootMode dual j)
        (GaussCARHistory.annihilateFiber (rootMode dual i) x):=by
  have h:=congrArg (fun T:FockFiber→L[ℂ]FockFiber=>T x) (actual_named_car dual i j)
  simp only [_root_.add_apply,mul_apply_eq_comp] at h
  by_cases hij:i=j
  · simp only [hij,ite_true,one_apply_eq_self] at h
    simpa only [delta,hij,ite_true,one_smul] using (eq_sub_iff_add_eq.mpr h)
  · simp only [hij,ite_false,_root_.zero_apply] at h
    simpa only [delta,hij,ite_false,zero_smul] using (eq_sub_iff_add_eq.mpr h)

private theorem actual_create_pair(dual:Bool)(i:NamedMode)(x y:FockFiber):
    inner ℂ (GaussCARHistory.createFiber (rootMode dual i) x) y=
      inner ℂ x (GaussCARHistory.annihilateFiber (rootMode dual i) y):=
  SourceCARBound.create_adjoint _ x y

private def one(dual:Bool)(i:NamedMode):FockFiber:=
  GaussCARHistory.createFiber (rootMode dual i) (occupationFiber dual ∅)
private def two(dual:Bool)(i j:NamedMode):FockFiber:=
  GaussCARHistory.createFiber (rootMode dual i) (one dual j)

private theorem ann_one(dual:Bool)(i j:NamedMode):
    GaussCARHistory.annihilateFiber (rootMode dual i) (one dual j)=delta i j • occupationFiber dual ∅:=by
  rw [one,actual_ann_create,vacuum_annihilates,map_zero,sub_zero]
private theorem pair_one(dual:Bool)(i j:NamedMode):
    inner ℂ (one dual i) (one dual j)=delta i j:=by
  rw [one,actual_create_pair]
  rw [ann_one,inner_smul_right,vacuum_pair,mul_one]

private theorem ann_two(dual:Bool)(i j k:NamedMode):
    GaussCARHistory.annihilateFiber (rootMode dual i) (two dual j k)=
      delta i j • one dual k-delta i k • one dual j:=by
  rw [two,actual_ann_create,ann_one,map_smul]
  rfl
private theorem pair_two(dual:Bool)(i j k l:NamedMode):
    inner ℂ (two dual i j) (two dual k l)=delta i k*delta j l-delta i l*delta j k:=by
  rw [two,actual_create_pair]
  rw [ann_two,inner_sub_right,inner_smul_right,inner_smul_right,pair_one,pair_one]

private theorem ann_triple(dual:Bool)(i a b c:NamedMode):
    GaussCARHistory.annihilateFiber (rootMode dual i) (orderedTriple dual a b c)=
      delta i a • two dual b c-delta i b • two dual a c+delta i c • two dual a b:=by
  change GaussCARHistory.annihilateFiber (rootMode dual i)
    (GaussCARHistory.createFiber (rootMode dual a) (two dual b c))=_
  rw [actual_ann_create,ann_two,map_sub,map_smul,map_smul]
  change delta i a • two dual b c-(delta i b • two dual a c-delta i c • two dual a b)=_
  abel

def tripleGram(i j k a b c:NamedMode):ℂ:=
  delta i a*(delta j b*delta k c-delta j c*delta k b)-
  delta i b*(delta j a*delta k c-delta j c*delta k a)+
  delta i c*(delta j a*delta k b-delta j b*delta k a)

/-- The original mother CAR and vacuum generate the three-particle Gram, with no ordering or distinctness premise. -/
theorem actual_ordered_triple_pair(dual:Bool)(i j k a b c:NamedMode):
    inner ℂ (orderedTriple dual i j k) (orderedTriple dual a b c)=tripleGram i j k a b c:=by
  change inner ℂ (GaussCARHistory.createFiber (rootMode dual i) (two dual j k))
    (orderedTriple dual a b c)=_
  rw [actual_create_pair,ann_triple,inner_add_right,inner_sub_right,
    inner_smul_right,inner_smul_right,inner_smul_right,pair_two,pair_two,pair_two]
  rfl

end LowEnergy.MixedSpectatorCandidate
