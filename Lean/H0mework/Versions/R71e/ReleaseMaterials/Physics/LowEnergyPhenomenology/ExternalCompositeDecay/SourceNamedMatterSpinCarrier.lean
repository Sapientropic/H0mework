import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterCompleteColorKernel
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussCoframeSpin
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore
open NamedMatterWedgeQt QuantizationCheck.Fermion
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq LowEnergy.Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=SourceRealScalarFock.branchOrder.toDecidableEq

def spinEntry(dual:Bool)(a:Fin 7)(r c:Fin 4):ℂ:=
  if dual then (if a.val<3 then star (GaussCoframeSpin.sourceSpin a r c)
    else -star (GaussCoframeSpin.sourceSpin a r c)) else GaussCoframeSpin.sourceSpin a r c

private theorem primal_spin_column(a:Fin 7)(i:NamedMode)(j:LowEnergy.Quantum.Index):
    GaussCoframeSpin.primal a j (rootIndex i)=
      ∑r:Fin 4,GaussCoframeSpin.sourceSpin a r i.1*(if j=rootIndex (r,i.2) then 1 else 0):=by
  rcases j with ⟨q,k⟩
  by_cases hk:k=(rootIndex i).2
  · simp only [GaussCoframeSpin.primal,GaussCoframeSpin.spinLift,hk,ite_true]
    simp [rootIndex,mul_ite]
  · simp only [GaussCoframeSpin.primal,GaussCoframeSpin.spinLift,hk,ite_false]
    have hr(r:Fin 4):(⟨q,k⟩:LowEnergy.Quantum.Index)≠rootIndex (r,i.2):=by
      intro h
      exact hk (congrArg (fun v:LowEnergy.Quantum.Index=>v.2) h)
    simp [hr]

/-- The original full504 spin columns retain the exact boost/rotation dual sign. -/
theorem actual_full_spin_column(dual:Bool)(a:Fin 7)(i:NamedMode)(j:Mode):
    GaussCoframeSpin.full a j (rootMode dual i)=
      ∑r:Fin 4,spinEntry dual a r i.1*(if j=rootMode dual (r,i.2) then 1 else 0):=by
  cases dual with
  | false=>
    cases j with
    | inl j=>simpa [GaussCoframeSpin.full,rootMode,spinEntry] using primal_spin_column a i j
    | inr j=>simp [GaussCoframeSpin.full,rootMode,spinEntry]
  | true=>
    cases j with
    | inl j=>simp [GaussCoframeSpin.full,rootMode,spinEntry]
    | inr j=>
      have h:=congrArg star (primal_spin_column a i j)
      by_cases ha:a.val<3
      · simpa [GaussCoframeSpin.full,rootMode,spinEntry,ha,star_sum,star_mul,apply_ite] using h
      · have hl:GaussCoframeSpin.full a (Sum.inr j) (rootMode true i)=
            -star (GaussCoframeSpin.primal a j (rootIndex i)):=by
          simp [GaussCoframeSpin.full,rootMode,ha]
        rw [hl,h]
        simp only [star_sum,star_mul]
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r _
        by_cases hj:j=rootIndex (r,i.2) <;> simp [spinEntry,rootMode,ha,hj]

private theorem collapse_spin_column {V:Type*}[AddCommGroup V][Module ℂ V]
    {ι:Type*}[Fintype ι][DecidableEq ι](roots:Fin 4→ι)(b:Fin 4→ℂ)(X:ι→V):
    (∑j:ι,(∑r:Fin 4,b r*(if j=roots r then 1 else 0)) • X j)=∑r:Fin 4,b r • X (roots r):=by
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mul_ite,mul_one,mul_zero,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private theorem spin_create(dual:Bool)(a:Fin 7)(i:NamedMode)(x:FockFiber):
    GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)
      (GaussCARHistory.createFiber (rootMode dual i) x)=
    GaussCARHistory.createFiber (rootMode dual i)
      (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) x)+
      ∑r:Fin 4,spinEntry dual a r i.1 • GaussCARHistory.createFiber (rootMode dual (r,i.2)) x:=by
  apply fiberCoordinates.injective
  have h:=LinearMap.congr_fun
    (LowEnergy.FullQuantum.NativeHistory.CurrentCAR.creation_quantize
      (GaussCoframeSpin.full a) (rootMode dual i)) (fiberCoordinates x)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] at h
  simp_rw [actual_full_spin_column] at h
  have hc:=collapse_spin_column (fun r:Fin 4=>rootMode dual (r,i.2))
    (fun r=>spinEntry dual a r i.1)
    (fun j:Mode=>LowEnergy.Fermion.creation j (fiberCoordinates x))
  have hfinal:=h.trans hc
  simp only [map_add,map_sum,map_smul]
  change LowEnergy.Fermion.quantize (GaussCoframeSpin.full a)
      (LowEnergy.Fermion.creation (rootMode dual i) (fiberCoordinates x))=
    LowEnergy.Fermion.creation (rootMode dual i)
      (LowEnergy.Fermion.quantize (GaussCoframeSpin.full a) (fiberCoordinates x))+
      ∑r:Fin 4,spinEntry dual a r i.1 • LowEnergy.Fermion.creation (rootMode dual (r,i.2)) (fiberCoordinates x)
  exact sub_eq_iff_eq_add.mp hfinal |>.trans (add_comm _ _)

private theorem spin_vacuum(dual:Bool)(a:Fin 7):
    GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (occupationFiber dual ∅)=0:=by
  apply fiberCoordinates.injective
  have hv:fiberCoordinates (occupationFiber dual ∅)=(vacuum:Fock Mode):=by
    funext s
    simp [occupationFiber,occupation,fiberCoordinates,EuclideanSpace.single,vacuum,occupationBasis]
  change LowEnergy.Fermion.quantize (GaussCoframeSpin.full a)
    (fiberCoordinates (occupationFiber dual ∅))=fiberCoordinates 0
  rw [hv,map_zero]
  simp only [LowEnergy.Fermion.quantize,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    LowEnergy.Fermion.annihilation_apply,annihilate_vacuum,map_zero,smul_zero,Finset.sum_const_zero]

theorem actual_spin_ordered_triple(dual:Bool)(a:Fin 7)(i j k:NamedMode):
    GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (orderedTriple dual i j k)=
      (∑r:Fin 4,spinEntry dual a r i.1 • orderedTriple dual (r,i.2) j k)+
      (∑r:Fin 4,spinEntry dual a r j.1 • orderedTriple dual i (r,j.2) k)+
      (∑r:Fin 4,spinEntry dual a r k.1 • orderedTriple dual i j (r,k.2)):=by
  rw [orderedTriple,spin_create,spin_create,spin_create,spin_vacuum]
  simp only [map_zero,zero_add,map_add,map_sum,map_smul,orderedTriple]
  abel

theorem actual_spin_balanced(dual:Bool)(a:Fin 7)(t:ColorSpinAssignment):
    GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (balancedFiber dual t)=
      ∑p:Fin 3,∑r:Fin 4,spinEntry dual a r (t p) • balancedFiber dual (Function.update t p r):=by
  rw [balancedFiber,actual_spin_ordered_triple,Fin.sum_univ_three]
  simp only [balancedFiber,Function.update_self]
  abel

def spinBalancedAction(dual:Bool)(a:Fin 7):BalancedFiber→ₗ[ℂ]BalancedFiber where
  toFun b:=∑t:ColorSpinAssignment,∑p:Fin 3,∑r:Fin 4,
    (b t*spinEntry dual a r (t p)) • EuclideanSpace.single (Function.update t p r) 1
  map_add' b c:=by simp only [PiLp.add_apply,add_mul,add_smul,Finset.sum_add_distrib]
  map_smul' c b:=by simp only [PiLp.smul_apply,smul_eq_mul,mul_assoc,smul_smul,Finset.smul_sum,RingHom.id_apply]

private theorem balanced_single_return(dual:Bool)(t:ColorSpinAssignment):
    balancedLift dual (EuclideanSpace.single t 1)=balancedFiber dual t:=by
  classical
  change (∑u:ColorSpinAssignment,(EuclideanSpace.single t (1:ℂ)) u • balancedFiber dual u)=_
  simp only [PiLp.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- All seven original coframe-spin currents return to the same actual balanced CAR carrier. -/
theorem actual_spin_balanced_source(dual:Bool)(a:Fin 7)(b:BalancedFiber):
    GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (balancedLift dual b)=
      balancedLift dual (spinBalancedAction dual a b):=by
  change GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)
    (∑t:ColorSpinAssignment,b t • balancedFiber dual t)=balancedLift dual
    (∑t:ColorSpinAssignment,∑p:Fin 3,∑r:Fin 4,
      (b t*spinEntry dual a r (t p)) • EuclideanSpace.single (Function.update t p r) 1)
  simp only [map_sum,map_smul,actual_spin_balanced,balanced_single_return,Finset.smul_sum,smul_smul]

end LowEnergy.NamedColorQtNext
