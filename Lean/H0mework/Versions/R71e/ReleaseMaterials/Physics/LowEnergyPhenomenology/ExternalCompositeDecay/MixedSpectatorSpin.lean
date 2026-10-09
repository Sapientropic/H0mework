import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorCandidate
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussCoframeSpin
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSpinCasimir
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid SaturationMonoid.PhysicsCore
open QuantizationCheck.Fermion
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


private theorem rotation_entry (dual : Bool) (k : Fin 3) (r c : Fin 4) :
    spinEntry dual (NamedColorQtNext.rotationAxis k) r c =
      NamedColorQtNext.rotationEntry dual k r c :=
  NamedColorQtNext.actual_rotation_entry dual k r c

private theorem actual_triple_spin_half (dual : Bool) (a b c : Fin 3) :
    NamedColorQtNext.originalSpinCasimir
      (orderedTriple dual (0,a,0) (1,b,0) (2,c,1) -
        orderedTriple dual (0,a,0) (0,b,0) (3,c,1)) =
      (3/4 : ℂ) • (orderedTriple dual (0,a,0) (1,b,0) (2,c,1) -
        orderedTriple dual (0,a,0) (0,b,0) (3,c,1)) := by
  simp only [NamedColorQtNext.originalSpinCasimir, _root_.sum_apply,
    mul_apply_eq_comp, map_sub, actual_spin_ordered_triple,
    map_add, map_sum, map_smul, rotation_entry]
  cases dual <;>
    norm_num [Fin.sum_univ_three, Fin.sum_univ_four, NamedColorQtNext.rotationEntry,
      NamedColorQtNext.flipSpin, NamedColorQtNext.bitSign]
  all_goals simp +decide
  all_goals match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

theorem actual_candidate_spin_half (dual : Bool) :
    NamedColorQtNext.originalSpinCasimir (candidate dual) = (3/4 : ℂ) • candidate dual := by
  have he : candidate dual = (1/3 : ℂ) • ∑ p : Fin 6,
      NamedMatterWedgeQt.colorSign p •
        (orderedTriple dual (0, NamedMatterWedgeQt.colorPerm p 0, 0)
          (1, NamedMatterWedgeQt.colorPerm p 1, 0) (2, NamedMatterWedgeQt.colorPerm p 2, 1) -
        orderedTriple dual (0, NamedMatterWedgeQt.colorPerm p 0, 0)
          (0, NamedMatterWedgeQt.colorPerm p 1, 0) (3, NamedMatterWedgeQt.colorPerm p 2, 1)) := by
    simp only [candidate, epsilon, Finset.sum_sub_distrib, smul_sub]
    rfl
  rw [he, map_smul, map_sum]
  simp only [map_smul, actual_triple_spin_half, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  module

end LowEnergy.MixedSpectatorCandidate
