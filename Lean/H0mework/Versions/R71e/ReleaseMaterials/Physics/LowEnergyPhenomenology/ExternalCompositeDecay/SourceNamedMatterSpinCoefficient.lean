import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSpinCarrier
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore NamedMatterWedgeQt
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace Matrix

private def assignmentEquiv:(Fin 4×Fin 4×Fin 4)≃ColorSpinAssignment where
  toFun v:=![v.1,v.2.1,v.2.2]
  invFun t:=(t 0,t 1,t 2)
  left_inv v:=by rcases v with ⟨x,y,z⟩; rfl
  right_inv t:=by funext i; fin_cases i <;> rfl

private theorem assignment_sum {V:Type*}[AddCommMonoid V](f:ColorSpinAssignment→V):
    (∑t:ColorSpinAssignment,f t)=∑x:Fin 4,∑y:Fin 4,∑z:Fin 4,f ![x,y,z]:=by
  rw [←assignmentEquiv.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem assignment_equal(t:ColorSpinAssignment)(x y z:Fin 4):
    t=![x,y,z] ↔ t 0=x ∧ t 1=y ∧ t 2=z:=by
  simp [funext_iff,Fin.forall_fin_succ]

private theorem update_zero(t:ColorSpinAssignment)(r:Fin 4):Function.update t 0 r=![r,t 1,t 2]:=by
  funext p
  fin_cases p <;> simp [Function.update]
private theorem update_one(t:ColorSpinAssignment)(r:Fin 4):Function.update t 1 r=![t 0,r,t 2]:=by
  funext p
  fin_cases p <;> simp [Function.update]
private theorem update_two(t:ColorSpinAssignment)(r:Fin 4):Function.update t 2 r=![t 0,t 1,r]:=by
  funext p
  fin_cases p <;> simp [Function.update]

private theorem coordinate_gram(dual:Bool)(b:BalancedFiber)(t:ColorSpinAssignment):
    inner ℂ (balancedFiber dual t) (balancedLift dual b)=b t:=by
  classical
  change inner ℂ (balancedFiber dual t) (∑u,b u • balancedFiber dual u)=_
  simp only [inner_sum,inner_smul_right,actual_balanced_pair]
  simp [mul_ite]

/-- The original creation-column action generates the coefficient-row return, including the independent dual sign. -/
theorem actual_spin_coefficient(dual:Bool)(a:Fin 7)(b:BalancedFiber)(t:ColorSpinAssignment):
    spinBalancedAction dual a b t=
      ∑p:Fin 3,∑r:Fin 4,spinEntry dual a (t p) r*b (Function.update t p r):=by
  classical
  change (∑u:ColorSpinAssignment,∑p:Fin 3,∑r:Fin 4,
    (b u*spinEntry dual a r (u p)) • EuclideanSpace.single (Function.update u p r) 1) t=_
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,PiLp.single_apply,smul_eq_mul]
  rw [assignment_sum]
  simp only [Fin.sum_univ_three]
  simp only [update_zero,update_one,update_two]
  simp [assignment_equal,Finset.sum_add_distrib,ite_and,mul_comm]

theorem actual_spin_row(dual:Bool)(a:Fin 7)(b:BalancedFiber)(x y z:Fin 4):
    spinBalancedAction dual a b ![x,y,z]=
      (∑r:Fin 4,spinEntry dual a x r*b ![r,y,z])+
      (∑r:Fin 4,spinEntry dual a y r*b ![x,r,z])+
      (∑r:Fin 4,spinEntry dual a z r*b ![x,y,r]):=by
  rw [actual_spin_coefficient,Fin.sum_univ_three]
  simp only [update_zero,update_one,update_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rfl

/-- The original spin action preserves the complete color kernel, by its actual coefficient word. -/
theorem actual_spin_symmetric(dual:Bool)(a:Fin 7)(b:BalancedFiber)(hb:b∈symmetricCarrier):
    spinBalancedAction dual a b∈symmetricCarrier:=by
  constructor
  · intro x y z
    have h0:(∑r:Fin 4,spinEntry dual a x r*b ![r,y,z])=
        ∑r:Fin 4,spinEntry dual a x r*b ![y,r,z]:=by
      apply Finset.sum_congr rfl
      intro r _
      rw [hb.1 r y z]
    have h1:(∑r:Fin 4,spinEntry dual a y r*b ![x,r,z])=
        ∑r:Fin 4,spinEntry dual a y r*b ![r,x,z]:=by
      apply Finset.sum_congr rfl
      intro r _
      rw [hb.1 x r z]
    have h2:(∑r:Fin 4,spinEntry dual a z r*b ![x,y,r])=
        ∑r:Fin 4,spinEntry dual a z r*b ![y,x,r]:=by
      apply Finset.sum_congr rfl
      intro r _
      rw [hb.1 x y r]
    rw [actual_spin_row,actual_spin_row,h0,h1,h2]
    ring
  · intro x y z
    have h0:(∑r:Fin 4,spinEntry dual a x r*b ![r,y,z])=
        ∑r:Fin 4,spinEntry dual a x r*b ![r,z,y]:=by
      apply Finset.sum_congr rfl
      intro r _
      rw [hb.2 r y z]
    have h1:(∑r:Fin 4,spinEntry dual a y r*b ![x,r,z])=
        ∑r:Fin 4,spinEntry dual a y r*b ![x,z,r]:=by
      apply Finset.sum_congr rfl
      intro r _
      rw [hb.2 x r z]
    have h2:(∑r:Fin 4,spinEntry dual a z r*b ![x,y,r])=
        ∑r:Fin 4,spinEntry dual a z r*b ![x,r,y]:=by
      apply Finset.sum_congr rfl
      intro r _
      rw [hb.2 x y r]
    rw [actual_spin_row,actual_spin_row,h0,h1,h2]
    ring

def rotationAxis(k:Fin 3):Fin 7:=⟨k.val+3,by omega⟩
def flipSpin(i:Fin 4):Fin 4:=![1,0,3,2] i
def bitSign(i:Fin 4):ℚ:=if i.val%2=0 then 1 else -1

def rotationEntry(dual:Bool)(k:Fin 3)(r c:Fin 4):ℂ:=
  if k=0 then (if r=flipSpin c then (if dual then 1 else -1)/2 else 0)
  else if k=1 then (if r=flipSpin c then (-Complex.I/2)*(bitSign c:ℂ) else 0)
  else (if r=c then ((if dual then 1 else -1)/2)*(bitSign c:ℂ) else 0)

private theorem rotation_entry_0(dual:Bool)(r c:Fin 4):
    spinEntry dual (rotationAxis 0) r c=rotationEntry dual 0 r c:=by
  cases dual <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinEntry,rotationAxis,rotationEntry,flipSpin,bitSign,GaussCoframeSpin.sourceSpin,
      DiracCliffordRepresentation.diracGammaOne,DiracCliffordRepresentation.diracGammaTwo,
      DiracCliffordRepresentation.diracGammaThree,Matrix.smul_apply,Matrix.mul_apply,
      Fin.sum_univ_four,Fin.coe_ofNat_eq_mod,Matrix.cons_val,Nat.reduceMod,
      Matrix.cons_val_two,Matrix.cons_val_three] <;> (try simp +decide) <;> ring_nf <;> norm_num [Complex.I_sq]

private theorem rotation_entry_1(dual:Bool)(r c:Fin 4):
    spinEntry dual (rotationAxis 1) r c=rotationEntry dual 1 r c:=by
  cases dual <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinEntry,rotationAxis,rotationEntry,flipSpin,bitSign,GaussCoframeSpin.sourceSpin,
      DiracCliffordRepresentation.diracGammaOne,DiracCliffordRepresentation.diracGammaTwo,
      DiracCliffordRepresentation.diracGammaThree,Matrix.smul_apply,Matrix.mul_apply,
      Fin.sum_univ_four,Fin.coe_ofNat_eq_mod,Matrix.cons_val,Nat.reduceMod,
      Matrix.cons_val_two,Matrix.cons_val_three] <;> (try simp +decide) <;> ring_nf

private theorem rotation_entry_2(dual:Bool)(r c:Fin 4):
    spinEntry dual (rotationAxis 2) r c=rotationEntry dual 2 r c:=by
  cases dual <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinEntry,rotationAxis,rotationEntry,flipSpin,bitSign,GaussCoframeSpin.sourceSpin,
      DiracCliffordRepresentation.diracGammaOne,DiracCliffordRepresentation.diracGammaTwo,
      DiracCliffordRepresentation.diracGammaThree,Matrix.smul_apply,Matrix.mul_apply,
      Fin.sum_univ_four,Fin.coe_ofNat_eq_mod,Matrix.cons_val,Nat.reduceMod,
      Matrix.cons_val_two,Matrix.cons_val_three] <;> (try simp +decide) <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The rotation word is calculated from the literal original gamma matrices and the full dual convention. -/
theorem actual_rotation_entry(dual:Bool)(k:Fin 3)(r c:Fin 4):
    spinEntry dual (rotationAxis k) r c=rotationEntry dual k r c:=by
  fin_cases k
  · exact rotation_entry_0 dual r c
  · exact rotation_entry_1 dual r c
  · exact rotation_entry_2 dual r c

end LowEnergy.NamedColorQtNext
