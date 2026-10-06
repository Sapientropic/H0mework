import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaNormalizedCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussYukawaInteraction
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussRadialHamiltonian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGradedRadial
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaOperator
open GaussCoreLabel NativeHistoryGrade SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceClockYukawaNormalizedCurrent SourceClockYukawaTail
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
local instance labelFintype : Fintype Label := Fintype.ofFinite _
attribute [local irreducible] fullAction normalizedAction diagonalAction compressionCore defectAction inverseAction
  bounded inverseRadius

/-- The orientation is fixed by the actual raising/lowering branch and its original grade bound. -/
def exponent (sharp : Bool) (g : Label) : ℕ := if sharp then 56-g.2.val else g.2.val

def radialWeight (sharp : Bool) : Op := ∑ g : Label,(inverseRadius^exponent sharp g)*projection g

def radialWeightCore (sharp : Bool) : End := ∑ g : Label,(inverseAction^exponent sharp g)*project g

attribute [local irreducible] radialWeight radialWeightCore

private theorem inverse_power_core (n : ℕ) (f : QuantumTest) :
    (inverseRadius^n) (embed f)=embed ((inverseAction^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change inverseRadius ((inverseRadius^n) (embed f))=_
    rw [ih,inverse_core]
    rfl

theorem original_radial_weight_core (sharp : Bool) (f : QuantumTest) :
    radialWeight sharp (embed f)=embed (radialWeightCore sharp f) := by
  simp only [radialWeight,radialWeightCore,sum_apply,LinearMap.sum_apply,Module.End.mul_apply,
    mul_apply_eq_comp,map_sum,←embed_project,inverse_power_core]

private theorem grade_left (g : Label) : projection g*GaussYukawaGrade.grade=(g.2.val:ℂ) • projection g :=
  GaussYukawaInteraction.source_grade_left g
private theorem grade_right (g : Label) : GaussYukawaGrade.grade*projection g=(g.2.val:ℂ) • projection g :=
  GaussYukawaInteraction.source_grade_right g

private theorem graded_block_zero {A : Type*} [Ring A] [Algebra ℂ A]
    (G B P Q : A) (c d : ℂ) (hG : G*B=B*G+B)
    (hP : P*G=c • P) (hQ : G*Q=d • Q) (hne : c-d-1≠0) : P*B*Q=0 := by
  have h := congrArg (fun X : A => P*X*Q) hG
  have he : (c-d-1) • (P*B*Q)=0 := by
    have hl : P*(G*B)*Q=c • (P*B*Q) := by rw [←mul_assoc P G B,hP,smul_mul_assoc,smul_mul_assoc]
    have hr : P*(B*G+B)*Q=d • (P*B*Q)+P*B*Q := by
      simp only [mul_add,add_mul,mul_assoc,hQ,mul_smul_comm]
    rw [hl,hr] at h
    linear_combination (norm := module) h
  have hc := congrArg (fun X : A => (c-d-1)⁻¹ • X) he
  simpa only [smul_smul,inv_mul_cancel₀ hne,one_smul,smul_zero] using hc

private theorem raising_block (i j : Label) (hij : i.2.val≠j.2.val+1) :
    projection i*bounded*projection j=0 := by
  have hn : (i.2.val:ℂ)-(j.2.val:ℂ)-1≠0 := by
    intro hz
    have hc : (i.2.val:ℂ)=((j.2.val+1:ℕ):ℂ) := by push_cast;linear_combination hz
    exact hij (by exact_mod_cast hc)
  exact graded_block_zero GaussYukawaGrade.grade bounded (projection i) (projection j)
    (i.2.val:ℂ) (j.2.val:ℂ) GaussYukawaGrade.bounded_raises (grade_left i) (grade_right j) hn

private theorem projection_star (g : Label) : star (projection g)=projection g :=
  (projection_symmetric g).isSelfAdjoint.star_eq

private theorem projection_adjoint (g : Label) : (projection g).adjoint=projection g :=
  (projection_symmetric g).isSelfAdjoint.star_eq

private theorem source_block (sharp : Bool) (i j : Label)
    (hij : exponent sharp i≠exponent sharp j+1) : projection i*sourceB sharp*projection j=0 := by
  cases sharp
  · exact raising_block i j hij
  · have hn : j.2.val≠i.2.val+1 := by
      intro h
      apply hij
      simp only [exponent,if_true]
      have hi := i.2.isLt
      have hj := j.2.isLt
      omega
    have h := congrArg star (raising_block j i hn)
    simpa only [star_mul,star_zero,mul_assoc,sourceB,if_true,
      ContinuousLinearMap.star_eq_adjoint,projection_adjoint,map_zero] using h

private theorem source_inverse (sharp : Bool) : Commute inverseRadius (sourceB sharp) := by
  cases sharp
  · exact SourceSignedRadiusBalance.bounded_inverse_commute.symm
  · have hs : IsSelfAdjoint inverseRadius :=
      (show inverseRadius.toLinearMap.IsSymmetric from fun x y => inverse_pair x y).isSelfAdjoint
    have h := congrArg star SourceSignedRadiusBalance.bounded_inverse_commute.eq
    change inverseRadius*bounded.adjoint=bounded.adjoint*inverseRadius
    simpa only [star_mul,hs.star_eq] using! h

private theorem inverse_project (g : Label) : Commute inverseRadius (projection g) :=
  (show Commute (projection g) inverseRadius from GaussYukawaGrade.inverse_blocks g).symm

private theorem weighted_intertwiner {A ι : Type*} [Ring A] [Algebra ℂ A] [Fintype ι] [DecidableEq ι]
    (P : ι → A) (S B : A) (e : ι → ℕ)
    (hres : ∑ i,P i=1) (horth : ∀ i j,P i*P j=if i=j then P i else 0)
    (hSP : ∀ i,Commute S (P i)) (hSB : Commute S B)
    (hblock : ∀ i j,e i≠e j+1 → P i*B*P j=0) :
    (∑ i,S^e i*P i)*B=S*B*(∑ i,S^e i*P i) := by
  classical
  let T := ∑ i,S^e i*P i
  have left (i : ι) : P i*T=S^e i*P i := by
    dsimp only [T]
    rw [Finset.mul_sum]
    have h (j : ι) : P i*(S^e j*P j)=S^e j*(P i*P j) := by
      rw [←mul_assoc,(hSP i).symm.pow_right (e j) |>.eq,mul_assoc]
    simp_rw [h,horth]
    simp
  have right (j : ι) : T*P j=S^e j*P j := by
    dsimp only [T]
    simp only [Finset.sum_mul,mul_assoc,horth]
    simp
  have pair (i j : ι) : P i*(T*B)*P j=P i*(S*B*T)*P j := by
    have hl : P i*(T*B)*P j=S^e i*(P i*B*P j) := by
      rw [←mul_assoc (P i) T,left]
      noncomm_ring
    have hr : P i*(S*B*T)*P j=S^(e j+1)*(P i*B*P j) := by
      calc
        _=P i*S*B*(T*P j) := by noncomm_ring
        _=P i*S*B*(S^e j*P j) := by rw [right]
        _=S*P i*B*(S^e j*P j) := by rw [(hSP i).symm.eq]
        _=S*P i*(B*S^e j)*P j := by noncomm_ring
        _=S*P i*(S^e j*B)*P j := by rw [hSB.symm.pow_right (e j) |>.eq]
        _=S*(P i*S^e j)*B*P j := by noncomm_ring
        _=S*(S^e j*P i)*B*P j := by rw [(hSP i).symm.pow_right (e j) |>.eq]
        _=S^(e j+1)*(P i*B*P j) := by rw [pow_succ'];noncomm_ring
    rw [hl,hr]
    by_cases h : e i=e j+1
    · rw [h]
    · rw [hblock i j h,mul_zero,mul_zero]
  change T*B=S*B*T
  calc
    _=(∑ i,P i)*(T*B)*(∑ j,P j) := by rw [hres,one_mul,mul_one]
    _=∑ i,∑ j,P i*(T*B)*P j := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
    _=∑ i,∑ j,P i*(S*B*T)*P j := by simp_rw [pair]
    _=(∑ i,P i)*(S*B*T)*(∑ j,P j) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
    _=_ := by rw [hres,one_mul,mul_one]

private theorem bounded_intertwiner (sharp : Bool) :
    radialWeight sharp*sourceB sharp=inverseRadius*sourceB sharp*radialWeight sharp := by
  unfold radialWeight
  exact weighted_intertwiner projection inverseRadius (sourceB sharp) (exponent sharp)
    projection_resolution projection_product inverse_project (source_inverse sharp) (source_block sharp)

private theorem inverse_weight (sharp : Bool) : Commute inverseRadius (radialWeight sharp) := by
  unfold radialWeight
  exact Commute.sum_right _ _ _ (fun g _ => (Commute.refl inverseRadius).pow_right _ |>.mul_right (inverse_project g))

/-- The original finite raising law removes Y's radial factor on the same full source core. -/
theorem original_graded_yukawa_return (sharp : Bool) :
    radialWeightCore sharp*fullAction sharp=normalizedAction sharp*radialWeightCore sharp := by
  apply LinearMap.ext
  intro f
  apply embed_injective
  apply inverse_injective
  simp only [Module.End.mul_apply]
  rw [←original_radial_weight_core,←original_normalized_core]
  change inverseRadius (radialWeight sharp (embed (fullAction sharp f)))=
    inverseRadius (sourceB sharp (embed (radialWeightCore sharp f)))
  rw [←original_radial_weight_core]
  have hs : inverseRadius (embed (fullAction sharp f))=sourceB sharp (embed f) := by
    rw [inverse_core,original_normalized_core]
    unfold normalizedAction
    rfl
  rw [show inverseRadius (radialWeight sharp (embed (fullAction sharp f)))=
    radialWeight sharp (inverseRadius (embed (fullAction sharp f))) from
      congrArg (fun A : Op => A (embed (fullAction sharp f))) (inverse_weight sharp).eq,hs]
  exact congrArg (fun A : Op => A (embed f)) (bounded_intertwiner sharp)

def radialPowerCurrent : ℕ → End
  | 0 => 0
  | n+1 => radialPowerCurrent n*inverseAction+inverseAction^n*GaussRadialHamiltonian.radialAction

private theorem hamiltonian_power (n : ℕ) : bracket diagonalAction (inverseAction^n)=radialPowerCurrent n := by
  induction n with
  | zero => simp [bracket,radialPowerCurrent]
  | succ n ih =>
    have h : bracket diagonalAction (inverseAction^(n+1))=
        bracket diagonalAction (inverseAction^n)*inverseAction+
          inverseAction^n*bracket diagonalAction inverseAction := by rw [pow_succ];unfold bracket;noncomm_ring
    rw [h,ih]
    have hs : bracket diagonalAction inverseAction=GaussRadialHamiltonian.radialAction := by
      unfold bracket
      rw [GaussRadialHamiltonian.diagonal_commutator,add_sub_cancel_left]
    rw [hs]
    rfl

def gradedRadialCurrent (sharp : Bool) : End := ∑ g : Label,radialPowerCurrent (exponent sharp g)*project g

/-- All non-scalar source sectors exit through their original label and radius commutation laws. -/
theorem original_graded_hamiltonian_current (sharp : Bool) :
    bracket diagonalAction (radialWeightCore sharp)=gradedRadialCurrent sharp := by
  have hp (g : Label) : diagonalAction*project g=project g*diagonalAction := by
    apply LinearMap.ext
    intro f
    exact (GaussDiagonalGrade.diagonal_action g f).symm
  have h (g : Label) : bracket diagonalAction ((inverseAction^exponent sharp g)*project g)=
      bracket diagonalAction (inverseAction^exponent sharp g)*project g := by
    unfold bracket
    linear_combination (norm := noncomm_ring) (inverseAction^exponent sharp g)*hp g
  unfold radialWeightCore gradedRadialCurrent
  simp only [bracket,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun g _ => (h g).trans (congrArg (·*project g) (hamiltonian_power _)))

def correctedGradedCurrent (sharp : Bool) (F : Index) : End :=
  gradedRadialCurrent sharp-bracket (defectAction F) (radialWeightCore sharp)

theorem actual_graded_compression_current (sharp : Bool) (F : Index) :
    bracket (compressionCore F) (radialWeightCore sharp)=correctedGradedCurrent sharp F := by
  rw [correctedGradedCurrent,←original_graded_hamiltonian_current]
  unfold defectAction bracket
  noncomm_ring

theorem original_full_graded_return (sharp : Bool) :
    radialWeightCore sharp*(diagonalAction+fullAction sharp)=
      (diagonalAction+normalizedAction sharp)*radialWeightCore sharp-gradedRadialCurrent sharp := by
  have hh := original_graded_hamiltonian_current sharp
  rw [bracket] at hh
  rw [mul_add,original_graded_yukawa_return,←hh]
  noncomm_ring

end LowEnergy.SourceClockYukawaGradedRadial
