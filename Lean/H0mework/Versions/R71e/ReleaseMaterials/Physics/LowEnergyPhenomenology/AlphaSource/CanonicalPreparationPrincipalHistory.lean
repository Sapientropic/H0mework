import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePoleQuantumWard
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceAmputatedPreparedVertex

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalZeroRead
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumRawJointFeedback
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPropagationPencil PreparationVacuumFieldConstraintResponse FullYSourceCutoffVolterra
open scoped BigOperators Topology InnerProductSpace
abbrev ZeroReadOp := H→L[ℂ] H
attribute [local irreducible] jointGenerator jointResolvent sourcePoleRead rawReader actualC actualA physicalTime
  finitePrefix sourcePoleActionEuler

private theorem prefix_sum (C A : ZeroReadOp) (n : ℕ) (t : ℝ) :
    partialEvolution C A n t=∑j∈Finset.range (n+1),finitePrefix C A j t :=by
  induction n with
  | zero=>simp [partialEvolution,finitePrefix,orderedIntegral]
  | succ n ih=>
    rw [partialEvolution,Finset.sum_range_succ]
    exact congrArg (fun X : ZeroReadOp=>X+finitePrefix C A (n+1) t) ih

/-- Both orders belong to the actual uncut history, including independent inverse left time. -/
def sourcePrincipalBlock (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (reader : Field289) (j k : Fin 57) (t : ℝ) : ZeroReadOp:=
  finitePrefix (actualC pL q.F) (actualA pL q.F) j.val (-t)*jointResolvent pL q.F q.z 0*
    rawReader reader pR q.F 0*jointResolvent pR q.F q.w 0*
      finitePrefix (actualC pR q.F) (actualA pR q.F) k.val t

/-- Total nilpotent history order; this is not a freely selected field direction. -/
def sourcePrincipalSector (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (reader : Field289) (n : Fin 113) (t : ℝ) : ZeroReadOp:=
  ∑j : Fin 57,∑k : Fin 57,if j.val+k.val=n.val then sourcePrincipalBlock q pL pR reader j k t else 0

private theorem sector_unique (j k : Fin 57) :
    ∃! n : Fin 113,j.val+k.val=n.val :=by
  refine ⟨⟨j.val+k.val,by omega⟩,rfl,?_⟩
  intro n same
  exact Fin.ext same.symm

private theorem history_regroup {A : Type*} [AddCommMonoid A] (B : Fin 57→Fin 57→A) :
    (∑j,∑k,B j k)=∑n : Fin 113,∑j : Fin 57,∑k : Fin 57,
      if j.val+k.val=n.val then B j k else 0 :=by
  conv_rhs=>rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  conv_rhs=>rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨n,same,unique⟩:=sector_unique j k
  symm
  rw [Finset.sum_eq_single n]
  · rw [if_pos same]
  · intro m _ different
    exact if_neg (fun h=>different (unique m h))
  · simp

theorem sourcePrincipalSector_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (reader : Field289) (t : ℝ) :
    fiveKernel reader pR (pL-pR) q.F q.z q.w t 0=
      ∑n : Fin 113,sourcePrincipalSector q pL pR reader n t :=by
  have pleft : pR+(pL-pR)=pL:=by ext i; simp
  rw [fiveKernel,pleft,actual_time_finitePrefix,actual_time_finitePrefix,prefix_sum,prefix_sum]
  simp only [Finset.sum_range,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑j : Fin 57,∑k : Fin 57,sourcePrincipalBlock q pL pR reader j k t)=
    ∑n : Fin 113,sourcePrincipalSector q pL pR reader n t
  unfold sourcePrincipalSector
  exact history_regroup (fun j k=>sourcePrincipalBlock q pL pR reader j k t)

def sourcePrincipalEulerSector (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (n : Fin 113) (t : ℝ) (i : Fin 289) : ℂ:=
  -sourcePoleRead q.epsilon q.precision pL pR left right
    (sourcePrincipalSector q pL pR (fieldUnit i) n t)

theorem sourcePrincipalEuler_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) :
    sourcePoleActionEuler q pL pR left right 0 t i=
      ∑n : Fin 113,sourcePrincipalEulerSector q pL pR left right n t i :=by
  rw [sourcePoleActionEuler_source,sourcePrincipalSector_generated,map_sum]
  unfold sourcePrincipalEulerSector
  symm
  exact Finset.sum_neg_distrib (fun n=>sourcePoleRead q.epsilon q.precision pL pR left right
    (sourcePrincipalSector q pL pR (fieldUnit i) n t))

def sourcePrincipalBlockPrice (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (reader : Field289) (j k : Fin 57) : ℝ:=
  ‖jointResolvent pL q.F q.z 0‖ *‖rawReader reader pR q.F 0‖ *‖jointResolvent pR q.F q.w 0‖ *
    ‖actualA pL q.F‖^j.val*‖actualA pR q.F‖^k.val

def sourcePrincipalSectorPrice (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (reader : Field289) (n : Fin 113) : ℝ:=
  ∑j : Fin 57,∑k : Fin 57,if j.val+k.val=n.val then sourcePrincipalBlockPrice q pL pR reader j k else 0

theorem sourcePrincipalBlock_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (reader : Field289) (j k : Fin 57) (t : ℝ) :
    ‖sourcePrincipalBlock q pL pR reader j k t‖ ≤  sourcePrincipalBlockPrice q pL pR reader j k*|t|^(j.val+k.val) :=by
  have L:=finitePrefix_bound (actualC pL q.F) (actualA pL q.F) (actualC_symmetric pL q.F) j.val (-t)
  rw [abs_neg] at L
  have R:=finitePrefix_bound (actualC pR q.F) (actualA pR q.F) (actualC_symmetric pR q.F) k.val t
  unfold sourcePrincipalBlock
  calc
    _≤‖finitePrefix (actualC pL q.F) (actualA pL q.F) j.val (-t)‖ *
      ‖jointResolvent pL q.F q.z 0‖ *‖rawReader reader pR q.F 0‖ *‖jointResolvent pR q.F q.w 0‖ *
      ‖finitePrefix (actualC pR q.F) (actualA pR q.F) k.val t‖:=by
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))) (norm_nonneg _))
    _≤(|t| *‖actualA pL q.F‖)^j.val*‖jointResolvent pL q.F q.z 0‖ *
      ‖rawReader reader pR q.F 0‖ *‖jointResolvent pR q.F q.w 0‖ *(|t| *‖actualA pR q.F‖)^k.val:=by gcongr
    _=sourcePrincipalBlockPrice q pL pR reader j k*|t|^(j.val+k.val):=by
      simp only [sourcePrincipalBlockPrice,mul_pow,pow_add]
      ring

theorem sourcePrincipalSector_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (reader : Field289) (n : Fin 113) (t : ℝ) :
    ‖sourcePrincipalSector q pL pR reader n t‖ ≤  sourcePrincipalSectorPrice q pL pR reader n*|t|^n.val :=by
  unfold sourcePrincipalSector sourcePrincipalSectorPrice
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  by_cases same : j.val+k.val=n.val
  · simp only [if_pos same]
    simpa only [same] using sourcePrincipalBlock_price q pL pR reader j k t
  · simp only [if_neg same,norm_zero,zero_mul,le_refl]

theorem sourcePrincipalEuler_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (n : Fin 113) (t : ℝ) (i : Fin 289) :
    ‖sourcePrincipalEulerSector q pL pR left right n t i‖ ≤
      sourcePrincipalSectorPrice q pL pR (fieldUnit i) n*|t|^n.val :=by
  unfold sourcePrincipalEulerSector
  rw [norm_neg]
  exact ((sourcePoleRead q.epsilon q.precision pL pR left right).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (sourcePoleRead_price q.epsilon q.precision pL pR left right)
      (norm_nonneg _)).trans ((one_mul _).le.trans (sourcePrincipalSector_price q pL pR (fieldUnit i) n t)))

end LowEnergy.PreparationVacuumPhysicalZeroRead
