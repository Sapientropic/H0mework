import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPhysicalFullResponseRay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3CausalWindow
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldPerturbation.Blocks PreparationVacuumFullPoleContinuation
open ActualEMJointCurrentMomentum ActualElectronPhysicalJointInverse ActualElectronWholeChargeSoft
open ActualElectronWholeNoetherObserver ActualDressedFullCoulomb ActualDressedNoether
open SourcePropagationCommonMomentum SourcePropagationTimeDependentFeedback
open SourceFamilyHilbert SourceFamilyOperator Filter
open scoped Topology InnerProductSpace
local instance realOperators : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] actualFullNoetherVariation jointResolvent jointCurrent jointGenerator jointHessian
  physicalTime noetherReader noetherReaderContact rawReaderContact timeSlope mixedVertex

private theorem variation_corner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C B : E→L[ℂ]E) (t : ℝ) :
    CanonicalGradedVariation.variation C B t=
      corner (SourceFiniteUnitary.time (diagonal C C+upper B) t) := by
  have block:=triangular_time C C B (1:ℂ) t
  simp only [one_smul] at block
  rw [block,map_add,corner_diagonal,corner_upper,zero_add]
  rw [crossTime_integral]
  simp only [CanonicalGradedVariation.variation,CanonicalGradedVariation.variationBetween,zero_smul,add_zero]

private theorem variation_joint_continuous {P E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C B : P→E→L[ℂ]E) (hc : Continuous C) (hb : Continuous B) :
    Continuous (fun pt : P×ℝ=>CanonicalGradedVariation.variation (C pt.1) (B pt.1) pt.2) := by
  let : Fact ((1:ENNReal)≤2):=⟨by norm_num⟩
  let : NormedAddCommGroup (Channel E):=WithLp.instProdNormedAddCommGroup 2 E E
  let : NormedSpace ℂ (Channel E):=WithLp.instProdNormedSpace 2 ℂ E E
  let : InnerProductSpace ℂ (Channel E):=WithLp.instProdInnerProductSpace
  let : NormedAlgebra ℝ (Channel E→L[ℂ]Channel E):=NormedAlgebra.restrictScalars ℝ ℂ _
  let : NormedAlgebra ℚ (Channel E→L[ℂ]Channel E):=NormedAlgebra.restrictScalars ℚ ℂ _
  let : NormedSpace ℝ (Channel E→L[ℂ]Channel E):=inferInstance
  have diagonalContinuous:=(diagonalMap (E:=E)).continuous.comp (hc.prodMk hc)
  have upperContinuous:=(blockMap (E:=E) injectOut projectIn).continuous.comp hb
  have blockContinuous:=diagonalContinuous.add upperContinuous
  have exponential:=NormedSpace.exp_continuous.comp
    ((continuous_snd : Continuous fun pt : P×ℝ=>pt.2).smul
      ((blockContinuous.comp (continuous_fst : Continuous fun pt : P×ℝ=>pt.1)).const_smul
        (-Complex.I)))
  have observed:=(corner (E:=E)).continuous.comp exponential
  simpa only [variation_corner,SourceFiniteUnitary.time,diagonalMap,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] using! observed

/-- The actual full time variation is jointly continuous in momentum and causal age. -/
theorem physical_n3_time_slope_joint (F : GaussUnitaryHistory.Index) (force : Field289) :
    Continuous (fun pt : PhysicalMomentum×ℝ=>timeSlope force pt.1 F pt.2) := by
  have current : Continuous (fun p : PhysicalMomentum=>jointCurrent p F 0 0 force):=
    (joint_current_momentum_continuous F 0).clm_apply continuous_const
  have generated:=variation_joint_continuous (fun p : PhysicalMomentum=>jointGenerator p F 0 0)
    (fun p : PhysicalMomentum=>jointCurrent p F 0 0 force) (jointGenerator_base_continuous F 0) current
  simpa only [timeSlope] using! generated

/-- The complete actual five-term Noether variation is jointly continuous in transfer and age. -/
theorem physical_n3_variation_joint (event : DressedEvent) (reader force : Field289) :
    Continuous (fun kt : PhysicalMomentum×ℝ=>actualFullNoetherVariation event (-kt.1) reader force kt.2) := by
  have momentum : Continuous (fun kt : PhysicalMomentum×ℝ=>event.momentum+kt.1):=
    (continuous_const (y:=event.momentum)).add continuous_fst
  have leftpair : Continuous (fun kt : PhysicalMomentum×ℝ=>(event.momentum+kt.1,-kt.2)):=by fun_prop
  have tl :=(actualJointTime_continuous event.frame).comp leftpair
  have l :=(actual_electron_physical_resolvent_continuous event.frame event.energy event.nonreal).comp momentum
  have dtl :=(physical_n3_time_slope_joint event.frame force).comp leftpair
  have current :=((joint_current_momentum_continuous event.frame event.energy).comp momentum).clm_apply
    (continuous_const (y:=force))
  have dl :=((l.mul current).mul l).neg
  have dJ : Continuous (fun _ : PhysicalMomentum×ℝ=>
      noetherReaderContact reader force event.momentum event.frame):=continuous_const
  have J : Continuous (fun _ : PhysicalMomentum×ℝ=>
      noetherReader reader event.momentum event.frame 0):=continuous_const
  have R : Continuous (fun _ : PhysicalMomentum×ℝ=>
      jointResolvent event.momentum event.frame event.energy 0):=continuous_const
  have dR : Continuous (fun _ : PhysicalMomentum×ℝ=>
      -(jointResolvent event.momentum event.frame event.energy 0*
        jointCurrent event.momentum event.frame event.energy 0 force*
        jointResolvent event.momentum event.frame event.energy 0)):=continuous_const
  have rightpair : Continuous (fun kt : PhysicalMomentum×ℝ=>(event.momentum,kt.2)):=by fun_prop
  have TR :=(actualJointTime_continuous event.frame).comp rightpair
  have dTR :=(physical_n3_time_slope_joint event.frame force).comp rightpair
  have generated:=(((((dtl.mul l).add (tl.mul dl)).mul J).add ((tl.mul l).mul dJ)).mul R |>.add
    (((tl.mul l).mul J).mul dR)).mul TR |>.add ((((tl.mul l).mul J).mul R).mul dTR)
  simpa only [actualFullNoetherVariation,sub_neg_eq_add,Function.comp_def,Pi.mul_apply,Pi.add_apply,
    Pi.neg_apply] using! generated

end LowEnergy.GaussComposite.PhysicalN3CausalWindow
