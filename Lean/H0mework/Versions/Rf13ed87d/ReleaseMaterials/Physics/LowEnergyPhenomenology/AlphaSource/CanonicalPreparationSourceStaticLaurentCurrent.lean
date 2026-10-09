import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticObservedField

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticSimpleCoupling
open PreparationVacuumObservedPoleTensor PreparationVacuumObservedStaticResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumQuantumSlowResidue
open PreparationVacuumQuantumSlowResponse PreparationVacuumPhysicalSlowBlock
open PreparationVacuumPhysicalPinnedVelocity PreparationVacuumGaugeSlowFrequency
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumElectromagneticIdentity CanonicalGradedSpatialSource
open Filter Set
open scoped Topology
attribute [local irreducible] sourceEqualProjection sourceRetainerReturn sourceFullInitialUpper
  sourceFullInitialBase sourcePinnedResolvent sourcePoleRead sourceBaseResidue sourceUpperResidue
  sourceStaticBase sourceStaticCurrent

/-- Both mixed resonant/off-resonant retainer returns belong to the actual simple static coefficient. -/
def sourceBaseCross (q : PhysicalResponsePoint) (n : PhysicalMomentum) (eta : ℝ) (i : Fin 289) : SourceOp :=
  -(sourceOffPoleReturn q.F n 0 eta*sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourceResonanceProjection q.F n 0*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))))-
    sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourceOffPoleReturn q.F n 0 eta*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))

def sourceBaseRegular (q : PhysicalResponsePoint) (n : PhysicalMomentum) (eta : ℝ) (i : Fin 289) : SourceOp :=
  -(sourceOffPoleReturn q.F n 0 eta*sourceEqualProjection q.F
    (sourceRetainerReturn q.F (sourceOffPoleReturn q.F n 0 eta*
      sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))))

attribute [local irreducible] sourceBaseCross sourceBaseRegular

private theorem boundary_base (q : PhysicalResponsePoint) (n : PhysicalMomentum) (eta : ℝ)
    (positive : 0<eta) (i : Fin 289) :
    sourceBaseResidue q n (eta:ℂ) i=
      -(((eta:ℂ)⁻¹ • sourceResonanceProjection q.F n 0+sourceOffPoleReturn q.F n 0 eta)*
        sourceEqualProjection q.F (sourceRetainerReturn q.F
          (((eta:ℂ)⁻¹ • sourceResonanceProjection q.F n 0+sourceOffPoleReturn q.F n 0 eta)*
            sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))) := by
  simpa only [sourcePoleSide,Complex.ofReal_zero,mul_zero,add_zero] using
    sourceActual_base_boundary q n 0 eta positive i

/-- Exact Laurent decomposition of the complete original base, before taking any static limit. -/
theorem sourceBase_static_decomposition (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (eta : ℝ) (positive : 0<eta) (i : Fin 289) :
    sourceBaseResidue q n (eta:ℂ) i=
      ((eta:ℂ)⁻¹)^2 • sourceStaticBase q n i+
        (eta:ℂ)⁻¹ • sourceBaseCross q n eta i+sourceBaseRegular q n eta i := by
  rw [boundary_base q n eta positive i]
  simp only [sourceStaticBase,sourceBaseCross,sourceBaseRegular,add_mul,mul_add,
    smul_mul_assoc,mul_smul_comm,map_add,map_smul,smul_neg,smul_sub,pow_two]
  module

private theorem current_cross_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) :
    Tendsto (fun eta=>sourceBaseCross q n eta i) (𝓝 0) (𝓝 (sourceBaseCross q n 0 i)) := by
  have off:=sourceOffPoleReturn_limit q.F n 0
  have initial:=(off.mul_const (sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))
  have second:=(sourceEqualProjection q.F).continuous.continuousAt.tendsto.comp
    ((sourceRetainerReturn q.F).continuous.continuousAt.tendsto.comp initial)
  simpa only [sourceBaseCross,Function.comp_def] using (off.mul_const _).neg.sub (second.const_mul _)

private theorem current_regular_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) :
    Tendsto (fun eta=>sourceBaseRegular q n eta i) (𝓝 0) (𝓝 (sourceBaseRegular q n 0 i)) := by
  have off:=sourceOffPoleReturn_limit q.F n 0
  have initial:=off.mul_const (sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))
  have projected:=(sourceEqualProjection q.F).continuous.continuousAt.tendsto.comp
    ((sourceRetainerReturn q.F).continuous.continuousAt.tendsto.comp initial)
  simpa only [sourceBaseRegular,Function.comp_def] using (off.mul projected).neg

private theorem cancel_double {E : Type*} [AddCommGroup E] [Module ℂ E]
    (z : ℂ) (nonzero : z≠0) (a b c : E) :
    z • (z⁻¹^2 • a+z⁻¹ • b+c-z⁻¹^2 • a)=b+z • c := by
  have cancel : z⁻¹^2 • a+z⁻¹ • b+c-z⁻¹^2 • a=z⁻¹ • b+c := by abel
  rw [cancel,smul_add,smul_smul,mul_inv_cancel₀ nonzero,one_smul]

/-- The actual double coefficient is subtracted explicitly; no vanishing or conservation premise is inserted. -/
theorem sourceBase_simple_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • (sourceBaseResidue q n (eta:ℂ) i-
      ((eta:ℂ)⁻¹)^2 • sourceStaticBase q n i))
      (𝓝[>] 0) (𝓝 (sourceBaseCross q n 0 i)) := by
  have scalar : Tendsto (fun eta : ℝ=>(eta:ℂ)) (𝓝 0) (𝓝 0) := Complex.continuous_ofReal.tendsto 0
  have h:=(current_cross_limit q n i).add (scalar.smul (current_regular_limit q n i))
  have zero : (0:ℂ) • sourceBaseRegular q n 0 i=0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact zero_smul ℂ _
  rw [zero,add_zero] at h
  apply (h.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)).congr'
  filter_upwards [self_mem_nhdsWithin] with eta positive
  rw [sourceBase_static_decomposition q n eta positive i]
  have nonzero : (eta:ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
  exact (cancel_double (eta:ℂ) nonzero _ _ _).symm


private theorem retained_price (P T : SourceSuperOp) (B X Y : SourceOp) :
    ‖X*P (T (Y*B))‖≤‖X‖*‖P‖*‖T‖*‖Y‖*‖B‖ := by
  calc
    _≤‖X‖*‖P (T (Y*B))‖ := norm_mul_le _ _
    _≤‖X‖*(‖P‖*‖T (Y*B)‖) := mul_le_mul_of_nonneg_left (P.le_opNorm _) (norm_nonneg _)
    _≤‖X‖*(‖P‖*(‖T‖*‖Y*B‖)) := by gcongr;exact T.le_opNorm _
    _≤‖X‖*(‖P‖*(‖T‖*(‖Y‖*‖B‖))) := by gcongr;exact norm_mul_le _ _
    _=_ := by ring

/-- A source-only reciprocal-gap price for the simple Laurent remainder. -/
def sourceBaseSimplePrice (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) : ℝ :=
  (2*‖sourceResonanceProjection q.F n 0‖*sourceOffPoleError q.F n 0+
    (sourceOffPolePrice q.F n 0)^2)*‖sourceEqualProjection q.F‖*‖sourceRetainerReturn q.F‖*
      ‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖

private theorem cross_price (q : PhysicalResponsePoint) (n : PhysicalMomentum) (eta : ℝ) (i : Fin 289) :
    ‖sourceBaseCross q n eta i-sourceBaseCross q n 0 i‖≤
      2*|eta| *sourceOffPoleError q.F n 0*‖sourceResonanceProjection q.F n 0‖*
        ‖sourceEqualProjection q.F‖*‖sourceRetainerReturn q.F‖*
          ‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖ := by
  let O:=sourceOffPoleReturn q.F n 0 eta-sourceOffPoleReturn q.F n 0 0
  let R:=sourceResonanceProjection q.F n 0
  let P:=sourceEqualProjection q.F
  let T:=sourceRetainerReturn q.F
  let B:=P (sourceFullInitialUpper q 0 0 i)
  have difference : sourceBaseCross q n eta i-sourceBaseCross q n 0 i=
      -(O*P (T (R*B)))-R*P (T (O*B)) := by
    simp only [sourceBaseCross,O,R,P,T,B,sub_mul,map_sub,mul_sub]
    abel
  have gap : ‖O‖≤|eta| *sourceOffPoleError q.F n 0 := sourceOffPoleReturn_error _ _ _ _
  rw [difference]
  calc
    _≤‖O*P (T (R*B))‖+‖R*P (T (O*B))‖ := by simpa only [norm_neg] using norm_sub_le (-(O*P (T (R*B)))) (R*P (T (O*B)))
    _≤‖O‖*‖P‖*‖T‖*‖R‖*‖B‖+‖R‖*‖P‖*‖T‖*‖O‖*‖B‖ :=
      add_le_add (retained_price P T B O R) (retained_price P T B R O)
    _≤(|eta| *sourceOffPoleError q.F n 0)*‖P‖*‖T‖*‖R‖*‖B‖+
        ‖R‖*‖P‖*‖T‖*(|eta| *sourceOffPoleError q.F n 0)*‖B‖ := by gcongr
    _=_ := by dsimp only [P,T,R,B];ring

/-- The original reciprocal-gap bounds control the new coefficient, with the actual B1 and retainer norms. -/
theorem sourceBase_simple_error (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (eta : ℝ) (positive : 0<eta) (i : Fin 289) :
    ‖(eta:ℂ) • (sourceBaseResidue q n (eta:ℂ) i-((eta:ℂ)⁻¹)^2 • sourceStaticBase q n i)-
      sourceBaseCross q n 0 i‖≤|eta| *sourceBaseSimplePrice q n i := by
  have decomposition : (eta:ℂ) • (sourceBaseResidue q n (eta:ℂ) i-((eta:ℂ)⁻¹)^2 • sourceStaticBase q n i)=
      sourceBaseCross q n eta i+(eta:ℂ) • sourceBaseRegular q n eta i := by
    rw [sourceBase_static_decomposition q n eta positive i]
    have nonzero : (eta:ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
    exact cancel_double (eta:ℂ) nonzero _ _ _
  have regular : ‖sourceBaseRegular q n eta i‖≤(sourceOffPolePrice q.F n 0)^2*
      ‖sourceEqualProjection q.F‖*‖sourceRetainerReturn q.F‖*
      ‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖ := by
    unfold sourceBaseRegular
    rw [norm_neg]
    apply (retained_price _ _ _ _ _).trans
    have off:=sourceOffPoleReturn_price q.F n 0 eta
    have nonnegative:=sourceOffPolePrice_nonneg q.F n 0
    calc
      _≤ sourceOffPolePrice q.F n 0*‖sourceEqualProjection q.F‖*‖sourceRetainerReturn q.F‖*
          sourceOffPolePrice q.F n 0*‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖ := by gcongr
      _=_ := by ring
  rw [decomposition]
  have reorder : sourceBaseCross q n eta i+(eta:ℂ) • sourceBaseRegular q n eta i-sourceBaseCross q n 0 i=
      (sourceBaseCross q n eta i-sourceBaseCross q n 0 i)+(eta:ℂ) • sourceBaseRegular q n eta i := by abel
  rw [reorder]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  apply (add_le_add (cross_price q n eta i) (mul_le_mul_of_nonneg_left regular (abs_nonneg eta))).trans_eq
  unfold sourceBaseSimplePrice
  ring

def sourceCurrentSimple (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  fun i=> -sourcePoleRead q.epsilon q.precision 0 0 l r (sourceBaseCross q n 0 i)

/-- The same actual independent-dual reader consumes every full-current simple coefficient. -/
theorem sourceCurrent_simple_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • (sourceFullCurrentResidue q n (eta:ℂ) l r-
      ((eta:ℂ)⁻¹)^2 • sourceStaticCurrent q n l r))
      (𝓝[>] 0) (𝓝 (sourceCurrentSimple q n l r)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.continuousAt.tendsto.comp
    (sourceBase_simple_generated q n i)).neg
  simpa only [Function.comp_def,sourceCurrentSimple,sourceFullCurrentResidue,sourceStaticCurrent,
    Pi.smul_apply,Pi.sub_apply,map_smul,map_sub,smul_sub,smul_neg,neg_sub,sub_neg_eq_add,neg_add_eq_sub] using h

/-- Each actual independent-leg current reader inherits the source's explicit linear error price. -/
theorem sourceCurrent_simple_error (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (eta : ℝ) (positive : 0<eta) (i : Fin 289) :
    ‖(eta:ℂ)*(sourceFullCurrentResidue q n (eta:ℂ) l r i-
      ((eta:ℂ)⁻¹)^2*sourceStaticCurrent q n l r i)-sourceCurrentSimple q n l r i‖≤
      ‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*(|eta| *sourceBaseSimplePrice q n i) := by
  have generated : (eta:ℂ)*(sourceFullCurrentResidue q n (eta:ℂ) l r i-
      ((eta:ℂ)⁻¹)^2*sourceStaticCurrent q n l r i)-sourceCurrentSimple q n l r i=
    -sourcePoleRead q.epsilon q.precision 0 0 l r
      ((eta:ℂ) • (sourceBaseResidue q n (eta:ℂ) i-((eta:ℂ)⁻¹)^2 • sourceStaticBase q n i)-sourceBaseCross q n 0 i) := by
    simp only [sourceFullCurrentResidue,sourceStaticCurrent,sourceCurrentSimple,map_sub,map_smul,smul_eq_mul]
    ring
  rw [generated,norm_neg]
  exact ((sourcePoleRead q.epsilon q.precision 0 0 l r).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (sourceBase_simple_error q n eta positive i) (norm_nonneg _))

end LowEnergy.PreparationVacuumStaticSimpleCoupling
