import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationActualBackgroundEvolution
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNearFieldTime
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent
open PreparationVacuumPhysicalTailPrice PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
open SourcePropagationSpectralAxis SourcePropagationFieldFeedback
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ TransferOp:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedSpace ℝ TransferOp:=ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ TransferOp:=by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=TransferOp)) using 1
local instance : ContinuousSMul ℝ TransferOp:=by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=TransferOp)) using 1
local instance : ContinuousENorm TransferOp:=by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=TransferOp)) using 1
local instance : AddCommGroup TransferOp:=ContinuousLinearMap.addCommGroup
local instance : IsTopologicalAddGroup TransferOp:=by
  have normal : @IsTopologicalAddGroup TransferOp
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddGroup:=inferInstance
  convert! normal using 1
local instance : IsTopologicalRing TransferOp:=by
  convert! (NonUnitalSeminormedRing.toIsTopologicalRing (α:=TransferOp)) using 1
local instance : NormSMulClass ℂ TransferOp:=by
  convert! (NormedSpace.toNormSMulClass (𝕜:=ℂ) (E:=TransferOp)) using 1
local instance : IsScalarTower ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  rfl⟩
local instance : SMulCommClass ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  exact (map_smul A c (B X)).symm⟩

open MeasureTheory Set Filter PreparationVacuumGaugeSourceInjection
open scoped Topology Interval
attribute [local irreducible] physicalBackgroundMap physicalBudget fieldEvolution

section Gronwall
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

private theorem volterra_growth (U0 U1 : ℝ→R) (D : R) (M eta : ℝ)
    (continuous0 : Continuous U0) (continuous1 : Continuous U1) (nonnegative : 0≤M)
    (base : ∀t : ℝ,0≤t→‖U0 t‖≤M*Real.exp (eta*t))
    (volterra : ∀t : ℝ,0≤t→U1 t=U0 t+∫s in (0:ℝ)..t,U0 (t-s)*D*U1 s)
    (t : ℝ) (future : 0≤t) : ‖U1 t‖≤M*Real.exp ((eta+M*‖D‖)*t) :=by
  let w:=fun s : ℝ=>Real.exp (-eta*s)*‖U1 s‖
  let B:=fun r : ℝ=>M+M*‖D‖*∫s in (0:ℝ)..r,w s
  have wc : Continuous w:=(Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous1.norm
  have scaled (r : ℝ) (futureR : 0≤r) : w r≤B r:=by
    have term : Continuous (fun s : ℝ=>U0 (r-s)*D*U1 s):=
      ((continuous0.comp (continuous_const.sub continuous_id)).mul continuous_const).mul continuous1
    have envelope : Continuous (fun s : ℝ=>M*Real.exp (eta*(r-s))*‖D‖*‖U1 s‖):=by fun_prop
    have bound (s : ℝ) (inside : s∈Icc (0:ℝ) r) :
        ‖U0 (r-s)*D*U1 s‖≤M*Real.exp (eta*(r-s))*‖D‖*‖U1 s‖:=by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (base (r-s) (by linarith [inside.2])) (norm_nonneg D))) (norm_nonneg _))
    have boundIntegral:=(intervalIntegral.norm_integral_le_integral_norm (μ:=volume) futureR).trans
      (intervalIntegral.integral_mono_on futureR (term.norm.intervalIntegrable _ _) (envelope.intervalIntegrable _ _) bound)
    have equal : (∫s in (0:ℝ)..r,M*Real.exp (eta*(r-s))*‖D‖*‖U1 s‖)=
        Real.exp (eta*r)*(M*‖D‖*(∫s in (0:ℝ)..r,w s)):=by
      have point (s : ℝ) : M*Real.exp (eta*(r-s))*‖D‖*‖U1 s‖=
          (Real.exp (eta*r)*(M*‖D‖))*w s:=by
        have exponent : eta*(r-s)=eta*r+(-eta*s):=by ring
        rw [exponent,Real.exp_add]
        dsimp only [w]
        ring
      rw [intervalIntegral.integral_congr (fun s _=>point s),intervalIntegral.integral_const_mul]
      ring
    have normBound : ‖U1 r‖≤Real.exp (eta*r)*B r:=by
      calc
        _=‖U0 r+∫s in (0:ℝ)..r,U0 (r-s)*D*U1 s‖:=by rw [←volterra r futureR]
        _≤‖U0 r‖+‖∫s in (0:ℝ)..r,U0 (r-s)*D*U1 s‖:=norm_add_le _ _
        _≤M*Real.exp (eta*r)+Real.exp (eta*r)*(M*‖D‖*(∫s in (0:ℝ)..r,w s)):=
          add_le_add (base r futureR) (boundIntegral.trans_eq equal)
        _=Real.exp (eta*r)*B r:=by dsimp only [B];ring
    have weight : Real.exp (-eta*r)*Real.exp (eta*r)=1:=by
      rw [←Real.exp_add,show -eta*r+eta*r=0 by ring,Real.exp_zero]
    exact (mul_le_mul_of_nonneg_left normBound (Real.exp_pos _).le).trans_eq (by rw [←mul_assoc,weight,one_mul])
  have derivative (r : ℝ) : HasDerivAt B (M*‖D‖*w r) r:=by
    have integral:=intervalIntegral.integral_hasDerivAt_right (wc.intervalIntegrable (0:ℝ) r)
      wc.aestronglyMeasurable.stronglyMeasurableAtFilter wc.continuousAt
    exact (integral.const_mul (M*‖D‖)).const_add M
  have bc : Continuous B:=continuous_iff_continuousAt.mpr (fun r=>(derivative r).continuousAt)
  have rightJet (s : ℝ) (_ : s∈Ico (0:ℝ) t) :
      HasDerivWithinAt B (M*‖D‖*w s) (Ici s) s:=(derivative s).hasDerivWithinAt
  have initial : ‖B 0‖≤M:=by simp only [B,intervalIntegral.integral_same,mul_zero,add_zero,Real.norm_eq_abs,abs_of_nonneg nonnegative];rfl
  have rate (s : ℝ) (inside : s∈Ico (0:ℝ) t) :
      ‖M*‖D‖*w s‖≤(M*‖D‖)*‖B s‖+0:=by
    have wpos : 0≤w s:=mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    have bpos : 0≤B s:=wpos.trans (scaled s inside.1)
    simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg nonnegative (norm_nonneg D)) wpos),abs_of_nonneg bpos,add_zero]
    exact mul_le_mul_of_nonneg_left (scaled s inside.1) (mul_nonneg nonnegative (norm_nonneg D))
  have gronwall:=norm_le_gronwallBound_of_norm_deriv_right_le bc.continuousOn rightJet initial rate t ⟨future,le_rfl⟩
  have budget : B t≤M*Real.exp ((M*‖D‖)*t):=by
    exact (le_abs_self (B t)).trans (by simpa only [sub_zero,gronwallBound_ε0,Real.norm_eq_abs] using gronwall)
  have combine : Real.exp (eta*t)*Real.exp ((M*‖D‖)*t)=Real.exp ((eta+M*‖D‖)*t):=by
    rw [←Real.exp_add];congr 1;ring
  have unweight : ‖U1 t‖=Real.exp (eta*t)*w t:=by
    dsimp only [w]
    rw [←mul_assoc,←Real.exp_add]
    have cancel : eta*t+(-eta*t)=0:=by ring
    rw [cancel,Real.exp_zero,one_mul]
  rw [unweight]
  exact (mul_le_mul_of_nonneg_left ((scaled t future).trans budget) (Real.exp_pos _).le).trans_eq (by calc
    _=M*(Real.exp (eta*t)*Real.exp ((M*‖D‖)*t)):=by ring
    _=_:=by rw [combine])

end Gronwall

def sourceDeviation (q : PhysicalResponsePoint) (h : Field289) : ℝ:=‖fieldEvolution q h-fieldEvolution q 0‖

def sourceRate (q : PhysicalResponsePoint) (eta : ℝ) (h : Field289) : ℝ:=
  eta+physicalBudget q eta*sourceDeviation q h

theorem physicalBackgroundMap_continuous (q : PhysicalResponsePoint) (h : Field289) :
    Continuous (physicalBackgroundMap q h) :=by
  have normal : ∀t,@HasDerivAt ℝ _ TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ TransferOp).toModule
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : ContinuousSMul ℝ TransferOp) (physicalBackgroundMap q h)
      (fieldEvolution q h*physicalBackgroundMap q h t) t:=by
    intro t
    convert! physicalBackgroundMap_derivative q h t using 1
  convert! continuous_iff_continuousAt.mpr (fun t=>(normal t).continuousAt) using 1

theorem physicalBackgroundMap_growth (q : PhysicalResponsePoint) (h : Field289) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖physicalBackgroundMap q h t‖≤physicalBudget q eta*Real.exp (sourceRate q eta h*t) :=by
  have generated:=volterra_growth (R:=TransferOp) (physicalBackgroundMap q 0) (physicalBackgroundMap q h)
    (fieldEvolution q h-fieldEvolution q 0) (physicalBudget q eta) eta
    (physicalBackgroundMap_continuous q 0) (physicalBackgroundMap_continuous q h)
    (physicalBudget_nonnegative q eta positive) (fun s hs=>physicalBackgroundMap_base_bound q eta s positive hs)
    (fun s _=>physicalBackgroundMap_volterra q h s) t future
  convert! generated using 1

theorem sourceRate_near (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    ∀ᶠh : Field289 in 𝓝 0,sourceRate q (lambda.re/4) h<lambda.re/2 :=by
  have zero : sourceDeviation q 0=0:=by
    unfold sourceDeviation
    rw [sub_self]
    convert! (@norm_zero TransferOp (inferInstance : SeminormedAddGroup TransferOp)) using 1
  have continuous : ContinuousAt (sourceDeviation q) 0:=by
    have normal : @ContinuousAt Field289 TransferOp
        (inferInstance : PseudoMetricSpace Field289).toUniformSpace.toTopologicalSpace
        (inferInstance : SeminormedAddGroup TransferOp).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (fun h : Field289=>fieldEvolution q h-fieldEvolution q 0) 0:=by
      convert! (fieldEvolution_C2 q).continuousAt.sub (continuousAt_const : ContinuousAt (fun _ : Field289=>fieldEvolution q 0) 0) using 1
    convert! normal.norm using 1
  have rate : ContinuousAt (sourceRate q (lambda.re/4)) 0:=continuousAt_const.add (continuousAt_const.mul continuous)
  have base : sourceRate q (lambda.re/4) 0=lambda.re/4:=by rw [sourceRate,zero,mul_zero,add_zero]
  exact rate.eventually (gt_mem_nhds (show sourceRate q (lambda.re/4) 0<lambda.re/2 by rw [base];linarith))

private theorem weight_jet (lambda : ℂ) (t : ℝ) :
    HasDerivAt (laplaceWeight lambda) (-lambda*laplaceWeight lambda t) t :=by
  unfold laplaceWeight
  convert! (((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.const_mul (-lambda)).cexp) using 1
  simp [Complex.ofRealCLM]
  ring



private theorem actual_half_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (L : E→L[ℂ] E) (f : ℝ→E) (lambda : ℂ)
    (fi : IntegrableOn (fun t=>laplaceWeight lambda t • f t) (Ioi (0:ℝ)))
    (terminal : Tendsto (fun t=>laplaceWeight lambda t • f t) atTop (𝓝 0))
    (ode : ∀t,HasDerivAt f (L (f t)) t) :
    lambda • (∫t in Ioi (0:ℝ),laplaceWeight lambda t • f t)-
      L (∫t in Ioi (0:ℝ),laplaceWeight lambda t • f t)=f 0 :=by
  let B : E→L[ℂ] E:=L-lambda • ContinuousLinearMap.id ℂ E
  have derivative (t : ℝ) : HasDerivAt (fun s=>laplaceWeight lambda s • f s)
      (B (laplaceWeight lambda t • f t)) t:=by
    have h:=(weight_jet lambda t).smul (ode t)
    convert! h using 1
    dsimp only [B]
    rw [sub_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_smul,neg_mul,neg_smul]
    abel
  have bi : IntegrableOn (fun t=>B (laplaceWeight lambda t • f t)) (Ioi (0:ℝ)):=B.integrable_comp fi
  have total:=integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _=>derivative t) bi terminal
  rw [B.integral_comp_comm fi] at total
  have atzero : laplaceWeight lambda 0=1:=by simp [laplaceWeight]
  simp only [B,sub_apply,smul_apply,ContinuousLinearMap.id_apply,atzero,one_smul,zero_sub] at total
  calc
    _=-(L (∫t in Ioi (0:ℝ),laplaceWeight lambda t • f t)-
      lambda • (∫t in Ioi (0:ℝ),laplaceWeight lambda t • f t)):=by abel
    _=_:=by rw [total,neg_neg]

/-- The observation domain is generated near the original source by its actual field continuity. -/
def timeDomain (q : PhysicalResponsePoint) (lambda : ℂ) : Set Field289:=
  {h | sourceRate q (lambda.re/4) h<lambda.re/2}

theorem timeDomain_source_near (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    ∀ᶠh : Field289 in 𝓝 0,h∈timeDomain q lambda:=sourceRate_near q lambda positive

theorem physicalBackgroundMap_damped_bound (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (h : Field289) (inside : h∈timeDomain q lambda) (t : ℝ) (future : 0≤t) :
    ‖laplaceWeight lambda t • physicalBackgroundMap q h t‖≤
      physicalBudget q (lambda.re/4)*Real.exp (-(lambda.re/2)*t) :=by
  have bound:=physicalBackgroundMap_growth q h (lambda.re/4) t (by positivity) future
  have price:=physicalBudget_nonnegative q (lambda.re/4) (by positivity)
  have rate : sourceRate q (lambda.re/4) h≤lambda.re/2:=inside.le
  have weightedNorm : ‖laplaceWeight lambda t • physicalBackgroundMap q h t‖=
      Real.exp (-lambda.re*t)*‖physicalBackgroundMap q h t‖:=by
    convert! (norm_smul (laplaceWeight lambda t) (physicalBackgroundMap q h t)) using 1
    exact (congrArg (fun a : ℝ=>a*‖physicalBackgroundMap q h t‖) (laplace_norm lambda t)).symm
  rw [weightedNorm]
  calc
    _≤Real.exp (-lambda.re*t)*(physicalBudget q (lambda.re/4)*Real.exp (sourceRate q (lambda.re/4) h*t)):=
      mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le
    _=physicalBudget q (lambda.re/4)*Real.exp ((-lambda.re+sourceRate q (lambda.re/4) h)*t):=by
      calc
        _=physicalBudget q (lambda.re/4)*(Real.exp (-lambda.re*t)*Real.exp (sourceRate q (lambda.re/4) h*t)):=by ring
        _=_:=by rw [←Real.exp_add];congr 2;ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) price

theorem physicalBackgroundMap_integrable (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (h : Field289) (inside : h∈timeDomain q lambda) :
    IntegrableOn (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t) (Ioi (0:ℝ)) :=by
  have majorant : IntegrableOn (fun t : ℝ=>physicalBudget q (lambda.re/4)*Real.exp (-(lambda.re/2)*t)) (Ioi (0:ℝ)):=
    (integrableOn_exp_mul_Ioi (by linarith) (0:ℝ)).const_mul _
  have continuity : Continuous (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t):=by
    have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
    exact weight.smul (physicalBackgroundMap_continuous q h)
  have normal : @Continuous ℝ TransferOp inferInstance
      (inferInstance : NormedAddCommGroup TransferOp).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t):=by
    convert! continuity using 1
  have bounded : ∀ᵐt ∂volume.restrict (Ioi (0:ℝ)),
      ‖laplaceWeight lambda t • physicalBackgroundMap q h t‖≤physicalBudget q (lambda.re/4)*Real.exp (-(lambda.re/2)*t):=
    (ae_restrict_mem measurableSet_Ioi).mono (fun t ht=>physicalBackgroundMap_damped_bound q lambda positive h inside t ht.le)
  have generated : IntegrableOn (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t) (Ioi (0:ℝ)):=by
    have measurable :=normal.aestronglyMeasurable (μ:=volume) |>.restrict (s:=Ioi (0:ℝ))
    have normalMeasurable : AEStronglyMeasurable (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t)
        (volume.restrict (Ioi (0:ℝ))):=by convert! measurable using 1
    have paid:=Integrable.mono' (β:=TransferOp) (f:=fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t)
      majorant normalMeasurable (by convert! bounded using 1)
    unfold IntegrableOn
    convert! paid using 1
  exact generated

theorem physicalBackgroundMap_terminal (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (h : Field289) (inside : h∈timeDomain q lambda) :
    Tendsto (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t) atTop (𝓝 0) :=by
  have normLimit : Tendsto (fun t=>‖laplaceWeight lambda t • physicalBackgroundMap q h t‖) atTop (𝓝 (0:ℝ)):=by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun t=>show (0:ℝ)≤‖laplaceWeight lambda t • physicalBackgroundMap q h t‖ from by convert! norm_nonneg (laplaceWeight lambda t • physicalBackgroundMap q h t) using 1))
      (eventually_ge_atTop (0:ℝ) |>.mono (fun t ht=>physicalBackgroundMap_damped_bound q lambda positive h inside t ht))
    have decay : Tendsto (fun t : ℝ=>Real.exp (-(lambda.re/2)*t)) atTop (𝓝 (0:ℝ)):=by
      simpa only [Real.rpow_zero,one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (lambda.re/2) (by positivity)
    convert! decay.const_mul (physicalBudget q (lambda.re/4)) using 1
    simp
  have normal : Tendsto (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t) atTop
      (@nhds TransferOp (inferInstance : SeminormedAddGroup TransferOp).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (inferInstance : SeminormedAddGroup TransferOp).toAddGroup.toAddMonoid.toAddZeroClass.toZero.zero):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert! normLimit using 1
  convert! normal using 1

/-- Actual physical time, before any operator inverse is read. -/
def nearTimeHalf (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) : TransferOp:=
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t • physicalBackgroundMap q h t

attribute [local irreducible] nearTimeHalf fieldPencil fieldInverse

private theorem pencil_algebra {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    (lambda : ℂ) (L A : R) : (lambda • 1-L)*A=lambda • A-L*A:=by
  rw [sub_mul,smul_mul_assoc,one_mul]

theorem nearTimeHalf_pencil (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (h : Field289) (inside : h∈timeDomain q lambda) :
    fieldPencil q lambda h*nearTimeHalf q lambda h=1 :=by
  have integral:=physicalBackgroundMap_integrable q lambda positive h inside
  have terminal:=physicalBackgroundMap_terminal q lambda positive h inside
  have ode (t : ℝ) : HasDerivAt (physicalBackgroundMap q h)
      ((ContinuousLinearMap.mul ℂ TransferOp (fieldEvolution q h)) (physicalBackgroundMap q h t)) t:=by
    convert! physicalBackgroundMap_derivative q h t using 1
  have paid : lambda • (∫t in Ioi (0:ℝ),laplaceWeight lambda t • physicalBackgroundMap q h t)-
      (ContinuousLinearMap.mul ℂ TransferOp (fieldEvolution q h))
        (∫t in Ioi (0:ℝ),laplaceWeight lambda t • physicalBackgroundMap q h t)=physicalBackgroundMap q h 0:=by
    apply actual_half_ode (E:=TransferOp) _ _ lambda
    · convert! integral using 1
    · convert! terminal using 1
    · intro t
      convert! ode t using 1
  simp only [ContinuousLinearMap.mul_apply',physicalBackgroundMap_initial] at paid
  have value : (∫t in Ioi (0:ℝ),laplaceWeight lambda t • physicalBackgroundMap q h t)=nearTimeHalf q lambda h:=by unfold nearTimeHalf;rfl
  have folded : lambda • nearTimeHalf q lambda h-fieldEvolution q h*nearTimeHalf q lambda h=(1:TransferOp):=by
    convert! paid using 1
    exact congrArg (fun A : TransferOp=>lambda • A-fieldEvolution q h*A) value.symm
  have algebra : fieldPencil q lambda h*nearTimeHalf q lambda h=
      lambda • nearTimeHalf q lambda h-fieldEvolution q h*nearTimeHalf q lambda h:=by
    unfold fieldPencil
    convert! pencil_algebra (R:=TransferOp) lambda (fieldEvolution q h) (nearTimeHalf q lambda h) using 1
  exact algebra.trans folded

theorem nearTimeHalf_inverse_generated (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    ∀ᶠh : Field289 in 𝓝 0,nearTimeHalf q lambda h=fieldInverse q lambda h :=by
  filter_upwards [timeDomain_source_near q lambda positive,fieldInverse_right_generated q lambda (ne_of_gt positive)] with h inside right
  have left:=nearTimeHalf_pencil q lambda positive h inside
  exact (left_inv_eq_right_inv right left).symm

end LowEnergy.SourcePropagationNearFieldTime
