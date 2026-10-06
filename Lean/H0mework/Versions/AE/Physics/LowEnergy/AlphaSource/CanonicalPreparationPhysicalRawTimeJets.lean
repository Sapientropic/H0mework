import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawJointFiveTerms
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldTransferDerivative

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumSourcePreparedResponse
open PreparationVacuumFieldConstraintResponse PreparationVacuumFullFieldRiesz PreparationVacuumActionFieldLift
open CanonicalPreparationCore.Completed GaussComposite GaussComposite.SourceGraph
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix
abbrev Index:=GaussUnitaryHistory.Index
abbrev Op:=H→L[ℂ] H
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointGenerator jointCurrent jointResolvent rawReader rawReaderContact

def addJet (a b : SourceJet Op) : SourceJet Op :=
  ⟨a.value+b.value,a.first+b.first,a.second+b.second⟩

theorem productJets (a b : ℝ→SourceJet Op) (r : ℝ)
    (ha : HasSourceJets a r) (hb : HasSourceJets b r) :
    HasSourceJets (fun t=>jetMul (a t) (b t)) r :=
  ⟨ha.1.mul hb.1,(ha.2.mul hb.1).add (ha.1.mul hb.2)⟩

theorem constantJets (A : Op) (r : ℝ) : HasSourceJets (fun _=>jetConst A) r :=
  ⟨hasDerivAt_const r A,hasDerivAt_const r 0⟩

theorem sumJets (a b : ℝ→SourceJet Op) (r : ℝ)
    (ha : HasSourceJets a r) (hb : HasSourceJets b r) :
    HasSourceJets (fun t=>addJet (a t) (b t)) r :=⟨ha.1.add hb.1,ha.2.add hb.2⟩

theorem timeJets_generated (C : Op) (rate shift r : ℝ) :
    HasSourceJets (timeJet C rate shift) r :=by
  have path : HasDerivAt (fun t : ℝ=>rate*t+shift) rate r :=by
    convert! ((hasDerivAt_id r).const_mul rate).add_const shift using 1
    simp
  have ht:=(hasDerivAt_exp_smul_const ((-Complex.I) • C) (rate*r+shift)).scomp r path
  exact ⟨ht,(ht.mul_const ((-Complex.I) • C)).const_smul rate⟩

def variationJet (C B : Op) (rate shift r : ℝ) : SourceJet Op :=
  let V:=CanonicalGradedVariation.variation C B (rate*r+shift)
  let G:=(-Complex.I) • C
  let K:=(-Complex.I) • B
  let T:=timeJet C rate shift r
  let first:=rate • (V*G+T.value*K)
  ⟨V,first,rate • (first*G+T.first*K)⟩

theorem variation_ode (C B : Op) (t : ℝ) :
    HasDerivAt (CanonicalGradedVariation.variation C B)
      (CanonicalGradedVariation.variation C B t*((-Complex.I) • C)+
        SourceFiniteUnitary.time C t*((-Complex.I) • B)) t :=by
  have same : PreparationVacuumFieldPerturbation.Blocks.crossTime C C B=
      CanonicalGradedVariation.variation C B :=by
    funext s
    rw [PreparationVacuumFieldPerturbation.Blocks.crossTime_integral]
    simp only [CanonicalGradedVariation.variation,CanonicalGradedVariation.variationBetween,
      zero_smul,add_zero]
  simpa only [same] using PreparationVacuumFieldPerturbation.Blocks.crossTime_derivative C C B t

theorem variationJets_generated (C B : Op) (rate shift r : ℝ) :
    HasSourceJets (variationJet C B rate shift) r :=by
  have path : HasDerivAt (fun t : ℝ=>rate*t+shift) rate r :=by
    convert! ((hasDerivAt_id r).const_mul rate).add_const shift using 1
    simp
  have hv:=(variation_ode C B (rate*r+shift)).scomp r path
  have ht:=(timeJets_generated C rate shift r).1
  exact ⟨hv,((hv.mul_const ((-Complex.I) • C)).add (ht.mul_const ((-Complex.I) • B))).const_smul rate⟩

def physicalTimeJet (p : PhysicalMomentum) (F : Index) (h : Field289)
    (rate shift r : ℝ) : SourceJet Op :=timeJet (jointGenerator p F 0 h) rate shift r

def physicalSlopeJet (force : Field289) (p : PhysicalMomentum) (F : Index)
    (rate shift r : ℝ) : SourceJet Op :=
  variationJet (jointGenerator p F 0 0) (jointCurrent p F 0 0 force) rate shift r

theorem physicalTimeJet_generated (p : PhysicalMomentum) (F : Index) (h : Field289)
    (rate shift r : ℝ) : HasSourceJets (physicalTimeJet p F h rate shift) r :=
  timeJets_generated _ _ _ _

theorem physicalSlopeJet_generated (force : Field289) (p : PhysicalMomentum) (F : Index)
    (rate shift r : ℝ) : HasSourceJets (physicalSlopeJet force p F rate shift) r :=
  variationJets_generated _ _ _ _ _

def rawKernelJet (reader : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ)
    (h : Field289) (r : ℝ) : SourceJet Op :=
  jetMul (jetMul (jetMul (jetMul (physicalTimeJet (p+k) F h (-1) 0 r)
    (jetConst (jointResolvent (p+k) F z h))) (jetConst (rawReader reader p F h)))
      (jetConst (jointResolvent p F w h))) (physicalTimeJet p F h 1 0 r)

theorem rawKernelJet_generated (reader : Field289) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) (h : Field289) (r : ℝ) :
    HasSourceJets (rawKernelJet reader p k F z w h) r :=
  productJets _ _ r (productJets _ _ r (productJets _ _ r (productJets _ _ r
    (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _)) (constantJets _ _))
      (constantJets _ _)) (physicalTimeJet_generated _ _ _ _ _ _)

theorem rawKernelJet_value (reader : Field289) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) (h : Field289) (r : ℝ) :
    (rawKernelJet reader p k F z w h r).value=fiveKernel reader p k F z w r h :=by
  simp only [rawKernelJet,jetMul,jetConst,physicalTimeJet,timeJet,fiveKernel,physicalTime,
    neg_one_mul,add_zero,one_mul]

def slopeKernelJet (reader force : Field289) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) (r : ℝ) : SourceJet Op :=
  let TL:=physicalTimeJet (p+k) F 0 (-1) 0 r
  let TR:=physicalTimeJet p F 0 1 0 r
  let VL:=physicalSlopeJet force (p+k) F (-1) 0 r
  let VR:=physicalSlopeJet force p F 1 0 r
  let L:=jetConst (jointResolvent (p+k) F z 0)
  let R:=jetConst (jointResolvent p F w 0)
  let A:=jetConst (rawReader reader p F 0)
  let DL:=jetConst (-(jointResolvent (p+k) F z 0*jointCurrent (p+k) F z 0 force*jointResolvent (p+k) F z 0))
  let DR:=jetConst (-(jointResolvent p F w 0*jointCurrent p F w 0 force*jointResolvent p F w 0))
  let DA:=jetConst (rawReaderContact reader force p F)
  addJet (addJet (addJet (addJet
    (jetMul (jetMul (jetMul (jetMul VL L) A) R) TR)
    (jetMul (jetMul (jetMul (jetMul TL DL) A) R) TR))
    (jetMul (jetMul (jetMul (jetMul TL L) DA) R) TR))
    (jetMul (jetMul (jetMul (jetMul TL L) A) DR) TR))
    (jetMul (jetMul (jetMul (jetMul TL L) A) R) VR)

theorem slopeKernelJet_generated (reader force : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (r : ℝ) :
    HasSourceJets (slopeKernelJet reader force p k F z w) r :=by
  unfold slopeKernelJet
  apply sumJets
  · apply sumJets
    · apply sumJets
      · apply sumJets
        · exact productJets _ _ r (productJets _ _ r (productJets _ _ r (productJets _ _ r
            (physicalSlopeJet_generated _ _ _ _ _ _) (constantJets _ _)) (constantJets _ _))
              (constantJets _ _)) (physicalTimeJet_generated _ _ _ _ _ _)
        · exact productJets _ _ r (productJets _ _ r (productJets _ _ r (productJets _ _ r
            (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _)) (constantJets _ _))
              (constantJets _ _)) (physicalTimeJet_generated _ _ _ _ _ _)
      · exact productJets _ _ r (productJets _ _ r (productJets _ _ r (productJets _ _ r
          (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _)) (constantJets _ _))
            (constantJets _ _)) (physicalTimeJet_generated _ _ _ _ _ _)
    · exact productJets _ _ r (productJets _ _ r (productJets _ _ r (productJets _ _ r
        (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _)) (constantJets _ _))
          (constantJets _ _)) (physicalTimeJet_generated _ _ _ _ _ _)
  · exact productJets _ _ r (productJets _ _ r (productJets _ _ r (productJets _ _ r
      (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _)) (constantJets _ _))
        (constantJets _ _)) (physicalSlopeJet_generated _ _ _ _ _ _)

theorem slopeKernelJet_value (reader force : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (r : ℝ) :
    (slopeKernelJet reader force p k F z w r).value=fiveDerivative reader force p k F z w r :=by
  simp only [slopeKernelJet,addJet,jetMul,jetConst,physicalTimeJet,timeJet,physicalSlopeJet,
    variationJet,fiveDerivative,physicalTime,timeSlope,neg_one_mul,add_zero,one_mul]

def pairJet (x y : H) (j : SourceJet Op) : SourceJet ℂ :=
  ⟨inner ℂ x (j.value y),inner ℂ x (j.first y),inner ℂ x (j.second y)⟩

theorem pairJets_generated (x y : H) (j : ℝ→SourceJet Op) (r : ℝ)
    (hj : HasSourceJets j r) : HasSourceJets (fun t=>pairJet x y (j t)) r :=
  ⟨paired_derivative hj.1 x y,paired_derivative hj.2 x y⟩

def negativeJet (j : SourceJet ℂ) : SourceJet ℂ :=⟨-j.value,-j.first,-j.second⟩

theorem negativeJets_generated (j : ℝ→SourceJet ℂ) (r : ℝ) (hj : HasSourceJets j r) :
    HasSourceJets (fun t=>negativeJet (j t)) r :=⟨hj.1.neg,hj.2.neg⟩

structure PhysicalResponsePoint where
  epsilon : ℝ
  precision : 0<epsilon
  p : PhysicalMomentum
  k : PhysicalMomentum
  F : Index
  z : ℂ
  w : ℂ
  left : Bool
  right : Bool
  lc : Fin 2
  ls : Fin 2
  rc : Fin 2
  rs : Fin 2

def responseLeft (q : PhysicalResponsePoint) : H:=
  completedLeg q.left q.lc q.ls (sourceProfile q.epsilon q.precision)

def responseRight (q : PhysicalResponsePoint) : H:=
  completedLeg q.right q.rc q.rs (sourceProfile q.epsilon q.precision)

/-- The Euler minus is inserted here once, before the original field Green. -/
def sourceJet (q : PhysicalResponsePoint) (h : Field289) (r : ℝ) (i : Fin 289) : SourceJet ℂ:=
  negativeJet (pairJet (responseLeft q) (responseRight q)
    (rawKernelJet (fieldUnit i) q.p q.k q.F q.z q.w h r))

def sourceSlopeJet (q : PhysicalResponsePoint) (force : Field289) (r : ℝ) (i : Fin 289) : SourceJet ℂ:=
  negativeJet (pairJet (responseLeft q) (responseRight q)
    (slopeKernelJet (fieldUnit i) force q.p q.k q.F q.z q.w r))

theorem sourceJet_generated (q : PhysicalResponsePoint) (h : Field289) (r : ℝ) (i : Fin 289) :
    HasSourceJets (fun t=>sourceJet q h t i) r :=
  negativeJets_generated _ _ (pairJets_generated _ _ _ _ (rawKernelJet_generated _ _ _ _ _ _ _ _))

theorem sourceSlopeJet_generated (q : PhysicalResponsePoint) (force : Field289) (r : ℝ) (i : Fin 289) :
    HasSourceJets (fun t=>sourceSlopeJet q force t i) r :=
  negativeJets_generated _ _ (pairJets_generated _ _ _ _ (slopeKernelJet_generated _ _ _ _ _ _ _ _))

theorem sourceJet_value (q : PhysicalResponsePoint) (h : Field289) (r : ℝ) (i : Fin 289) :
    (sourceJet q h r i).value=eulerCovector q.epsilon q.precision q.p q.k q.F q.z q.w r
      q.left q.right q.lc q.ls q.rc q.rs h i :=by
  simp only [sourceJet,negativeJet,pairJet,rawKernelJet_value,responseLeft,responseRight,eulerCovector,rawPrepared]

theorem sourceSlopeJet_value (q : PhysicalResponsePoint) (force : Field289) (r : ℝ) (i : Fin 289) :
    (sourceSlopeJet q force r i).value=eulerCovectorSlope q.epsilon q.precision force q.p q.k q.F q.z q.w r
      q.left q.right q.lc q.ls q.rc q.rs i :=by
  simp only [sourceSlopeJet,negativeJet,pairJet,slopeKernelJet_value,responseLeft,responseRight,eulerCovectorSlope,rawPreparedSlope]

end LowEnergy.PreparationVacuumPhysicalFeedback
