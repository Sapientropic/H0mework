import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGradedDensityTransport

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumGradedTransport
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair GaussDiagonalHistory
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse PreparationVacuumSourceActionJets
open PreparationVacuumMixedFieldReturn GaussNativePotential
open NativeHistoryGrade (Label projection)
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace BigOperators
local instance : Fintype Label:=Fintype.ofFinite _

abbrev Index:=GaussUnitaryHistory.Index

abbrev physicalSpan (p : PhysicalMomentum) (F : Index) : Submodule ℂ GaussCoreHilbert.H :=
  FiniteCoreEvolution.coreSpan (CanonicalPhysicalSpatial.physical p) F
abbrev PhysicalBasisIndex (p : PhysicalMomentum) (F : Index) := Fin (Module.finrank ℂ (physicalSpan p F))
def physicalBasis (p : PhysicalMomentum) (F : Index) : OrthonormalBasis (PhysicalBasisIndex p F) ℂ (physicalSpan p F) :=
  stdOrthonormalBasis ℂ (physicalSpan p F)
def physicalFrame (p : PhysicalMomentum) (F : Index) (i : Label × PhysicalBasisIndex p F) : H :=
  projection i.1 ((physicalBasis p F i.2 : physicalSpan p F) : H)

def bareTest (p : PhysicalMomentum) (F : Index) (i : PhysicalBasisIndex p F) : QuantumTest :=
  coreEquiv.symm ⟨(physicalBasis p F i).val,FiniteCoreEvolution.coreSpan_le (physical p) F (physicalBasis p F i).property⟩

def projectionTest (p : PhysicalMomentum) (F : Index) (x : H) : QuantumTest :=
  coreEquiv.symm ⟨(physicalSpan p F).starProjection x,
    FiniteCoreEvolution.coreSpan_le (physical p) F ((physicalSpan p F).orthogonalProjectionOnto x).property⟩

def gradedTest (p : PhysicalMomentum) (F : Index) (g : Label) (x : H) : QuantumTest :=projectionTest p F (projection g x)

theorem bareTest_embed (p : PhysicalMomentum) (F : Index) (i : PhysicalBasisIndex p F) : embed (bareTest p F i)=(physicalBasis p F i).val :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

theorem projectionTest_embed (p : PhysicalMomentum) (F : Index) (x : H) : embed (projectionTest p F x)=(physicalSpan p F).starProjection x :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

theorem projectionTest_frame (p : PhysicalMomentum) (F : Index) (x : H) :
    projectionTest p F x=∑i : PhysicalBasisIndex p F,inner ℂ (physicalBasis p F i).val x • bareTest p F i := by
  apply embed_injective
  rw [projectionTest_embed,map_sum]
  simp only [map_smul,bareTest_embed]
  rw [(physicalBasis p F).starProjection_eq_sum_rankOne]
  simp only [sum_apply,InnerProductSpace.rankOne_apply]

theorem gradedTest_frame (p : PhysicalMomentum) (F : Index) (g : Label) (x : H) :
    gradedTest p F g x=∑i : PhysicalBasisIndex p F,inner ℂ (physicalFrame p F (g,i)) x • bareTest p F i := by
  rw [gradedTest,projectionTest_frame]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun c : ℂ=>c • bareTest p F i) (NativeHistoryGrade.projection_symmetric g (physicalBasis p F i).val x).symm

def yukawaFiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  GaussYukawaCoefficient.sourceMap (scalarField z)

theorem yukawaFiber_smooth (z : physicalChart) : ContDiffAt ℝ ∞ yukawaFiber z.val :=
  (GaussYukawaCoefficient.sourceMap.contDiff.comp scalarField_smooth).contDiffAt

def physicalForm (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (r : ℝ) : ℂ :=
  fieldForm f p a b r-fiberFieldForm f yukawaFiber a b r

def physicalJets (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : TwoJets (physicalForm f p a b) :=
  (fieldJets f p a b).sub (fiberFieldJets f yukawaFiber yukawaFiber_smooth a b)

theorem yukawa_form_source (f : Field289) (a b : QuantumTest) :
    fiberFieldForm f yukawaFiber a b 0=sourcePair a (GaussYukawaOperator.originalAction b) := by
  rw [fiberFieldForm,sourcePair_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    simp only [curve_zero,fiberSample]
    rw [←pairSample_source]
    rfl

theorem physicalForm_source (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    physicalForm f p a b 0=sourcePair a (physicalAction p b) := by
  rw [physicalForm,fieldForm_source,yukawa_form_source]
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,add_sub_cancel_right]

theorem physicalForm_sesq (f : Field289) (p : PhysicalMomentum) : SesqGerm (physicalForm f p) := by
  have h:=(fieldForm_sesq f p).add ((fiberField_sesq f yukawaFiber yukawaFiber_smooth).scale (-1))
  unfold physicalForm
  simpa only [neg_one_mul,sub_eq_add_neg] using h

attribute [local irreducible] fieldForm physicalForm fieldJets physicalJets physicalAction diagonalAction

def gradedForm (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ) : H →L[ℂ] H :=
  ∑g : Label,∑i : PhysicalBasisIndex p F,∑j : PhysicalBasisIndex p F,
    physicalForm f p (bareTest p F i) (bareTest p F j) r •
      InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j))

def gradedCurrent (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ) : H →L[ℂ] H :=
  ∑g : Label,∑i : PhysicalBasisIndex p F,∑j : PhysicalBasisIndex p F,
    (physicalJets f p (bareTest p F i) (bareTest p F j)).first r •
      InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j))

def gradedContact (f : Field289) (p : PhysicalMomentum) (F : Index) : H →L[ℂ] H :=
  ∑g : Label,∑i : PhysicalBasisIndex p F,∑j : PhysicalBasisIndex p F,
    (physicalJets f p (bareTest p F i) (bareTest p F j)).second •
      InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j))

theorem gradedForm_pair (f : Field289) (p : PhysicalMomentum) (F : Index) (x y : H) :
    (fun r=>inner ℂ x (gradedForm f p F r y))=ᶠ[𝓝 0]
      fun r=>∑g : Label,physicalForm f p (gradedTest p F g x) (gradedTest p F g y) r := by
  have hg (g : Label):=(physicalForm_sesq f p).finite_frame (bareTest p F)
    (fun i=>inner ℂ (physicalFrame p F (g,i)) x) (fun j=>inner ℂ (physicalFrame p F (g,j)) y)
  simp only [←gradedTest_frame] at hg
  filter_upwards [Filter.eventually_all.mpr hg] with r hr
  simp only [gradedForm,sum_apply,smul_apply,InnerProductSpace.rankOne_apply,inner_sum,inner_smul_right]
  apply Finset.sum_congr rfl
  intro g _
  rw [hr g]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [←inner_conj_symm x (physicalFrame p F (g,i))]
  simp only [starRingEnd_apply]
  ring

theorem compression_raw_pair (T : H →ₗ.[ℂ] H) (F : Finset T.domain) (x y : H) :
    inner ℂ x (FiniteCoreEvolution.compression T F y)=
      inner ℂ ((FiniteCoreEvolution.coreSpan T F).starProjection x)
        (T ⟨(FiniteCoreEvolution.coreSpan T F).starProjection y,
          FiniteCoreEvolution.coreSpan_le T F ((FiniteCoreEvolution.coreSpan T F).orthogonalProjectionOnto y).property⟩) := by
  change inner ℂ x ((FiniteCoreEvolution.coreSpan T F).starProjection _) = _
  exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm

theorem finite_compression_pair (p : PhysicalMomentum) (F : Index) (x y : H) :
    inner ℂ x (FiniteCoreEvolution.compression (physical p) F y)=
      sourcePair (projectionTest p F x) (physicalAction p (projectionTest p F y)) := by
  rw [compression_raw_pair (physical p) F x y]
  change inner ℂ ((physicalSpan p F).starProjection x) (embed (physicalAction p (projectionTest p F y)))=
    inner ℂ (embed (projectionTest p F x)) (embed (physicalAction p (projectionTest p F y)))
  exact congrArg (fun v : H=>inner ℂ v (embed (physicalAction p (projectionTest p F y)))) (projectionTest_embed p F x).symm

theorem gradedForm_zero (f : Field289) (p : PhysicalMomentum) (F : Index) :
    gradedForm f p F 0=compression p F := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  have same:= (gradedForm_pair f p F x y).self_of_nhds
  change inner ℂ x (gradedForm f p F 0 y)=∑g : Label,physicalForm f p (gradedTest p F g x) (gradedTest p F g y) 0 at same
  rw [same]
  simp only [physicalForm_source,compression_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact (finite_compression_pair p F (projection g x) (projection g y)).symm.trans
    (NativeHistoryGrade.projection_symmetric g x (FiniteCoreEvolution.compression (physical p) F (projection g y)))

theorem gradedForm_first (f : Field289) (p : PhysicalMomentum) (F : Index) :
    HasDerivAt (gradedForm f p F) (gradedCurrent f p F 0) 0 := by
  unfold gradedForm gradedCurrent
  apply HasDerivAt.fun_sum; intro g _
  apply HasDerivAt.fun_sum; intro i _
  apply HasDerivAt.fun_sum; intro j _
  exact (physicalJets f p (bareTest p F i) (bareTest p F j)).actual.1.smul_const
    (InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j)))

theorem gradedCurrent_second (f : Field289) (p : PhysicalMomentum) (F : Index) :
    HasDerivAt (gradedCurrent f p F) (gradedContact f p F) 0 := by
  unfold gradedCurrent gradedContact
  apply HasDerivAt.fun_sum; intro g _
  apply HasDerivAt.fun_sum; intro i _
  apply HasDerivAt.fun_sum; intro j _
  exact (physicalJets f p (bareTest p F i) (bareTest p F j)).second_derivative.smul_const
    (InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j)))

def gradedPairJets (f : Field289) (p : PhysicalMomentum) (F : Index) (x y : H) :
    TwoJets (fun r=>inner ℂ x (gradedForm f p F r y)) where
  first r:=inner ℂ x (gradedCurrent f p F r y)
  second:=inner ℂ x (gradedContact f p F y)
  derivative_near:=by
    have h:=Filter.eventually_all.mpr (fun i : PhysicalBasisIndex p F=>Filter.eventually_all.mpr
      (fun j : PhysicalBasisIndex p F=>(physicalJets f p (bareTest p F i) (bareTest p F j)).derivative_near))
    filter_upwards [h] with r hr
    apply paired_derivative
    unfold gradedForm gradedCurrent
    apply HasDerivAt.fun_sum; intro g _
    apply HasDerivAt.fun_sum; intro i _
    apply HasDerivAt.fun_sum; intro j _
    exact (hr i j).smul_const (InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j)))
  second_derivative:=paired_derivative (gradedCurrent_second f p F) x y

theorem gradedCurrent_source (f : Field289) (p : PhysicalMomentum) (F : Index) (x y : H) :
    inner ℂ x (gradedCurrent f p F 0 y)=
      ∑g : Label,(physicalJets f p (gradedTest p F g x) (gradedTest p F g y)).first 0 :=
  ((gradedPairJets f p F x y).actual.1.congr_of_eventuallyEq (gradedForm_pair f p F x y).symm).unique
    (sumJets (fun g : Label=>physicalJets f p (gradedTest p F g x) (gradedTest p F g y))).actual.1

theorem gradedContact_source (f : Field289) (p : PhysicalMomentum) (F : Index) (x y : H) :
    inner ℂ x (gradedContact f p F y)=
      ∑g : Label,(physicalJets f p (gradedTest p F g x) (gradedTest p F g y)).second :=
  ((gradedPairJets f p F x y).actual.2.congr_of_eventuallyEq (gradedForm_pair f p F x y).deriv.symm).unique
    (sumJets (fun g : Label=>physicalJets f p (gradedTest p F g x) (gradedTest p F g y))).actual.2

theorem original_basis_density_transport (f : Field289) (p : PhysicalMomentum) (F : Index) (i : PhysicalBasisIndex p F)
    (N : ℕ) (word : SourceQuantumConfigurationHilbert.Occupation) (r : ℝ) (small : |r|≤fieldRadius f (bareTest p F i)) :
    ‖transportedSector f N (bareTest p F i) word r small‖=‖scalarLp N (component word (bareTest p F i))‖ :=
  transportedSector_norm f N (bareTest p F i) word r small

end LowEnergy.PreparationVacuumGradedTransport
