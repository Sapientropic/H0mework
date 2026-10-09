import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationMovingNoetherPreparedContact

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumOrderedRealSignal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open QuantizationCheck.Fermion SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert (Mode Occupation)
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open GaussQuantumMultiplier CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalDensity
open PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback
open PreparationVacuumSourceActionJets PreparationVacuumGaugeSourceInjection
open PreparationVacuumJointFieldResponse PreparationVacuumFullFieldRiesz PreparationVacuumSourceFieldFamily
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
abbrev Operator:=H→L[ℂ] H
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _

def sectorConjugation (N : ℕ) : SectorHilbert N→L[ℝ] SectorHilbert N:=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 (numberMeasure N)

theorem sectorConjugation_ae (N : ℕ) (v : SectorHilbert N) :
    sectorConjugation N v=ᵐ[numberMeasure N] (fun z=>star (v z)):=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL v

theorem sectorConjugation_twice (N : ℕ) (v : SectorHilbert N) :
    sectorConjugation N (sectorConjugation N v)=v :=by
  apply Lp.ext
  filter_upwards [sectorConjugation_ae N (sectorConjugation N v),sectorConjugation_ae N v] with z h1 h2
  rw [h1,h2,star_star]

theorem sectorConjugation_bound (N : ℕ) (v : SectorHilbert N) : ‖sectorConjugation N v‖≤ ‖v‖ :=by
  have source:=Complex.conjCLE.toContinuousLinearMap.norm_compLp_le v
  change ‖Complex.conjCLE.toContinuousLinearMap.compLp v‖≤ ‖v‖
  simpa only [Complex.conjCLE_norm,one_mul] using source

theorem sectorConjugation_norm (N : ℕ) (v : SectorHilbert N) : ‖sectorConjugation N v‖=‖v‖ :=by
  apply le_antisymm (sectorConjugation_bound N v)
  simpa only [sectorConjugation_twice] using sectorConjugation_bound N (sectorConjugation N v)

def historyConjugationLinear : H→ₗ[ℝ] H where
  toFun v:=WithLp.toLp 2 (fun word=>sectorConjugation word.card (v word))
  map_add' x y:=by apply PiLp.ext;intro word;exact map_add (sectorConjugation word.card) (x word) (y word)
  map_smul' c x:=by apply PiLp.ext;intro word;exact map_smul (sectorConjugation word.card) c (x word)

theorem historyConjugationLinear_norm (v : H) : ‖historyConjugationLinear v‖=‖v‖ :=by
  have squared : ‖historyConjugationLinear v‖^2=‖v‖^2:=by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro word _
    rw [show historyConjugationLinear v word=sectorConjugation word.card (v word) from rfl,sectorConjugation_norm]
  nlinarith [norm_nonneg (historyConjugationLinear v),norm_nonneg v]

def historyConjugation : H→L[ℝ] H:=
  historyConjugationLinear.mkContinuous 1 (fun v=>by simpa only [one_mul] using (historyConjugationLinear_norm v).le)

theorem historyConjugation_apply (v : H) (word : Occupation) :
    historyConjugation v word=sectorConjugation word.card (v word):=rfl

theorem historyConjugation_twice (v : H) : historyConjugation (historyConjugation v)=v :=by
  apply PiLp.ext
  intro word
  exact sectorConjugation_twice word.card (v word)

theorem historyConjugation_norm (v : H) : ‖historyConjugation v‖=‖v‖:=historyConjugationLinear_norm v

theorem historyConjugation_smul (c : ℂ) (v : H) : historyConjugation (c • v)=star c • historyConjugation v :=by
  apply PiLp.ext
  intro word
  apply Lp.ext
  filter_upwards [sectorConjugation_ae word.card (c • v word),sectorConjugation_ae word.card (v word),
    Lp.coeFn_smul c (v word),Lp.coeFn_smul (star c) (sectorConjugation word.card (v word))] with z h1 h2 h3 h4
  change sectorConjugation word.card (c • v word) z=(star c • sectorConjugation word.card (v word)) z
  simp only [h1,h4,h3,Pi.smul_apply,smul_eq_mul,h2,star_mul,mul_comm]

theorem sectorConjugation_pair (N : ℕ) (x y : SectorHilbert N) :
    inner ℂ (sectorConjugation N x) (sectorConjugation N y)=star (inner ℂ x y) :=by
  rw [L2.inner_def,L2.inner_def]
  change _=(starRingEnd ℂ) (∫z,inner ℂ (x z) (y z) ∂numberMeasure N)
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [sectorConjugation_ae N x,sectorConjugation_ae N y] with z hx hy
  rw [hx,hy]
  change star (y z)*star (star (x z))=star (y z*star (x z))
  rw [star_star,star_mul,star_star]
  ring

theorem historyConjugation_pair (x y : H) :
    inner ℂ (historyConjugation x) (historyConjugation y)=star (inner ℂ x y) :=by
  rw [PiLp.inner_apply,PiLp.inner_apply,star_sum]
  apply Finset.sum_congr rfl
  intro word _
  exact sectorConjugation_pair word.card (x word) (y word)

def fiberConjugationLinear : FockFiber→ₗ[ℝ] FockFiber where
  toFun v:=WithLp.toLp 2 (fun word=>star (v word))
  map_add' x y:=by ext word;exact star_add _ _
  map_smul' c x:=by ext word;simp

theorem fiberConjugationLinear_norm (v : FockFiber) : ‖fiberConjugationLinear v‖=‖v‖ :=by
  have squared : ‖fiberConjugationLinear v‖^2=‖v‖^2:=by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro word _
    exact congrArg (fun r : ℝ=>r^2) (norm_star (v word))
  nlinarith [norm_nonneg (fiberConjugationLinear v),norm_nonneg v]

def fiberConjugation : FockFiber→L[ℝ] FockFiber:=
  fiberConjugationLinear.mkContinuous 1 (fun v=>by simpa only [one_mul] using (fiberConjugationLinear_norm v).le)

theorem fiberConjugation_apply (v : FockFiber) (word : Occupation) : fiberConjugation v word=star (v word):=rfl

theorem fiberConjugation_twice (v : FockFiber) : fiberConjugation (fiberConjugation v)=v :=by
  apply PiLp.ext
  intro word
  exact star_star (v word)

theorem fiberConjugation_quantizer (A : Matrix Mode Mode ℂ) (v : FockFiber) :
    fiberConjugation (quantizer A v)=quantizer (A.map star) (fiberConjugation v) :=by
  apply PiLp.ext
  intro word
  change star (Fermion.quantize A (fiberCoordinates v) word)=
    Fermion.quantize (A.map star) (fiberCoordinates (fiberConjugation v)) word
  have coordinates : fiberCoordinates (fiberConjugation v)=(fun word=>star (fiberCoordinates v word)):=rfl
  rw [coordinates]
  simp only [Fermion.quantize_apply,secondQuantize,star_sum,star_mul,create,annihilate,
    Matrix.map_apply,apply_ite,star_zero,Fermion.star_sign]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

def conjugateTest : QuantumTest→L[ℝ] QuantumTest:=TestFunction.postcompCLM fiberConjugation

theorem conjugateTest_apply (f : QuantumTest) (z : SourceCoordinateSlice) : conjugateTest f z=fiberConjugation (f z):=rfl

theorem historyConjugation_core (f : QuantumTest) : historyConjugation (embed f)=embed (conjugateTest f) :=by
  apply PiLp.ext
  intro word
  apply Lp.ext
  filter_upwards [sectorConjugation_ae word.card (embed f word),embed_ae f word,
    embed_ae (conjugateTest f) word] with z hc hf he
  change sectorConjugation word.card (embed f word) z=embed (conjugateTest f) word z
  rw [hc,he,hf]
  rfl

private def conjugateAlong {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    (C : E→L[ℝ] E) (anti : ∀ (c : ℂ) v,C (c • v)=star c • C v) (isometry : ∀ v,‖C v‖=‖v‖)
    (A : E→L[ℂ] E) : E→L[ℂ] E:=
  let L : E→ₗ[ℂ] E := {
    toFun := fun v=>C (A (C v))
    map_add' := by
      intro x y
      simp only [map_add]
    map_smul' := by
      intro c v
      rw [anti,map_smul,anti,star_star]
      rfl }
  L.mkContinuous ‖A‖ (fun v=>by
    change ‖C (A (C v))‖≤ ‖A‖*‖v‖
    rw [isometry,←isometry v]
    exact A.le_opNorm (C v))

attribute [local irreducible] historyConjugation historyConjugationLinear sectorConjugation

def conjugatedOperator (A : Operator) : Operator:=
  conjugateAlong historyConjugation historyConjugation_smul historyConjugation_norm A

theorem conjugatedOperator_apply (A : Operator) (v : H) :
    conjugatedOperator A v=historyConjugation (A (historyConjugation v)):=rfl

theorem conjugatedOperator_twice (A : Operator) : conjugatedOperator (conjugatedOperator A)=A :=by
  apply ContinuousLinearMap.ext
  intro v
  simp only [conjugatedOperator_apply,historyConjugation_twice]

theorem conjugatedOperator_add (A B : Operator) : conjugatedOperator (A+B)=conjugatedOperator A+conjugatedOperator B :=by
  apply ContinuousLinearMap.ext
  intro v
  simp only [conjugatedOperator_apply,add_apply,map_add]

theorem conjugatedOperator_mul (A B : Operator) : conjugatedOperator (A*B)=conjugatedOperator A*conjugatedOperator B :=by
  apply ContinuousLinearMap.ext
  intro v
  simp only [conjugatedOperator_apply,mul_apply_eq_comp,historyConjugation_twice]

theorem conjugatedOperator_one : conjugatedOperator (1:Operator)=1 :=by
  apply ContinuousLinearMap.ext
  intro v
  exact historyConjugation_twice v

theorem conjugatedOperator_smul (c : ℂ) (A : Operator) : conjugatedOperator (c • A)=star c • conjugatedOperator A :=by
  apply ContinuousLinearMap.ext
  intro v
  simp only [conjugatedOperator_apply,smul_apply,historyConjugation_smul]

theorem conjugatedOperator_norm (A : Operator) : ‖conjugatedOperator A‖=‖A‖ :=by
  have bound (B : Operator) : ‖conjugatedOperator B‖≤ ‖B‖:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
    intro v
    rw [conjugatedOperator_apply,historyConjugation_norm]
    simpa only [historyConjugation_norm] using B.le_opNorm (historyConjugation v)
  apply le_antisymm (bound A)
  simpa only [conjugatedOperator_twice] using bound (conjugatedOperator A)

def conjugationMap : Operator→L[ℝ] Operator:=
  ({toFun:=conjugatedOperator,map_add':=conjugatedOperator_add,
    map_smul':=by
      intro c A
      apply ContinuousLinearMap.ext
      intro v
      change historyConjugation (c • A (historyConjugation v))=c • historyConjugation (A (historyConjugation v))
      exact map_smul historyConjugation c (A (historyConjugation v))} : Operator→ₗ[ℝ] Operator).mkContinuous
    1 (fun A=>by change ‖conjugatedOperator A‖≤1*‖A‖;rw [one_mul];exact (conjugatedOperator_norm A).le)

theorem conjugationMap_apply (A : Operator) : conjugationMap A=conjugatedOperator A:=rfl

attribute [local irreducible] conjugatedOperator

theorem conjugatedOperator_pair (A : Operator) (x y : H) :
    inner ℂ (historyConjugation x) (conjugatedOperator A (historyConjugation y))=star (inner ℂ x (A y)) :=by
  rw [conjugatedOperator_apply,historyConjugation_twice,historyConjugation_pair]

theorem conjugatedOperator_rankOne (x y : H) :
    conjugatedOperator (InnerProductSpace.rankOne ℂ x y)=InnerProductSpace.rankOne ℂ (historyConjugation x) (historyConjugation y) :=by
  apply ContinuousLinearMap.ext
  intro v
  simp only [conjugatedOperator_apply,InnerProductSpace.rankOne_apply,historyConjugation_smul]
  have pair:=historyConjugation_pair y (historyConjugation v)
  rw [historyConjugation_twice] at pair
  rw [pair]

private theorem conjugatedOperator_sum {ι : Type*} [Fintype ι] (family : ι→Operator) :
    conjugatedOperator (∑i,family i)=∑i,conjugatedOperator (family i) :=by
  exact map_sum conjugationMap family Finset.univ

def conjugateRiesz (F : GaussUnitaryHistory.Index) (entries : FrameIndex F→FrameIndex F→ℂ) : Operator:=
  ∑i,∑j,star (entries i j) • InnerProductSpace.rankOne ℂ (historyConjugation (frameVector F i)) (historyConjugation (frameVector F j))

private theorem conjugatedRankOne_sum {ι : Type*} [Fintype ι] (vectors : ι→H) (entries : ι→ι→ℂ) :
    conjugatedOperator (∑i,∑j,entries i j • InnerProductSpace.rankOne ℂ (vectors i) (vectors j))=
      ∑i,∑j,star (entries i j) • InnerProductSpace.rankOne ℂ (historyConjugation (vectors i)) (historyConjugation (vectors j)) :=by
  apply (conjugatedOperator_sum (fun i=>∑j,entries i j • InnerProductSpace.rankOne ℂ (vectors i) (vectors j))).trans
  apply Finset.sum_congr rfl
  intro i _
  apply (conjugatedOperator_sum (fun j=>entries i j • InnerProductSpace.rankOne ℂ (vectors i) (vectors j))).trans
  apply Finset.sum_congr rfl
  intro j _
  exact (conjugatedOperator_smul (entries i j) _).trans
    (congrArg (fun A : Operator=>star (entries i j) • A) (conjugatedOperator_rankOne (vectors i) (vectors j)))

theorem conjugateRiesz_generated (F : GaussUnitaryHistory.Index) (entries : FrameIndex F→FrameIndex F→ℂ) :
    conjugatedOperator (finiteRiesz F entries)=conjugateRiesz F entries :=
  conjugatedRankOne_sum (frameVector F) entries

theorem original_noetherReader_conjugated (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    conjugatedOperator (noetherReader reader p F h)=
      conjugateRiesz F (fun i j=>noetherForm reader p (frameTest F i) (frameTest F j) h) :=
  conjugateRiesz_generated F _

theorem original_noetherContact_conjugated (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    conjugatedOperator (noetherReaderContact reader force p F)=
      conjugateRiesz F (fun i j=>noetherContactForm reader force p (frameTest F i) (frameTest F j)) :=by
  rw [noetherReaderContact_source,conjugateRiesz_generated]

theorem original_rawFiber_conjugated (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) (v : FockFiber) :
    fiberConjugation (rawFiber reader p u v)=
      quantizer ((PreparationVacuumActionFieldLift.rawActionSymbol reader p (ambientState u)).map star) (fiberConjugation v) :=
  fiberConjugation_quantizer _ _

theorem original_noetherFiber_conjugated (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) (v : FockFiber) :
    fiberConjugation (noetherFiber reader p u v)=
      quantizer ((transportedRawSymbol reader (sourceState u.2) (ambientState u) p).map star) (fiberConjugation v) :=
  fiberConjugation_quantizer _ _

end LowEnergy.PreparationVacuumOrderedRealSignal
