import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.ClosedRange.LivingLawRootGeneratedScalarFeatureClosedRangeNaturalityKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaNativePortMoments
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace PaCoefficientSourceGram
open Complex Filter MeasureTheory Set
open scoped BigOperators InnerProductSpace Topology
namespace Port
export CenteredGram.IntegralGraphJointAction.OriginalKCrossParameterRAdjointSource.PaNativePortSource
  (Pa sourceMap sourceMap_zero_iff)
export CenteredGram.IntegralGraphJointAction.OriginalKCrossParameterRAdjointSource.PaNativePortMoments
  (actual_port_log_moment)
end Port
namespace FG
export SourceGeneratedFiniteGram
  (Coordinates action Kernel Compatible solutionClass coefficients equation full_fibre sourceEffect source_effect_eq)
end FG
namespace Hilbert
export SourceGeneratedComplexFeaturePerfectification
  (HilbertAmbient canonicalHilbertMap canonicalHilbertMap_ker hilbertAmbientRealizationCLM
   hilbertAmbientRealization_source_readback hilbertAmbientClosedRangeEquiv)
end Hilbert
abbrev Index := BurnolCompactCoPoissonGeneratorIndex
local instance : DecidableEq Index := Classical.decEq _
local notation "q" => (1/4:ℝ)
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
abbrev SourceSpace := Hilbert.HilbertAmbient burnolCompactCoPoissonLanding

/-- Both parities retain the original source recipe, including the actual reciprocal. -/
def recipe (i : Index) : burnolCompactAnnulusSource :=
  if i.2=0 then i.1 else burnolCompactTateReciprocalSource i.1
def sigmaGenerator (i : Index) : BurnolL2 := (recipe i).1.toLp 2 volume
def arithmeticRaw (i : Index) (x : ℝ) : ℂ := burnolCompactAdditiveCoSum (recipe i) x

/-- The complete integer co-sum and its normalization generate the source metric. -/
def arithmeticGram (i j : Index) : ℂ :=
  ∫x:ℝ,star (arithmeticRaw i x)*arithmeticRaw j x
def scalarBill (c : BurnolCompletedMellinCoordinate) (i : Index) : ℂ :=
  2*∫t:ℝ in Icc q 4,(t:ℂ)^(-c.value)*(recipe i).1 t
def matrix (F : Finset Index) : Matrix ↥F ↥F ℂ := fun i j=>arithmeticGram i.1 j.1
def rhs (c : BurnolCompletedMellinCoordinate) (F : Finset Index) : FG.Coordinates ↥F :=
  WithLp.toLp 2 (fun i=>star (scalarBill c i.1))

theorem generator_recipe (i : Index) :
    burnolCompactCoPoissonGenerator i=burnolCompactAdditivePhysicalState (recipe i) := by
  rcases i with ⟨g,p⟩
  fin_cases p
  · rfl
  · apply Subtype.ext
    exact burnolCompactFourierL2_eq_reciprocalL2 g

theorem arithmetic_gram_read (i j : Index) :
    arithmeticGram i j=inner ℂ (burnolCompactCoPoissonGenerator i) (burnolCompactCoPoissonGenerator j) := by
  rw [generator_recipe,generator_recipe]
  change arithmeticGram i j=inner ℂ (burnolCompactAdditiveL2 (recipe i)) (burnolCompactAdditiveL2 (recipe j))
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolCompactAdditiveL2_coeFn (recipe i),burnolCompactAdditiveL2_coeFn (recipe j)] with x left right
  simp only [arithmeticRaw,RCLike.inner_apply,starRingEnd_apply,left,right]
  ring

theorem hermitian (F : Finset Index) : (matrix F).IsHermitian := by
  ext i j
  change star (arithmeticGram j.1 i.1)=arithmeticGram i.1 j.1
  rw [arithmetic_gram_read,arithmetic_gram_read]
  exact inner_conj_symm _ _

theorem sigma_generator_read (i : Index) :
    burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolCompactCoPoissonGenerator i))=sigmaGenerator i := by
  rw [generator_recipe]
  exact burnolCompactPa_tate_source (recipe i)

theorem bill_read (c : BurnolCompletedMellinCoordinate) (i : Index) :
    burnolPaResolventSourceCoefficient c (burnolCompactCoPoissonGenerator i)=scalarBill c i := by
  let p : ↥Port.Pa := ⟨burnolCompactCoPoissonGenerator i,burnolCompactCoPoissonGenerator_mem_closedRange i⟩
  have generated:=Port.actual_port_log_moment c 0 p
  change burnolPaResolventSourceCoefficient c (burnolCompactCoPoissonGenerator i)=_ at generated
  have source : Port.sourceMap p=sigmaGenerator i:=sigma_generator_read i
  rw [source] at generated
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one] at generated
  change _=2*∫t:ℝ in Icc q 4,(t:ℂ)^(-c.value)*sigmaGenerator i t at generated
  rw [generated]
  unfold scalarBill
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae ((recipe i).1.coeFn_toLp 2 volume)] with t actual
  rw [show sigmaGenerator i t=(recipe i).1 t from actual]

def input (F : Finset Index) : FG.Coordinates ↥F →ₗ[ℂ] BurnolCompactCoPoissonLinearSource where
  toFun a:=∑i:↥F,Finsupp.single i.1 (a i)
  map_add' a b:=by simp only [PiLp.add_apply,Finsupp.single_add,Finset.sum_add_distrib]
  map_smul' z a:=by simp only [PiLp.smul_apply,Finsupp.smul_single,Finset.smul_sum,RingHom.id_apply]
def physicalSynthesis (F : Finset Index) : FG.Coordinates ↥F →ₗ[ℂ] BurnolPaAmbientCarrier :=
  burnolCompactCoPoissonLanding.comp (input F)
def sigmaLanding : BurnolCompactCoPoissonLinearSource →ₗ[ℂ] BurnolL2 :=
  Finsupp.lsum ℂ fun i=>LinearMap.toSpanSingleton ℂ _ (sigmaGenerator i)
def sigmaSynthesis (F : Finset Index) : FG.Coordinates ↥F →ₗ[ℂ] BurnolL2 :=
  sigmaLanding.comp (input F)
def hilbertSynthesis (F : Finset Index) : FG.Coordinates ↥F →ₗ[ℂ] SourceSpace :=
  (Hilbert.canonicalHilbertMap burnolCompactCoPoissonLanding).comp (input F)
def sourceWriter : SourceSpace →L[ℂ] BurnolL2 :=
  (burnolTateReciprocalL2.comp burnolMobiusSourceL2).comp
    (Hilbert.hilbertAmbientRealizationCLM burnolCompactCoPoissonLanding)

theorem physical_synthesis_read (F : Finset Index) (a : FG.Coordinates ↥F) :
    physicalSynthesis F a=∑i:↥F,a i • burnolCompactCoPoissonGenerator i.1 := by
  change burnolCompactCoPoissonLanding (∑i:↥F,Finsupp.single i.1 (a i))=_
  rw [map_sum]
  simp only [burnolCompactCoPoissonLanding_single]

theorem sigma_landing_read (u : BurnolCompactCoPoissonLinearSource) :
    sigmaLanding u=burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolCompactCoPoissonLanding u)) := by
  induction u using Finsupp.induction_linear with
  | zero=>simp only [map_zero]
  | add u v hu hv=>simp only [map_add,hu,hv]
  | single i z=>
    simp only [sigmaLanding,Finsupp.lsum_single,LinearMap.toSpanSingleton_apply,
      burnolCompactCoPoissonLanding_single,map_smul,sigma_generator_read]

theorem writer_synthesis (F : Finset Index) (a : FG.Coordinates ↥F) :
    sourceWriter (hilbertSynthesis F a)=sigmaSynthesis F a := by
  change sourceWriter (Hilbert.canonicalHilbertMap burnolCompactCoPoissonLanding (input F a))=
    sigmaLanding (input F a)
  rw [sigma_landing_read]
  change burnolTateReciprocalL2 (burnolMobiusSourceL2
    (SourceGeneratedComplexFeaturePerfectification.hilbertAmbientRealization
      burnolCompactCoPoissonLanding (Hilbert.canonicalHilbertMap burnolCompactCoPoissonLanding (input F a))))=_
  rw [Hilbert.hilbertAmbientRealization_source_readback]

theorem action_read (F : Finset Index) (a : FG.Coordinates ↥F) (i : ↥F) :
    FG.action (matrix F) a i=inner ℂ (burnolCompactCoPoissonGenerator i.1) (physicalSynthesis F a) := by
  change (∑j:↥F,arithmeticGram i.1 j.1*a j)=_
  rw [physical_synthesis_read,inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    arithmeticGram i.1 j.1*a j=
        a j*inner ℂ (burnolCompactCoPoissonGenerator i.1) (burnolCompactCoPoissonGenerator j.1) := by
      rw [arithmetic_gram_read]
      ring
    _=inner ℂ (burnolCompactCoPoissonGenerator i.1) (a j • burnolCompactCoPoissonGenerator j.1) :=
      (_root_.inner_smul_right (𝕜:=ℂ) (burnolCompactCoPoissonGenerator i.1)
        (burnolCompactCoPoissonGenerator j.1) (a j)).symm

theorem kernel_physical (F : Finset Index) : FG.Kernel (matrix F) ≤ (physicalSynthesis F).ker := by
  intro a zero
  have pair : inner ℂ (physicalSynthesis F a) (physicalSynthesis F a)=0 := by
    calc
      _=inner ℂ (∑i:↥F,a i • burnolCompactCoPoissonGenerator i.1) (physicalSynthesis F a) :=
        congrArg (fun left=>inner ℂ left (physicalSynthesis F a)) (physical_synthesis_read F a)
      _=∑i:↥F,star (a i)*inner ℂ (burnolCompactCoPoissonGenerator i.1) (physicalSynthesis F a) := by
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro i _
        exact _root_.inner_smul_left (𝕜:=ℂ) (burnolCompactCoPoissonGenerator i.1) (physicalSynthesis F a) (a i)
      _=0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [←action_read,show FG.action (matrix F) a=0 from zero]
        simp only [PiLp.zero_apply,mul_zero]
  exact inner_self_eq_zero.mp pair

theorem kernel_sigma (F : Finset Index) : FG.Kernel (matrix F) ≤ (sigmaSynthesis F).ker := by
  intro a zero
  change sigmaLanding (input F a)=0
  rw [sigma_landing_read]
  have physical:=kernel_physical F zero
  change burnolCompactCoPoissonLanding (input F a)=0 at physical
  rw [physical,map_zero,map_zero]

theorem sigma_kernel_exact (F : Finset Index) : (sigmaSynthesis F).ker=FG.Kernel (matrix F) := by
  apply le_antisymm
  · intro a zero
    have member : physicalSynthesis F a∈burnolCompactCoPoissonClosedRange :=
      (LinearMap.range burnolCompactCoPoissonLanding).le_topologicalClosure ⟨input F a,rfl⟩
    let original : ↥Port.Pa := ⟨physicalSynthesis F a,member⟩
    have sourceZero : Port.sourceMap original=0 := by
      change burnolTateReciprocalL2
        (burnolMobiusSourceL2 (burnolCompactCoPoissonLanding (input F a)))=0
      rw [←sigma_landing_read]
      exact zero
    have physicalZero := congrArg (fun p:↥Port.Pa=>(p:BurnolPaAmbientCarrier))
      ((Port.sourceMap_zero_iff original).mp sourceZero)
    change FG.action (matrix F) a=0
    ext i
    change FG.action (matrix F) a i=0
    rw [action_read,show physicalSynthesis F a=0 from physicalZero,inner_zero_right]
  · exact kernel_sigma F

theorem sigma_fibre (F : Finset Index) (a b : FG.Coordinates ↥F) :
    sigmaSynthesis F a=sigmaSynthesis F b ↔ a-b∈FG.Kernel (matrix F) := by
  rw [←sigma_kernel_exact F]
  change _ ↔ sigmaSynthesis F (a-b)=0
  rw [map_sub,sub_eq_zero]

theorem kernel_hilbert (F : Finset Index) : FG.Kernel (matrix F) ≤ (hilbertSynthesis F).ker := by
  intro a zero
  change input F a∈(Hilbert.canonicalHilbertMap burnolCompactCoPoissonLanding).ker
  rw [Hilbert.canonicalHilbertMap_ker]
  exact kernel_physical F zero

theorem compatible (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    FG.Compatible (matrix F) (rhs c F) := by
  intro a zero
  have physical:=kernel_physical F zero
  have scalar:=congrArg (burnolPaResolventSourceCoefficient c) physical
  rw [physical_synthesis_read,map_sum,map_zero] at scalar
  simp only [map_smul,bill_read,smul_eq_mul] at scalar
  have conjugate:=congrArg star scalar
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑i:↥F,star (scalarBill c i.1)*star (a i))=0
  simpa only [star_sum,star_mul,star_zero,mul_comm] using conjugate

def finiteCoefficients (c : BurnolCompletedMellinCoordinate) (F : Finset Index) : FG.Coordinates ↥F :=
  FG.coefficients (matrix F) (hermitian F) (rhs c F) (compatible c F)
def finiteSource (c : BurnolCompletedMellinCoordinate) (F : Finset Index) : BurnolL2 :=
  FG.sourceEffect (matrix F) (hermitian F) (rhs c F) (compatible c F) (sigmaSynthesis F) (kernel_sigma F)
def finiteHilbert (c : BurnolCompletedMellinCoordinate) (F : Finset Index) : SourceSpace :=
  FG.sourceEffect (matrix F) (hermitian F) (rhs c F) (compatible c F) (hilbertSynthesis F) (kernel_hilbert F)

theorem finite_equation (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    FG.action (matrix F) (finiteCoefficients c F)=rhs c F :=
  FG.equation (matrix F) (hermitian F) (rhs c F) (compatible c F)
theorem coefficient_fibre (c : BurnolCompletedMellinCoordinate) (F : Finset Index) (a : FG.Coordinates ↥F) :
    FG.action (matrix F) a=rhs c F ↔ a-finiteCoefficients c F∈FG.Kernel (matrix F) :=
  FG.full_fibre (matrix F) (hermitian F) (rhs c F) (compatible c F) a

theorem finite_source_read (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    finiteSource c F=∑i:↥F,finiteCoefficients c F i • sigmaGenerator i.1 := by
  rw [finiteSource,FG.source_effect_eq]
  change sigmaLanding (∑i:↥F,Finsupp.single i.1 (finiteCoefficients c F i))=_
  rw [map_sum]
  simp only [sigmaLanding,Finsupp.lsum_single,LinearMap.toSpanSingleton_apply]

theorem finite_source_fibre (c : BurnolCompletedMellinCoordinate) (F : Finset Index)
    (a : FG.Coordinates ↥F) :
    sigmaSynthesis F a=finiteSource c F ↔ FG.action (matrix F) a=rhs c F := by
  rw [finiteSource,FG.source_effect_eq,sigma_fibre]
  exact (coefficient_fibre c F a).symm

theorem finite_writer_read (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    sourceWriter (finiteHilbert c F)=finiteSource c F := by
  rw [finiteHilbert,finiteSource,FG.source_effect_eq,FG.source_effect_eq]
  exact writer_synthesis F (finiteCoefficients c F)

def finiteCalculation (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :=
  (F,matrix F,rhs c F,
   FG.solutionClass (matrix F) (hermitian F) (rhs c F) (compatible c F),
   FG.Kernel (matrix F),finiteCoefficients c F,input F (finiteCoefficients c F),
   finiteHilbert c F,finiteSource c F,
   PLift.up (finite_equation c F),PLift.up (coefficient_fibre c F),
   PLift.up (sigma_fibre F),PLift.up (finite_source_fibre c F),PLift.up (finite_writer_read c F))

def finiteRefinement (c : BurnolCompletedMellinCoordinate) (F G : Finset Index) :=
  (finiteCalculation c F,finiteCalculation c G,finiteHilbert c G-finiteHilbert c F,
   finiteSource c G-finiteSource c F)

/-- The cofinal constructor reads only the generated finite source effects. -/
def completedSource (c : BurnolCompletedMellinCoordinate) : SourceSpace :=
  limUnder atTop (finiteHilbert c)
def sourceValue (c : BurnolCompletedMellinCoordinate) : BurnolL2 := sourceWriter (completedSource c)
def generatedPa (c : BurnolCompletedMellinCoordinate) : ↥Port.Pa :=
  Hilbert.hilbertAmbientClosedRangeEquiv burnolCompactCoPoissonLanding (completedSource c)
def sourceMoment (c : BurnolCompletedMellinCoordinate) (n : Nat) : ℂ :=
  2*(-2:ℂ)^n/(n.factorial:ℂ)*
    ∫t:ℝ in Icc q 4,(t:ℂ)^(-c.value)*(Real.log (t/q):ℂ)^n*sourceValue c t

theorem generated_pa_source (c : BurnolCompletedMellinCoordinate) :
    Port.sourceMap (generatedPa c)=sourceValue c := rfl

theorem source_moment_actual (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    CenteredGram.IntegralGraphJointAction.OriginalKCrossParameterRAdjointSource.PaNativePortSource.port
      c n (generatedPa c)=sourceMoment c n := by
  rw [Port.actual_port_log_moment,generated_pa_source]
  rfl

end PaCoefficientSourceGram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
