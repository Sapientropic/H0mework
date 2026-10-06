import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationRationalWWeightConsumers

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerCorrections
open PreparationVacuumRationalW PreparationVacuumPrincipalBudget
open PreparationVacuumCanonicalMoyal PreparationActualFactor PreparationScalarCoordinates
open PreparationCoordinates PreparationPhaseScalar
open PreparationVacuumLowerLeaves PreparationVacuumTemporalOrdering PreparationVacuumWeylOrdering
open PreparationVacuumEnergyTail GaussNativeEnergy GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology Matrix

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Configuration := SourceCoordinateSlice

def embed94 (u : Fin 94 → ℝ) : Fin 100 → ℝ := fun i => Fin.addCases (fun _ : Fin 6 => 0) u i

theorem embed94_left (u : Fin 94 → ℝ) (i : Fin 6) : embed94 u (Fin.castAdd 94 i)=0 := by simp [embed94]
theorem embed94_right (u : Fin 94 → ℝ) (i : Fin 94) : embed94 u (Fin.natAdd 6 i)=u i := by simp [embed94]

def cov94 (u : Fin 94 → ℝ) : Cotangent := nativeCovector (WithLp.toLp 2 (embed94 u))
def phase94 (x : Phase) (u : Fin 94 → ℝ) : Phase := (x.1,WithLp.toLp 2 (embed94 u))

theorem cov94_add (u v : Fin 94 → ℝ) : cov94 (u+v)=cov94 u+cov94 v := by
  have add : embed94 (u+v)=embed94 u+embed94 v := by
    ext i
    induction i using Fin.addCases (m:=6) (n:=94) with
    | left i => simp [embed94_left]
    | right i => simp [embed94_right]
  unfold cov94
  rw [add,WithLp.toLp_add]
  exact nativeCovectorLinear.map_add _ _

theorem cov94_single (i : Fin 94) : cov94 (Pi.single i 1)=rawCovector (Fin.natAdd 6 i) := by
  have same : embed94 (Pi.single i 1)=Pi.single (Fin.natAdd 6 i) 1 := by
    ext k
    induction k using Fin.addCases (m:=6) (n:=94) with
    | left k =>
      have ne : Fin.natAdd 6 i≠Fin.castAdd 94 k := by
        intro h
        have eq := congrArg Fin.val h
        change 6+i.val=k.val at eq
        omega
      simp [embed94_left,ne]
    | right k => simp [embed94_right,Pi.single_apply,(Fin.natAdd_injective 94 6).eq_iff]
  unfold cov94 rawCovector
  rw [same]

theorem cov94_coframe (u : Fin 94 → ℝ) (i : Fin 6) : coframeMomentum (cov94 u) i=0 := by
  rw [cov94,native_coframe_momentum]
  exact embed94_left u i

def quad {a : ℕ} (M : Matrix (Fin a) (Fin a) ℝ) (u : Fin a → ℝ) : ℝ := u ⬝ᵥ (M *ᵥ u)

theorem quad_sum {a : ℕ} (M : Matrix (Fin a) (Fin a) ℝ) (u : Fin a → ℝ) :
    quad M u=∑ i,∑ j,M i j*u i*u j := by
  unfold quad dotProduct Matrix.mulVec
  simp only [dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quad_sandwich {a : ℕ} (A : Matrix (Fin a) (Fin 94) ℝ) (W : Matrix (Fin a) (Fin a) ℝ)
    (u : Fin 94 → ℝ) : quad ((1/2 : ℝ) • (Aᵀ*W*A)) u=(1/2 : ℝ)*quad W (A *ᵥ u) := by
  unfold quad
  rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  congr 1
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,dotProduct_comm]

theorem raw94_scalar_momentum (x : Phase) (u : Fin 94 → ℝ) (a : Fin 70) :
    rawScalarMomentum a (phase94 x u)=(scalarCoefficients x.1 *ᵥ u) a := by
  rw [actual_rawScalar_momentum_matrix]
  simp only [phase94,WithLp.ofLp_toLp,embed94_right,Matrix.mulVec,dotProduct]

theorem raw94_gauge_momentum (x : Phase) (u : Fin 94 → ℝ) (a : Fin 36) :
    rawGaugeMomentum a (phase94 x u)=(gaugeCoefficients x.1 *ᵥ u) a := by
  rw [actual_rawGauge_momentum_matrix]
  simp only [phase94,WithLp.ofLp_toLp,embed94_right,Matrix.mulVec,dotProduct]

theorem scalarP_quad (n : ℝ) (b : Fin 3 → ℝ) (x : Phase) (u : Fin 94 → ℝ) :
    quad (scalarP n b x) u=(1/2 : ℝ)*scalarWeight n b x*
      scalarNormSquare (fullCoordinates.symm x.1) (cov94 u) := by
  rw [scalarP,quad_sandwich,quad_sum]
  have consumer := actual_scalarW_quadratic n b (phase94 x u)
  simp only [raw94_scalar_momentum] at consumer
  have same : scalarW n b (phase94 x u)=scalarW n b x := rfl
  rw [same] at consumer
  rw [consumer]
  dsimp [phase94,PreparationVacuumRationalW.scalarWeight,cov94]
  ring

theorem gaugeP_quad (n : ℝ) (b : Fin 3 → ℝ) (x : Phase) (u : Fin 94 → ℝ) :
    quad (gaugeP n b x) u=(1/2 : ℝ)*
      (∑ i : Fin 3,∑ j : Fin 3,actualElectric n b i j x*
        electricGram (fullCoordinates.symm x.1) (cov94 u) i j) := by
  rw [gaugeP,quad_sandwich,quad_sum]
  have consumer := actual_gaugeW_quadratic n b (phase94 x u)
  simp only [raw94_gauge_momentum] at consumer
  have same : gaugeW n b (phase94 x u)=gaugeW n b x := rfl
  rw [same] at consumer
  rw [consumer]
  rfl

def totalP (n : ℝ) (b : Fin 3 → ℝ) : RectSymbol 94 94 := fun x => scalarP n b x+gaugeP n b x

theorem original_Qtime_quad (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (x : Phase)
    (physical : fullCoordinates.symm x.1∈physicalChart) (u : Fin 94 → ℝ) :
    timelikePrincipal (fullCoordinates.symm x.1) (cov94 u) n b=quad (totalP n b x) u := by
  let z : physicalChart := ⟨_,physical⟩
  have hn := (time_positive n b time).1.ne'
  have hd := (time_positive n b time).2.ne'
  have gauge := originalElectricPrincipal_generated n b z (cov94 u) hn hd
  have coframe : coframeQuadratic z.val (cov94 u)=0 := by simp [coframeQuadratic,cov94_coframe]
  have scalar : scalarWeight n b x= -n*(volume z.val)⁻¹ := scalar_weight_formula n b z hn
  have contraction : (∑ i : Fin 3,∑ j : Fin 3,b i*S z.val (cov94 u) i j*b j)=
      ∑ i : Fin 3,∑ j : Fin 3,b i*b j*S z.val (cov94 u) i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have split : quad (totalP n b x) u=quad (scalarP n b x) u+quad (gaugeP n b x) u := by
    simp [quad,totalP,Matrix.add_mulVec,dotProduct_add]
  rw [split,scalarP_quad,gaugeP_quad,scalar]
  unfold timelikePrincipal A
  change n*(coframeQuadratic z.val (cov94 u)/sourceTime 0-scalarNormSquare z.val (cov94 u)/(2*volume z.val))+
    _=_
  rw [coframe,zero_div,zero_sub,contraction,←gauge]
  dsimp [z,actualElectric]
  ring

private theorem gram_symmetric (i j : Fin 12) : rawGramInverse i j=rawGramInverse j i := by
  by_cases h : i=j
  · subst j; rfl
  · simp [rawGramInverse,h,Ne.symm h,and_comm,or_comm]

theorem scalarP_symmetric (n : ℝ) (b : Fin 3 → ℝ) (x : Phase) : (scalarP n b x)ᵀ=scalarP n b x := by
  simp [scalarP,scalarW,Matrix.transpose_mul,Matrix.mul_assoc]

theorem gaugeP_symmetric (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (x : Phase)
    (physical : fullCoordinates.symm x.1∈physicalChart) : (gaugeP n b x)ᵀ=gaugeP n b x := by
  have w : (gaugeW n b x)ᵀ=gaugeW n b x := by
    ext i j
    change actualElectric n b (spatialRow j) (spatialRow i) x*rawGramInverse (nativeRow j) (nativeRow i)=_
    rw [gram_symmetric]
    have inverse := originalElectricInverse_symmetric n b ⟨_,physical⟩ (time_positive n b time).1.ne'
      (time_positive n b time).2.ne' (spatialRow j) (spatialRow i)
    exact congrArg (fun c : ℝ => c*rawGramInverse (nativeRow i) (nativeRow j)) inverse
  simp [gaugeP,Matrix.transpose_mul,w,Matrix.mul_assoc]

theorem quad_polarization {a : ℕ} (M : Matrix (Fin a) (Fin a) ℝ) (symmetric : Mᵀ=M)
    (i k : Fin a) :
    (quad M (Pi.single i 1+Pi.single k 1)-quad M (Pi.single i 1)-quad M (Pi.single k 1))/2=M i k := by
  have symm : M k i=M i k := congrArg (fun A : Matrix (Fin a) (Fin a) ℝ => A i k) symmetric
  simp only [quad,Matrix.mulVec_add,add_dotProduct,dotProduct_add,Matrix.mulVec_single_one,
    single_dotProduct,one_mul,Matrix.col,Matrix.transpose_apply,symm]
  ring

/-- The actual source polarization; no coefficient realization is supplied. -/
theorem raw94_Qtime_recognition (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (x : Phase) (physical : fullCoordinates.symm x.1∈physicalChart) (i k : Fin 94) :
    ((totalP n b x i k : ℝ) : ℂ)=timeTensor n b (Fin.natAdd 6 i) (Fin.natAdd 6 k) (fullCoordinates.symm x.1) := by
  rw [originalTimeTensor_polarization n b _ _ _ (time_positive n b time).1.ne' (time_positive n b time).2.ne']
  have symm : (totalP n b x)ᵀ=totalP n b x := by
    simp only [totalP,Matrix.transpose_add,scalarP_symmetric,gaugeP_symmetric n b time x physical]
  have identity := quad_polarization (totalP n b x) symm i k
  rw [←original_Qtime_quad n b time x physical,←original_Qtime_quad n b time x physical,
    ←original_Qtime_quad n b time x physical,cov94_add,cov94_single,cov94_single] at identity
  exact congrArg (fun r : ℝ => (r : ℂ)) identity.symm

end LowEnergy.PreparationVacuumLowerCorrections
