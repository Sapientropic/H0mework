import H0mework.Physics.LowEnergyMatterSpace.Duhamel

/-! The source graded phase transports the co-rotating L² field back to the original clock. -/
set_option autoImplicit false
open MeasureTheory Filter Topology FourierTransform
open scoped SchwartzMap InnerProductSpace Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open Fermion Stage9C.Material.SpinPair
noncomputable section

local instance : LinearOrder SourceIndex :=
  LinearOrder.lift' (Fintype.equivFin SourceIndex) (Fintype.equivFin SourceIndex).injective
local instance : NormedAlgebra ℚ (MatterFiber →L[ℂ] MatterFiber) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

theorem constant_map_toLp (L : MatterFiber →L[ℂ] MatterFiber)
    (f : 𝓢(Position, MatterFiber)) :
    L.compLpL 2 volume (f.toLp 2)=(f.postcompCLM L).toLp 2 := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (f.toLp 2),f.coeFn_toLp 2 volume,
    (f.postcompCLM L).coeFn_toLp 2 volume] with x hl hf hg
  rw [hl,hf,hg]
  rfl

theorem constant_map_fourier_schwartz (L : MatterFiber →L[ℂ] MatterFiber)
    (f : 𝓢(Position, MatterFiber)) :
    𝓕 (f.postcompCLM L)=(𝓕 f).postcompCLM L := by
  apply SchwartzMap.ext
  intro xi
  rw [SchwartzMap.fourier_coe,SchwartzMap.postcompCLM_apply,
    SchwartzMap.fourier_coe,Real.fourier_eq,Real.fourier_eq]
  have generated := L.integral_comp_comm
    ((Real.fourierIntegral_convergent_iff (μ := volume) xi).mpr f.integrable)
  simpa only [SchwartzMap.postcompCLM_apply,Circle.smul_def,map_smul] using generated

theorem constant_map_fourier (L : MatterFiber →L[ℂ] MatterFiber) (f : MatterL2) :
    fourier (L.compLpL 2 volume f)=L.compLpL 2 volume (fourier f) := by
  apply DenseRange.induction_on (p := fun g : MatterL2 =>
      fourier (L.compLpL 2 volume g)=L.compLpL 2 volume (fourier g))
    (SchwartzMap.denseRange_toLpCLM (E := Position) (F := MatterFiber) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (fourier.continuous.comp (L.compLpL 2 volume).continuous)
      ((L.compLpL 2 volume).continuous.comp fourier.continuous)
  · intro test
    change 𝓕 (L.compLpL 2 volume (test.toLp 2))=L.compLpL 2 volume (𝓕 (test.toLp 2))
    rw [constant_map_toLp,SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq,
      constant_map_toLp,constant_map_fourier_schwartz]

def phaseHamiltonian : SourceMatrix := (frequency : ℂ) • sourceCharge

theorem phaseHamiltonian_hermitian : phaseHamiltonian.conjTranspose=phaseHamiltonian := by
  simp [phaseHamiltonian,Matrix.conjTranspose_smul,sourceCharge_hermitian]

def phaseRead (t : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  (timeEvolution phaseHamiltonian t).compLpL 2 volume

theorem phaseRead_ae (t : ℝ) (f : MatterL2) :
    phaseRead t f=ᵐ[volume] fun x => timeEvolution phaseHamiltonian t (f x) :=
  (timeEvolution phaseHamiltonian t).coeFn_compLpL f

theorem phaseRead_norm (t : ℝ) (f : MatterL2) : ‖phaseRead t f‖=‖f‖ := by
  have norm (v : MatterFiber) : ‖timeEvolution phaseHamiltonian t v‖=‖v‖ :=
    ContinuousLinearMap.norm_map_of_mem_unitary
      (timeEvolution_unitary phaseHamiltonian phaseHamiltonian_hermitian t) v
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [phaseRead_ae t f] with x hx
    rw [hx,norm]
  · filter_upwards [phaseRead_ae t f] with x hx
    rw [hx,norm]

theorem phaseRead_fourier (t : ℝ) (f : MatterL2) :
    fourier (phaseRead t f)=phaseRead t (fourier f) :=
  constant_map_fourier (timeEvolution phaseHamiltonian t) f

theorem phaseRead_zero (f : MatterL2) : phaseRead 0 f=f := by
  apply Lp.ext
  filter_upwards [phaseRead_ae 0 f] with x hx
  rw [hx,timeEvolution_zero]

theorem phaseRead_add (s t : ℝ) (f : MatterL2) :
    phaseRead (s+t) f=phaseRead s (phaseRead t f) := by
  apply Lp.ext
  filter_upwards [phaseRead_ae (s+t) f,phaseRead_ae s (phaseRead t f),phaseRead_ae t f]
    with x hadd hs ht
  rw [hadd,hs,ht,evolution_add (fun _ : Unit => phaseHamiltonian) () s t]
  rfl

theorem phaseRead_inverse (t : ℝ) (f : MatterL2) : phaseRead (-t) (phaseRead t f)=f := by
  rw [← phaseRead_add,neg_add_cancel,phaseRead_zero]

theorem original_finite_evolution (k : Momentum) (t : ℝ) :
    timeEvolution (originalHamiltonian k) t=
      timeEvolution phaseHamiltonian t*timeEvolution (sourceHamiltonian k) t := by
  let phi := timeGenerator phaseHamiltonian
  let h := timeGenerator (sourceHamiltonian k)
  have sum : timeGenerator (originalHamiltonian k)=phi+h := by
    unfold phi h timeGenerator hamiltonianOperator originalHamiltonian phaseHamiltonian
    rw [map_add,smul_add,add_comm]
  have commute : Commute (hamiltonianOperator phaseHamiltonian)
      (hamiltonianOperator (sourceHamiltonian k)) := by
    have matrix : phaseHamiltonian*sourceHamiltonian k=sourceHamiltonian k*phaseHamiltonian := by
      simp only [phaseHamiltonian,Matrix.smul_mul,Matrix.mul_smul,sourceHamiltonian_commutes_charge]
    change hamiltonianOperator phaseHamiltonian*hamiltonianOperator (sourceHamiltonian k)=
      hamiltonianOperator (sourceHamiltonian k)*hamiltonianOperator phaseHamiltonian
    ext v i
    change (phaseHamiltonian*ᵥ(sourceHamiltonian k*ᵥ(fun j => v j))) i=
      (sourceHamiltonian k*ᵥ(phaseHamiltonian*ᵥ(fun j => v j))) i
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,matrix]
  have scaled : Commute ((t : ℂ) • phi) ((t : ℂ) • h) := by
    change ((t : ℂ) • phi)*((t : ℂ) • h)=((t : ℂ) • h)*((t : ℂ) • phi)
    have actual := congrArg (fun A : MatterFiber →L[ℂ] MatterFiber => A) commute.eq
    ext v i
    have point := congrArg (fun A : MatterFiber →L[ℂ] MatterFiber => A v i) actual
    simp only [mul_apply_eq_comp] at point
    simp [phi,h,timeGenerator,point]
  change NormedSpace.exp ((t : ℂ) • timeGenerator (originalHamiltonian k))=
    NormedSpace.exp ((t : ℂ) • phi)*NormedSpace.exp ((t : ℂ) • h)
  rw [sum]
  have distribute : (t : ℂ) • (phi+h)=(t : ℂ) • phi+(t : ℂ) • h := by
    ext v i
    simp
  rw [distribute]
  exact NormedSpace.exp_add_of_commute scaled

def originalFourierHamiltonian (xi : Position) : SourceMatrix :=
  originalHamiltonian (fun j => 2*Real.pi*xi j)

theorem originalFourierHamiltonian_continuous : Continuous originalFourierHamiltonian := by
  apply originalHamiltonian_continuous.comp
  fun_prop

theorem originalFourierHamiltonian_hermitian (xi : Position) :
    (originalFourierHamiltonian xi).conjTranspose=originalFourierHamiltonian xi :=
  originalHamiltonian_hermitian _

def originalSpatialUnitary (t : ℝ) : MatterL2 ≃ₗᵢ[ℂ] MatterL2 :=
  (fourier.trans (unitary volume originalFourierHamiltonian originalFourierHamiltonian_continuous
    originalFourierHamiltonian_hermitian t)).trans fourier.symm

theorem originalSpatialUnitary_readback (t : ℝ) (f : MatterL2) :
    originalSpatialUnitary t f=phaseRead t (spatialUnitary t f) := by
  apply fourier.injective
  rw [phaseRead_fourier,spatialUnitary_fourier]
  change fourier (fourier.symm (unitary volume originalFourierHamiltonian
    originalFourierHamiltonian_continuous originalFourierHamiltonian_hermitian t (fourier f)))=_
  rw [fourier.apply_symm_apply]
  apply Lp.ext
  filter_upwards [applyFlow_ae volume originalFourierHamiltonian originalFourierHamiltonian_continuous
    originalFourierHamiltonian_hermitian t (fourier f),
    applyFlow_ae volume actualFourierHamiltonian actualFourierHamiltonian_continuous
      actualFourierHamiltonian_hermitian t (fourier f),
    phaseRead_ae t (momentumUnitary t (fourier f))] with xi ho hs hp
  change applyFlow volume originalFourierHamiltonian originalFourierHamiltonian_continuous
    originalFourierHamiltonian_hermitian t (fourier f) xi=phaseRead t (momentumUnitary t (fourier f)) xi
  rw [ho,hp]
  change timeEvolution (originalHamiltonian (fun j => 2*Real.pi*xi j)) t (fourier f xi)=
    timeEvolution phaseHamiltonian t (applyFlow volume actualFourierHamiltonian
      actualFourierHamiltonian_continuous actualFourierHamiltonian_hermitian t (fourier f) xi)
  rw [hs,original_finite_evolution]
  rfl

def originalPerturbation (forcing : ℝ → MatterL2) (t : ℝ) : MatterL2 :=
  phaseRead t (duhamel forcing t)

theorem originalPerturbation_ae (forcing : ℝ → MatterL2) (t : ℝ) :
    originalPerturbation forcing t=ᵐ[volume] fun x =>
      timeEvolution ((frequency : ℂ) • sourceCharge) t (duhamel forcing t x) :=
  phaseRead_ae t (duhamel forcing t)

theorem originalPerturbation_norm (forcing : ℝ → MatterL2) (t : ℝ) :
    ‖originalPerturbation forcing t‖=‖duhamel forcing t‖ :=
  phaseRead_norm t (duhamel forcing t)

theorem originalPerturbation_zero_past (forcing : ℝ → MatterL2)
    (zeroPast : ∀ t, t≤0 → forcing t=0) (t : ℝ) (past : t≤0) :
    originalPerturbation forcing t=0 := by
  rw [originalPerturbation,duhamel_zero_past forcing zeroPast t past,map_zero]

theorem originalPerturbation_readback (forcing : ℝ → MatterL2) (t : ℝ) :
    phaseRead (-t) (originalPerturbation forcing t)=duhamel forcing t :=
  phaseRead_inverse t (duhamel forcing t)

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
