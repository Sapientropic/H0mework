import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorExchangeSelection
import H0mework.Versions.AB.Physics.LowEnergyFullPhase.Derivative

/-! The actual 97 primitive source directions, retaining the coframe derivative
of both adjugate and volume. The original coefficient producer is
matter-vertices/compute.py; its entire matrix table is independently compared
with these expressions before Contact is consumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.MixedSpectatorContactVertices
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineHolonomicField
open SU7MotherLieAlgebra SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
open ActiveMatterSectorCharge QuantizationCheck.Fermion
open scoped BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

def colorRaw (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, 1, 0; -1, 0, 0; 0, 0, 0],
    !![0, Complex.I, 0; Complex.I, 0, 0; 0, 0, 0],
    !![0, 0, 1; 0, 0, 0; -1, 0, 0],
    !![0, 0, Complex.I; 0, 0, 0; Complex.I, 0, 0],
    !![0, 0, 0; 0, 0, 1; 0, -1, 0],
    !![0, 0, 0; 0, 0, Complex.I; 0, Complex.I, 0],
    !![Complex.I, 0, 0; 0, 0, 0; 0, 0, -Complex.I],
    !![0, 0, 0; 0, Complex.I, 0; 0, 0, -Complex.I]] a

def colorBasis (a : Fin 8) : SpecialUnitaryLieMatrix (Fin 3) :=
  ⟨colorRaw a, by
    constructor
    · ext i j
      fin_cases a <;> fin_cases i <;> fin_cases j <;>
        norm_num [colorRaw, Matrix.star_eq_conjTranspose]
    · fin_cases a <;> norm_num [colorRaw, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]⟩

def weakRaw (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; -1, 0],
    !![0, Complex.I; Complex.I, 0],
    !![Complex.I, 0; 0, -Complex.I]] a

def weakBasis (a : Fin 3) : SpecialUnitaryLieMatrix (Fin 2) :=
  ⟨weakRaw a, by
    constructor
    · ext i j
      fin_cases a <;> fin_cases i <;> fin_cases j <;>
        norm_num [weakRaw, Matrix.star_eq_conjTranspose]
    · fin_cases a <;> norm_num [weakRaw, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]⟩

def nativeData (a : Fin 12) : P286LieBlockData :=
  if h : a.val < 8 then (colorBasis ⟨a.val,h⟩,0,0)
  else if h : a.val < 11 then (0,weakBasis ⟨a.val-8,by omega⟩,0)
  else Stage10.HyperchargeResponse.chargeDirection

def nativeMother (a : Fin 12) : SU7MotherLieMatrix := p286LieBlockEmbed (nativeData a)
def gauge (a : Fin 12) : FullQuantum.Mother := diracExteriorMotherLieAction (nativeMother a)
def spin (A : DiracMatrix) : FullQuantum.Mother := diracMatrixMatterAction A

def lorentzMatrix (a : Fin 6) : DiracMatrix :=
  (1/2 : ℂ) • (diracGamma (![0,0,0,2,3,1] a) * diracGamma (![1,2,3,3,1,2] a))

def scalarOrbit (a : Fin 9) : ExteriorBreakingScalarCarrier :=
  exteriorMotherLieAction 4 (nativeMother (![2,3,4,5,6,8,9,10,11] a)) exteriorBreakingScalar

def principal (mu : Fin 4) : FullQuantum.Mother :=
  (if mu = 0 then Complex.I / (lapse : ℂ) else Complex.I) • spin (diracGamma mu)

def sourceJet (p : Fin 4 → ℂ) (mu b : Fin 4) : FullQuantum.Mother :=
  Complex.I • (spin (diracGamma b) * (p mu • 1 + FullQuantum.connection actual 0 mu)) +
    (if mu = 0 then (frequency : ℂ) • (spin (diracGamma b) * FullPhase.phaseGenerator) else 0)

def adjugateDerivative (a nu mu b : Fin 4) : ℝ :=
  (actual.coframe 0).det *
    (((actual.coframe 0)⁻¹) nu a * ((actual.coframe 0)⁻¹) mu b -
     ((actual.coframe 0)⁻¹) mu a * ((actual.coframe 0)⁻¹) nu b)

def volumeDerivative (a nu : Fin 4) : ℝ :=
  (actual.coframe 0).det * ((actual.coframe 0)⁻¹) nu a

def coframeVertex (p : Fin 4 → ℂ) (a nu : Fin 4) : FullQuantum.Mother :=
  (∑ mu : Fin 4, ∑ b : Fin 4, (adjugateDerivative a nu mu b : ℂ) • sourceJet p mu b) +
    (volumeDerivative a nu : ℂ) • diracDualRightChiralYukawaAction exteriorBreakingScalar

/-- The original field ordering is scalar_J9, gauge48, coframe16, Lorentz24. -/
def rawVertex (p : Fin 4 → ℂ) (a : Fin 97) : FullQuantum.Mother :=
  if h : a.val < 9 then (lapse : ℂ) • diracDualRightChiralYukawaAction (scalarOrbit ⟨a.val,h⟩)
  else if h : a.val < 57 then (lapse : ℂ) •
    (principal ⟨(a.val-9)/12,by omega⟩ * gauge ⟨(a.val-9)%12,Nat.mod_lt _ (by decide)⟩)
  else if h : a.val < 73 then
    coframeVertex p ⟨(a.val-57)/4,by omega⟩ ⟨(a.val-57)%4,Nat.mod_lt _ (by decide)⟩
  else (lapse : ℂ) •
    (principal ⟨(a.val-73)/6,by omega⟩ * spin (lorentzMatrix ⟨(a.val-73)%6,Nat.mod_lt _ (by decide)⟩))

private def Commutes (A : FullQuantum.Mother) : Prop := activeProjection * A = A * activeProjection

private theorem commute_add {A B : FullQuantum.Mother} (a : Commutes A) (b : Commutes B) :
    Commutes (A+B) := by
  unfold Commutes at *
  rw [mul_add, add_mul, a, b]
private theorem commute_smul {A : FullQuantum.Mother} (a : Commutes A) (c : ℂ) :
    Commutes (c • A) := by
  unfold Commutes at *
  rw [mul_smul_comm, smul_mul_assoc, a]
private theorem commute_mul {A B : FullQuantum.Mother} (a : Commutes A) (b : Commutes B) :
    Commutes (A*B) := by
  unfold Commutes at *
  rw [← mul_assoc, a, mul_assoc, b, ← mul_assoc]
private theorem commute_sum {ι : Type*} [Fintype ι] (A : ι → FullQuantum.Mother)
    (h : ∀ i, Commutes (A i)) : Commutes (∑ i, A i) := by
  simp only [Commutes, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => h i)
private theorem commute_spin (A : DiracMatrix) : Commutes (spin A) := activeProjection_spin A
private theorem commute_one : Commutes (1 : FullQuantum.Mother) := by simp [Commutes]
private theorem commute_zero : Commutes (0 : FullQuantum.Mother) := by simp [Commutes]
private theorem commute_connection (mu : Fin 4) : Commutes (FullQuantum.connection actual 0 mu) :=
  commute_add (activeProjection_spin _) (activeProjection_gauge _)
private theorem commute_phase : Commutes FullPhase.phaseGenerator := by
  apply commute_add (activeProjection_spin _)
  apply commute_smul
  apply LinearMap.ext
  intro v
  funext s
  simp [activeProjection, MixedSymbol.degreeSix]
private theorem commute_jet (p : Fin 4 → ℂ) (mu b : Fin 4) : Commutes (sourceJet p mu b) := by
  apply commute_add
  · exact commute_smul (commute_mul (commute_spin _) (commute_add (commute_smul commute_one _) (commute_connection _))) _
  · split_ifs
    · exact commute_smul (commute_mul (commute_spin _) commute_phase) _
    · exact commute_zero
private theorem commute_coframe (p : Fin 4 → ℂ) (a nu : Fin 4) : Commutes (coframeVertex p a nu) :=
  commute_add (commute_sum _ (fun mu => commute_sum _ (fun b => commute_smul (commute_jet p mu b) _)))
    (commute_smul (activeProjection_yukawa _) _)

theorem actual_raw_vertex_commutes (p : Fin 4 → ℂ) (a : Fin 97) :
    activeProjection * rawVertex p a = rawVertex p a * activeProjection := by
  unfold rawVertex
  split_ifs
  · exact commute_smul (activeProjection_yukawa _) _
  · exact commute_smul (commute_mul (commute_smul (commute_spin _) _) (activeProjection_gauge _)) _
  · exact commute_coframe p _ _
  · exact commute_smul (commute_mul (commute_smul (commute_spin _) _) (commute_spin _)) _

/-- The source's fixed-coframe Legendre current, before imposing a matter shell. -/
def sourceVertex (p : Fin 4 → ℂ) (a : Fin 97) : Matrix Mode Mode ℂ :=
  SourceRealScalarFock.branches (Quantum.operatorMatrix (spin diracGammaZero * rawVertex p a))

theorem actual_source_vertex_preserves (p : Fin 4 → ℂ) (a : Fin 97) : Preserves (sourceVertex p a) := by
  have h := operator_preserves _ (commute_mul (commute_spin diracGammaZero) (actual_raw_vertex_commutes p a))
  exact preserves_branches _ _ h (primalPreserves_neg (primalPreserves_star h))

/-- This is the original independent momentum; no adjoint graph is imposed. -/
theorem actual_vertex_legendre (p : Fin 4 → ℂ) (a : Fin 97)
    (point : BasePoint) (chi : Module.Dual ℂ DiracExteriorMatterCarrier)
    (v : DiracExteriorMatterCarrier) :
    FullQuantum.normalizedMomentum actual point chi
      (spin diracGammaZero (rawVertex p a v)) = -chi (rawVertex p a v) := by
  have square (w : DiracExteriorMatterCarrier) :
      spin diracGammaZero (spin diracGammaZero w) = -w := by
    funext row
    fin_cases row <;> simp [spin, diracMatrixMatterAction, diracGammaZero, Fin.sum_univ_four]
    · exact neg_one_smul ℂ (w 0)
    · exact neg_one_smul ℂ (w 1)
    · exact neg_one_smul ℂ (w 2)
    · exact neg_one_smul ℂ (w 3)
  simp only [FullQuantum.normalizedMomentum, LinearMap.smul_apply,
    LinearMap.comp_apply, FullQuantum.actual_temporal_principal, map_smul, smul_eq_mul]
  rw [actual_coframe, Stage9C.Dynamics.Homogeneous.homogeneousCoframe_det, abs_of_pos lapse_pos]
  change (-Complex.I * (lapse : ℂ)) * ((Complex.I * (lapse : ℂ)⁻¹) *
    chi (spin diracGammaZero (spin diracGammaZero (rawVertex p a v)))) = _
  rw [square, map_neg]
  have nz : (lapse : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt lapse_pos
  field_simp
  simp [Complex.I_sq]

/-- Every raw primitive density is recovered on the same independent real
coordinates, including the negative conjugate branch and its half normalization. -/
theorem actual_vertex_real_action (p : Fin 4 → ℂ) (a : Fin 97)
    (point : BasePoint) (chi : Module.Dual ℂ DiracExteriorMatterCarrier)
    (v : DiracExteriorMatterCarrier) :
    (∑ i : Mode, ∑ j : Mode,
      SourceRealScalarFock.normalizedMomentum
        (Quantum.dualCoordinates (FullQuantum.normalizedMomentum actual point chi)) i *
      sourceVertex p a i j * SourceRealScalarFock.normalizedPrimal (Quantum.coordinates v) j) =
      -((chi (rawVertex p a v)).re : ℂ) := by
  rw [sourceVertex, SourceRealScalarFock.branches_original_real_bilinear]
  have eval : SourceRealScalarFock.complexBilinear
      (Quantum.operatorMatrix (spin diracGammaZero * rawVertex p a))
      (Quantum.dualCoordinates (FullQuantum.normalizedMomentum actual point chi))
      (Quantum.coordinates v) =
      FullQuantum.normalizedMomentum actual point chi (spin diracGammaZero (rawVertex p a v)) := by
    change _ = (FullQuantum.normalizedMomentum actual point chi) ((spin diracGammaZero * rawVertex p a) v)
    rw [Quantum.full_response]
    simp only [SourceRealScalarFock.complexBilinear, Matrix.mulVec, dotProduct,
      Finset.mul_sum, mul_assoc]
  rw [eval, actual_vertex_legendre]
  simp

end LowEnergy.MixedSpectatorContactVertices
