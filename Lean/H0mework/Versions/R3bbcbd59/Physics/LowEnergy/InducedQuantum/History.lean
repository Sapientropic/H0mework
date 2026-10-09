import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.Development
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeCurrent.Native
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.StateResponse.TransferNative

/-! The same incoming-zero state and intermediate plus/minus momentum
sectors generate the coframe current history, including its time-principal jet. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
open QuantizationCheck.Fermion Fermion FullQuantum.StateGreen FullQuantum.StateResponse
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair FullQuantum
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def quantizeMatrix : Matrix ι ι ℂ →L[ℂ] WordMatrix ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.toMatrix' (quantize A)
      map_add' := by
        intro A B
        rw [show quantize (A+B)=quantize A+quantize B by
          simp [quantize,add_smul,Finset.sum_add_distrib]]
        exact map_add _ _ _
      map_smul' := by
        intro c A
        rw [show quantize (c • A)=c • quantize A by
          simp [quantize,smul_smul,Finset.smul_sum]]
        exact map_smul _ _ _ }

def matrixRead (w : ι → ℂ) : WordMatrix ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => modePair (oneParticle w) (M*ᵥoneParticle w)
      map_add' := by intros; rw [Matrix.add_mulVec,modePair_add_right]
      map_smul' := by intros; rw [Matrix.smul_mulVec,modePair_smul_right]; rfl }

def centeredMatrix (w : ι → ℂ) (A : WordMatrix ι) : WordMatrix ι := A-matrixRead w A • 1

theorem centeredMatrix_original (w : ι → ℂ) (word : Module.End ℂ (Fock ι)) :
    centeredMatrix w (LinearMap.toMatrix' word)=LinearMap.toMatrix' (centered w word) := by
  simp only [centeredMatrix,centered,map_sub,map_smul]
  have mean : matrixRead w (LinearMap.toMatrix' word)=read w word := by
    change modePair (oneParticle w) (LinearMap.toMatrix' word*ᵥoneParticle w)=_
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  rw [mean]
  congr 2
  ext s t
  simp [LinearMap.toMatrix'_apply,Matrix.one_apply,Pi.single_apply]

theorem centeredMatrix_continuous (w : ι → ℂ) : Continuous (centeredMatrix w) :=
  continuous_id.sub ((matrixRead w).continuous.smul continuous_const)

def realMatrix (A : WordMatrix ι) : WordMatrix ι := (1/2 : ℂ) • (A+A.conjTranspose)

theorem realMatrix_original (word : Module.End ℂ (Fock ι)) :
    realMatrix (LinearMap.toMatrix' word)=LinearMap.toMatrix' (realWord word) := by
  simp [realMatrix,realWord,dagger_matrix]

omit [Fintype ι] [LinearOrder ι] in
theorem realMatrix_continuous : Continuous (realMatrix (ι := ι)) := by
  unfold realMatrix
  fun_prop

attribute [local instance] Fermion.fullIndexOrder
attribute [local instance] transferIndexOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _

abbrev TransferIndex := Fin 3×Quantum.Index
local instance : DecidableEq TransferIndex := (transferIndexOrder (ι := Quantum.Index)).toDecidableEq

def transferWeight (point : BasePoint) : Matrix TransferIndex TransferIndex ℂ :=
  ∑ label : Fin 3, channel label label (CoframeResponse.weightMatrix (actual.coframe point))

def transferPrimal (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) : Matrix TransferIndex TransferIndex ℂ :=
  channel 0 0 (primalMatrix actual point 0 time)+
    channel 1 1 (primalMatrix actual point momentum time)+
    channel 2 2 (primalMatrix actual point (-momentum) time)

def coframeCosineForce (point : BasePoint) (momentum : Fin 3 → ℝ) (reader : LorentzianCoframe) :
    Matrix TransferIndex TransferIndex ℂ :=
  (1/2 : ℂ) • (channel 1 0 (CoframeCurrent.currentForce point 0 reader (actual.coframe point))+
    channel 2 0 (CoframeCurrent.currentForce point 0 reader (actual.coframe point))+
    channel 0 1 (CoframeCurrent.currentForce point momentum reader (actual.coframe point))+
    channel 0 2 (CoframeCurrent.currentForce point (-momentum) reader (actual.coframe point)))

def cosineWord (point : BasePoint) (momentum : Fin 3 → ℝ) (reader : LorentzianCoframe) (time : ℝ) :
    Module.End ℂ (Fock TransferIndex) :=
  physicalWord (quantize (transferWeight point)*quantize
    (transferPrimal point momentum (-time)*coframeCosineForce point momentum reader*transferPrimal point momentum time))

def cosineCurrent (point : BasePoint) (momentum : Fin 3 → ℝ) (reader : LorentzianCoframe) (time : ℝ) : WordMatrix TransferIndex :=
  centeredMatrix (modeVector 0 (preparedVector point)) (LinearMap.toMatrix' (cosineWord point momentum reader time))

theorem sourceMatrix_continuous (point : BasePoint) (momentum : Fin 3 → ℝ) :
    Continuous (primalMatrix actual point momentum) :=
  continuous_iff_continuousAt.mpr fun t => (CoframeCurrent.sourceMatrix_derivative actual point momentum t).continuousAt

theorem channel_continuous (target incoming : Fin 3) :
    Continuous (channel (ι := Quantum.Index) target incoming) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold channel
  split_ifs <;> fun_prop

theorem transferPrimal_continuous (point : BasePoint) (momentum : Fin 3 → ℝ) :
    Continuous (transferPrimal point momentum) :=
  (((channel_continuous 0 0).comp (sourceMatrix_continuous point 0)).add
    ((channel_continuous 1 1).comp (sourceMatrix_continuous point momentum))).add
    ((channel_continuous 2 2).comp (sourceMatrix_continuous point (-momentum)))

theorem cosineCurrent_continuous (point : BasePoint) (momentum : Fin 3 → ℝ) (reader : LorentzianCoframe) :
    Continuous (cosineCurrent point momentum reader) := by
  have body : Continuous (fun t : ℝ => transferPrimal point momentum (-t)*coframeCosineForce point momentum reader*
      transferPrimal point momentum t) :=
    (((transferPrimal_continuous point momentum).comp continuous_neg).mul continuous_const).mul
      (transferPrimal_continuous point momentum)
  have words : Continuous (fun t : ℝ =>
      (-4 : ℂ) • realMatrix (quantizeMatrix (transferWeight point)*quantizeMatrix
        (transferPrimal point momentum (-t)*coframeCosineForce point momentum reader*transferPrimal point momentum t))) :=
    ((realMatrix_continuous.comp ((continuous_const (y := quantizeMatrix (transferWeight point))).mul (quantizeMatrix.continuous.comp body))).const_smul (-4 : ℂ))
  apply (centeredMatrix_continuous (modeVector 0 (preparedVector point))).comp
  convert! words using 1
  funext t
  simp only [cosineWord,physicalWord,map_smul,← realMatrix_original,LinearMap.toMatrix'_mul]
  rfl

theorem cosineCurrent_generated (point : BasePoint) (momentum : Fin 3 → ℝ) (reader : LorentzianCoframe) (time : ℝ) :
    Matrix.toLin' (cosineCurrent point momentum reader time)=
      centered (modeVector 0 (preparedVector point)) (cosineWord point momentum reader time) := by
  have generated := congrArg Matrix.toLin'
    (centeredMatrix_original (ι := TransferIndex) (modeVector 0 (preparedVector point))
      (cosineWord point momentum reader time))
  rw [Matrix.toLin'_toMatrix'] at generated
  exact generated

theorem cosineCurrent_adjoint (point : BasePoint) (momentum : Fin 3 → ℝ) (reader : LorentzianCoframe) (time : ℝ) :
    dagger (cosineWord point momentum reader time)=cosineWord point momentum reader time :=
  physicalWord_adjoint _

theorem cosineNoise_source (point : BasePoint) (momentum : Fin 3 → ℝ) (reader : LorentzianCoframe) (t s : ℝ) :
    transferNativeRead point (dagger (Matrix.toLin' (cosineCurrent point momentum reader t))*
      Matrix.toLin' (cosineCurrent point momentum reader s))=
      noise (modeVector 0 (preparedVector point)) (cosineWord point momentum reader t) (cosineWord point momentum reader s) := by
  rw [transferNativeRead_generated,cosineCurrent_generated,cosineCurrent_generated]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
