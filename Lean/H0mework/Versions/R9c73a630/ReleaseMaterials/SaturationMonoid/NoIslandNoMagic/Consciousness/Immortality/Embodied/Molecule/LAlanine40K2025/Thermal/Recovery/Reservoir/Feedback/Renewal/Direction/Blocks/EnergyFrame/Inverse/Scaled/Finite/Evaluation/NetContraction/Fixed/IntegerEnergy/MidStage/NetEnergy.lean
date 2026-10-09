import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.EntryError
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.Weighted

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def midNineQuadraticStage : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  multiply (fromTable midNineWeightedTable pairFin pointerFin)
    (fromTable midNineTable pointerFin pairFin)

def midElevenQuadraticStage : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  multiply (fromTable midElevenWeightedTable pairFin pointerFin)
    (fromTable midElevenTable pointerFin pairFin)

def midNetStage : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  sub midElevenQuadraticStage midNineQuadraticStage

def midBodyStage : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  sourceOrdinaryBodyInt (0 : Basis) (6 : Basis)

private theorem mid_nine_matrix :
    chargedNineInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midNineTable pointerFin pairFin := by
  calc
    _ = fromTable (toTable (chargedNineInt (0 : Basis) (6 : Basis) (by decide))
      pointerFin pairFin) pointerFin pairFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_nine_original_literal]

private theorem mid_eleven_matrix :
    chargedElevenInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midElevenTable pointerFin pairFin := by
  calc
    _ = fromTable (toTable (chargedElevenInt (0 : Basis) (6 : Basis) (by decide))
      pointerFin pairFin) pointerFin pairFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_eleven_original_literal]

private theorem mid_nine_weighted_matrix :
    chargedWeightedInt (0 : Basis) (6 : Basis)
      (chargedNineInt (0 : Basis) (6 : Basis) (by decide)) =
      fromTable midNineWeightedTable pairFin pointerFin := by
  calc
    _ = fromTable (toTable (chargedWeightedInt (0 : Basis) (6 : Basis)
      (chargedNineInt (0 : Basis) (6 : Basis) (by decide))) pairFin pointerFin)
      pairFin pointerFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_nine_weighted_original_literal]

private theorem mid_eleven_weighted_matrix :
    chargedWeightedInt (0 : Basis) (6 : Basis)
      (chargedElevenInt (0 : Basis) (6 : Basis) (by decide)) =
      fromTable midElevenWeightedTable pairFin pointerFin := by
  calc
    _ = fromTable (toTable (chargedWeightedInt (0 : Basis) (6 : Basis)
      (chargedElevenInt (0 : Basis) (6 : Basis) (by decide))) pairFin pointerFin)
      pairFin pointerFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_eleven_weighted_original_literal]

theorem mid_nine_quadratic_source :
    chargedQuadraticInt (0 : Basis) (6 : Basis)
      (chargedNineInt (0 : Basis) (6 : Basis) (by decide)) =
      midNineQuadraticStage := by
  rw [chargedQuadraticInt, mid_nine_weighted_matrix, mid_nine_matrix]
  rfl

theorem mid_eleven_quadratic_source :
    chargedQuadraticInt (0 : Basis) (6 : Basis)
      (chargedElevenInt (0 : Basis) (6 : Basis) (by decide)) =
      midElevenQuadraticStage := by
  rw [chargedQuadraticInt, mid_eleven_weighted_matrix, mid_eleven_matrix]
  rfl

theorem mid_net_source :
    chargedNetInt (0 : Basis) (6 : Basis) (by decide) = midNetStage := by
  rw [chargedNetInt, mid_nine_quadratic_source, mid_eleven_quadratic_source]
  rfl

def midNineQuadraticTable : IntTable 4 4 := ⟨
⟨#[
  (⟨#[9280266414802228216927449272514,13303677691623434200531,1547268587582790082544393,-13303677691627029105144],by decide⟩ : Vector Int 4),
  (⟨#[13303677691623434200531,9280268268740319635046275051849,13303677691628630797656,1547270343335412054298397],by decide⟩ : Vector Int 4),
  (⟨#[1547268587582790082544393,13303677691628630797657,9280266414802228216916706552675,-13303677691632210302213],by decide⟩ : Vector Int 4),
  (⟨#[-13303677691627029105144,1547270343335412054298396,-13303677691632210302213,9280268268740319635029851800267],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-8343172660211075070158,-26892268,8343172660211089540162],by decide⟩ : Vector Int 4),
  (⟨#[8343172660211075070157,0,8343172660211091935986,-41906997],by decide⟩ : Vector Int 4),
  (⟨#[26892268,-8343172660211091935987,0,8343172660211108873808],by decide⟩ : Vector Int 4),
  (⟨#[-8343172660211089540162,41906996,-8343172660211108873807,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem mid_nine_quadratic_literal : toTable midNineQuadraticStage pairFin pairFin = midNineQuadraticTable := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel

def midElevenQuadraticTable : IntTable 4 4 := ⟨
⟨#[
  (⟨#[9280276901177645695270182197040,7626817210988844938883,773564405658192913456267,-7626817210991159910701],by decide⟩ : Vector Int 4),
  (⟨#[7626817210988844938883,9280282288537443412785819128437,7626817210992358953138,773563585073584463310974],by decide⟩ : Vector Int 4),
  (⟨#[773564405658192913456267,7626817210992358953137,9280276901177645695263102827070,-7626817210994656409524],by decide⟩ : Vector Int 4),
  (⟨#[-7626817210991159910701,773563585073584463310974,-7626817210994656409524,9280282288537443412775261276782],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-7211983424230672861241,-17035865,7211983424230682996235],by decide⟩ : Vector Int 4),
  (⟨#[7211983424230672861242,0,7211983424230683967826,-26486521],by decide⟩ : Vector Int 4),
  (⟨#[17035865,-7211983424230683967826,0,7211983424230696539375],by decide⟩ : Vector Int 4),
  (⟨#[-7211983424230682996236,26486520,-7211983424230696539376,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem mid_eleven_quadratic_literal : toTable midElevenQuadraticStage pairFin pairFin = midElevenQuadraticTable := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel

def midNetTable : IntTable 4 4 := ⟨
⟨#[
  (⟨#[10486375417478342732924526,-5676860480634589261648,-773704181924597169088126,5676860480635869194443],by decide⟩ : Vector Int 4),
  (⟨#[-5676860480634589261648,14019797123777739544076588,-5676860480636271844518,-773706758261827590987423],by decide⟩ : Vector Int 4),
  (⟨#[-773704181924597169088126,-5676860480636271844520,10486375417478346396274395,5676860480637553892689],by decide⟩ : Vector Int 4),
  (⟨#[5676860480635869194443,-773706758261827590987422,5676860480637553892689,14019797123777745409476515],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,1131189235980402208917,9856403,-1131189235980406543927],by decide⟩ : Vector Int 4),
  (⟨#[-1131189235980402208915,0,-1131189235980407968160,15420476],by decide⟩ : Vector Int 4),
  (⟨#[-9856403,1131189235980407968161,0,-1131189235980412334433],by decide⟩ : Vector Int 4),
  (⟨#[1131189235980406543926,-15420476,1131189235980412334431,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

def midBodyTable : IntTable 4 4 := ⟨
⟨#[
  (⟨#[11799049092519191024333704143,0,141399588,0],by decide⟩ : Vector Int 4),
  (⟨#[0,1596827650858782667779679424,0,19136353],by decide⟩ : Vector Int 4),
  (⟨#[141399588,0,6613137959229503399685705534,0],by decide⟩ : Vector Int 4),
  (⟨#[0,19136353,0,894990898795119678945610151],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,0,-8833387365670570092915969257,0],by decide⟩ : Vector Int 4),
  (⟨#[0,0,0,-1195468981071742651429877448],by decide⟩ : Vector Int 4),
  (⟨#[8833387365670570092915969257,0,0,0],by decide⟩ : Vector Int 4),
  (⟨#[0,1195468981071742651429877448,0,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem mid_body_literal : toTable midBodyStage pairFin pairFin = midBodyTable := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel

private theorem mid_nine_quadratic_matrix :
    midNineQuadraticStage = fromTable midNineQuadraticTable pairFin pairFin := by
  calc
    _ = fromTable (toTable midNineQuadraticStage pairFin pairFin) pairFin pairFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [mid_nine_quadratic_literal]

private theorem mid_eleven_quadratic_matrix :
    midElevenQuadraticStage = fromTable midElevenQuadraticTable pairFin pairFin := by
  calc
    _ = fromTable (toTable midElevenQuadraticStage pairFin pairFin) pairFin pairFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [mid_eleven_quadratic_literal]

theorem mid_net_literal : toTable midNetStage pairFin pairFin = midNetTable := by
  unfold midNetStage
  rw [mid_eleven_quadratic_matrix,mid_nine_quadratic_matrix]
  apply int_table_ext
  · decide +kernel
  · decide +kernel

theorem mid_source_net_literal :
    toTable (sourceOrdinaryNetInt (0 : Basis) (6 : Basis) (by decide))
      pairFin pairFin = midNetTable := by
  rw [← charged_net_original (0 : Basis) (6 : Basis) (by decide),mid_net_source]
  exact mid_net_literal

theorem mid_source_body_literal :
    toTable (sourceOrdinaryBodyInt (0 : Basis) (6 : Basis)) pairFin pairFin =
      midBodyTable := mid_body_literal

private theorem mid_net_matrix :
    chargedNetInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midNetTable pairFin pairFin := by
  calc
    _ = fromTable (toTable (chargedNetInt (0 : Basis) (6 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_net_source,mid_net_literal]

private theorem mid_body_matrix :
    sourceOrdinaryBodyInt (0 : Basis) (6 : Basis) =
      fromTable midBodyTable pairFin pairFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryBodyInt (0 : Basis) (6 : Basis))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_source_body_literal]

theorem mid_energy_numerator_literal :
    (∑ i : Fin 2 × Fin 2,
      (multiply (fromTable midNetTable pairFin pairFin)
        (fromTable midBodyTable pairFin pairFin)).re i i) =
      228011896216884379796873 := by decide +kernel

theorem mid_original_integer_gain :
    sourceOrdinaryGainNumeratorInt (0 : Basis) (6 : Basis) (by decide) =
      228011896216884379796873 := by
  rw [← charged_gain_original (0 : Basis) (6 : Basis) (by decide),
    chargedGainNumeratorInt,mid_net_matrix,mid_body_matrix]
  exact mid_energy_numerator_literal

theorem mid_original_gain_positive :
    0 < smallGainQ (s((0 : Basis),(6 : Basis))) := by
  have margin : (101/10^9 : ℝ) <
      (stagedOrdinaryGainIntQ (0 : Basis) (6 : Basis) (by decide) : ℝ) := by
    rw [staged_ordinary_gain_same,sourceOrdinaryGainIntQ,mid_original_integer_gain]
    norm_num [scale]
  have err := staged_ordinary_gain_error_uniform (0 : Basis) (6 : Basis) (by decide)
  have upper := (abs_lt.mp err).2
  have positive : (0 : ℝ) < (smallGainQ (s((0 : Basis),(6 : Basis))) : ℝ) := by
    linarith only [margin,upper]
  exact_mod_cast positive

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
