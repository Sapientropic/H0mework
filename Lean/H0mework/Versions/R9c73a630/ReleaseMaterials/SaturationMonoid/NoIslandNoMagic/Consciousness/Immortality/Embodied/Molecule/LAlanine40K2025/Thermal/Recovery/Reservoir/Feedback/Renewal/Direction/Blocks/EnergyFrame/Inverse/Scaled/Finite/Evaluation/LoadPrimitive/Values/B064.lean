import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B042
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B043

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1025_pa : Scalar.QComplex := ((999999980023655597971618482019 : Int)/10^30,(-199881686017009640811269072 : Int)/10^30)
theorem v1025_pa_checked : Scalar.distance (sourceCoefficient 11 25 1 0) v1025_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1025_pb : Scalar.QComplex := ((-86244453179928250305501 : Int)/10^30,(-431477506397159734867777513 : Int)/10^30)
theorem v1025_pb_checked : Scalar.distance (sourceCoefficient 11 25 1 1) v1025_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1025_pg : Scalar.QComplex := ((-93086427391942957866717 : Int)/10^30,(18606272424086813910 : Int)/10^30)
theorem v1025_pg_checked : Scalar.distance (sourceCoefficient 11 25 1 2) v1025_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1025_mb : Scalar.QComplex := ((-458590076062425304008552 : Int)/10^30,(-431477271313285818700908902 : Int)/10^30)
theorem v1025_mb_checked : Scalar.distance (sourceCoefficient 11 25 3 1) v1025_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1025_mg : Scalar.QComplex := ((-93086376675236673365048 : Int)/10^30,(98935659878309602815 : Int)/10^30)
theorem v1025_mg_checked : Scalar.distance (sourceCoefficient 11 25 3 2) v1025_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1025_upper : Scalar.QComplex := ((999998145663496661633265639853 : Int)/10^30,(-1925790634548020086398287411 : Int)/10^30)
theorem v1025_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 25 5) 1) 14) v1025_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1025 : Material (11 : Basis) (25 : Basis) where
  plus := ![v1025_pa,v1025_pb,v1025_pg]
  minus := ![(Primitive.Addresses.material1025 1).one,v1025_mb,v1025_mg]
  upper := v1025_upper
  lower := (Primitive.Addresses.material1025 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1025_pa_checked.trans (by decide +kernel)
    · exact v1025_pb_checked.trans (by decide +kernel)
    · exact v1025_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 25 Primitive.Addresses.material1025
    · exact v1025_mb_checked.trans (by decide +kernel)
    · exact v1025_mg_checked.trans (by decide +kernel)
  upper_error := v1025_upper_checked
  lower_error := reuse_lower_error 11 25 Primitive.Addresses.material1025

def v1026_pa : Scalar.QComplex := ((999999978528771653926767361780 : Int)/10^30,(-207225616734835219520445334 : Int)/10^30)
theorem v1026_pa_checked : Scalar.distance (sourceCoefficient 11 26 1 0) v1026_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1026_pb : Scalar.QComplex := ((-89413194092564962300217 : Int)/10^30,(-431477505443578883395489696 : Int)/10^30)
theorem v1026_pb_checked : Scalar.distance (sourceCoefficient 11 26 1 1) v1026_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1026_pg : Scalar.QComplex := ((-93086427219504073096854 : Int)/10^30,(19289892704381774969 : Int)/10^30)
theorem v1026_pg_checked : Scalar.distance (sourceCoefficient 11 26 1 2) v1026_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1026_mb : Scalar.QComplex := ((-461758814972297628481402 : Int)/10^30,(-431477267625224629477753453 : Int)/10^30)
theorem v1026_mb_checked : Scalar.distance (sourceCoefficient 11 26 3 1) v1026_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1026_mg : Scalar.QComplex := ((-93086375912864340021990 : Int)/10^30,(99619279755254499333 : Int)/10^30)
theorem v1026_mg_checked : Scalar.distance (sourceCoefficient 11 26 3 2) v1026_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1026_upper : Scalar.QComplex := ((999998131493656761265868542759 : Int)/10^30,(-1933134551747889466998879526 : Int)/10^30)
theorem v1026_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 26 5) 1) 14) v1026_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1026 : Material (11 : Basis) (26 : Basis) where
  plus := ![v1026_pa,v1026_pb,v1026_pg]
  minus := ![(Primitive.Addresses.material1026 1).one,v1026_mb,v1026_mg]
  upper := v1026_upper
  lower := (Primitive.Addresses.material1026 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1026_pa_checked.trans (by decide +kernel)
    · exact v1026_pb_checked.trans (by decide +kernel)
    · exact v1026_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 26 Primitive.Addresses.material1026
    · exact v1026_mb_checked.trans (by decide +kernel)
    · exact v1026_mg_checked.trans (by decide +kernel)
  upper_error := v1026_upper_checked
  lower_error := reuse_lower_error 11 26 Primitive.Addresses.material1026

def v1027_pa : Scalar.QComplex := ((999999977470542844226847524673 : Int)/10^30,(-212270850104223837625309709 : Int)/10^30)
theorem v1027_pa_checked : Scalar.distance (sourceCoefficient 11 27 1 0) v1027_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1027_pb : Scalar.QComplex := ((-91590098801957460845524 : Int)/10^30,(-431477504770494924751183295 : Int)/10^30)
theorem v1027_pb_checked : Scalar.distance (sourceCoefficient 11 27 1 1) v1027_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1027_pg : Scalar.QComplex := ((-93086427097645549435832 : Int)/10^30,(19759535458353685967 : Int)/10^30)
theorem v1027_pg_checked : Scalar.distance (sourceCoefficient 11 27 1 2) v1027_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1027_mb : Scalar.QComplex := ((-463935718290287872525914 : Int)/10^30,(-431477265073570201396181232 : Int)/10^30)
theorem v1027_mb_checked : Scalar.distance (sourceCoefficient 11 27 3 1) v1027_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1027_mg : Scalar.QComplex := ((-93086375385725316981149 : Int)/10^30,(100088922229198531678 : Int)/10^30)
theorem v1027_mg_checked : Scalar.distance (sourceCoefficient 11 27 3 2) v1027_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1027_upper : Scalar.QComplex := ((999998121727814432104612393661 : Int)/10^30,(-1938179775776588712368320365 : Int)/10^30)
theorem v1027_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 27 5) 1) 14) v1027_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1027 : Material (11 : Basis) (27 : Basis) where
  plus := ![v1027_pa,v1027_pb,v1027_pg]
  minus := ![(Primitive.Addresses.material1027 1).one,v1027_mb,v1027_mg]
  upper := v1027_upper
  lower := (Primitive.Addresses.material1027 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1027_pa_checked.trans (by decide +kernel)
    · exact v1027_pb_checked.trans (by decide +kernel)
    · exact v1027_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 27 Primitive.Addresses.material1027
    · exact v1027_mb_checked.trans (by decide +kernel)
    · exact v1027_mg_checked.trans (by decide +kernel)
  upper_error := v1027_upper_checked
  lower_error := reuse_lower_error 11 27 Primitive.Addresses.material1027

def v1028_pa : Scalar.QComplex := ((999999976004729283198474629836 : Int)/10^30,(-219067434498672198166755751 : Int)/10^30)
theorem v1028_pa_checked : Scalar.distance (sourceCoefficient 11 28 1 0) v1028_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1028_pb : Scalar.QComplex := ((-94522672078350980447106 : Int)/10^30,(-431477503840612109200653221 : Int)/10^30)
theorem v1028_pb_checked : Scalar.distance (sourceCoefficient 11 28 1 1) v1028_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1028_pg : Scalar.QComplex := ((-93086426929115986302842 : Int)/10^30,(20392205223326036990 : Int)/10^30)
theorem v1028_pg_checked : Scalar.distance (sourceCoefficient 11 28 1 2) v1028_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1028_mb : Scalar.QComplex := ((-466868289672303346653710 : Int)/10^30,(-431477261613009072753309326 : Int)/10^30)
theorem v1028_mb_checked : Scalar.distance (sourceCoefficient 11 28 3 1) v1028_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1028_mg : Scalar.QComplex := ((-93086374671230303816731 : Int)/10^30,(100721591613165592071 : Int)/10^30)
theorem v1028_mg_checked : Scalar.distance (sourceCoefficient 11 28 3 2) v1028_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1028_upper : Scalar.QComplex := ((999998108531714970735277204819 : Int)/10^30,(-1944976347518461771497765305 : Int)/10^30)
theorem v1028_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 28 5) 1) 14) v1028_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1028 : Material (11 : Basis) (28 : Basis) where
  plus := ![v1028_pa,v1028_pb,v1028_pg]
  minus := ![(Primitive.Addresses.material1028 1).one,v1028_mb,v1028_mg]
  upper := v1028_upper
  lower := (Primitive.Addresses.material1028 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1028_pa_checked.trans (by decide +kernel)
    · exact v1028_pb_checked.trans (by decide +kernel)
    · exact v1028_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 28 Primitive.Addresses.material1028
    · exact v1028_mb_checked.trans (by decide +kernel)
    · exact v1028_mg_checked.trans (by decide +kernel)
  upper_error := v1028_upper_checked
  lower_error := reuse_lower_error 11 28 Primitive.Addresses.material1028

def v1029_pa : Scalar.QComplex := ((999999972894445279147956609588 : Int)/10^30,(-232832791305247616437634248 : Int)/10^30)
theorem v1029_pa_checked : Scalar.distance (sourceCoefficient 11 29 1 0) v1029_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1029_pb : Scalar.QComplex := ((-100462113870255521006538 : Int)/10^30,(-431477501875870727889800563 : Int)/10^30)
theorem v1029_pb_checked : Scalar.distance (sourceCoefficient 11 29 1 1) v1029_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1029_pg : Scalar.QComplex := ((-93086426572417924737127 : Int)/10^30,(21673573118961261041 : Int)/10^30)
theorem v1029_pg_checked : Scalar.distance (sourceCoefficient 11 29 1 2) v1029_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1029_mb : Scalar.QComplex := ((-472807727557198938783186 : Int)/10^30,(-431477254522797659119994309 : Int)/10^30)
theorem v1029_mb_checked : Scalar.distance (sourceCoefficient 11 29 3 1) v1029_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1029_mg : Scalar.QComplex := ((-93086373208769591800507 : Int)/10^30,(102002958723874625124 : Int)/10^30)
theorem v1029_mg_checked : Scalar.distance (sourceCoefficient 11 29 3 2) v1029_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1029_upper : Scalar.QComplex := ((999998081663678534352783482224 : Int)/10^30,(-1958741678455087190542098198 : Int)/10^30)
theorem v1029_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 29 5) 1) 14) v1029_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1029 : Material (11 : Basis) (29 : Basis) where
  plus := ![v1029_pa,v1029_pb,v1029_pg]
  minus := ![(Primitive.Addresses.material1029 1).one,v1029_mb,v1029_mg]
  upper := v1029_upper
  lower := (Primitive.Addresses.material1029 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1029_pa_checked.trans (by decide +kernel)
    · exact v1029_pb_checked.trans (by decide +kernel)
    · exact v1029_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 29 Primitive.Addresses.material1029
    · exact v1029_mb_checked.trans (by decide +kernel)
    · exact v1029_mg_checked.trans (by decide +kernel)
  upper_error := v1029_upper_checked
  lower_error := reuse_lower_error 11 29 Primitive.Addresses.material1029

def v1030_pa : Scalar.QComplex := ((999999971666315265700991338425 : Int)/10^30,(-238049088773303912221883492 : Int)/10^30)
theorem v1030_pa_checked : Scalar.distance (sourceCoefficient 11 30 1 0) v1030_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1030_pb : Scalar.QComplex := ((-102712828873951565777878 : Int)/10^30,(-431477501102862509839838105 : Int)/10^30)
theorem v1030_pb_checked : Scalar.distance (sourceCoefficient 11 30 1 1) v1030_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1030_pg : Scalar.QComplex := ((-93086426431872884398606 : Int)/10^30,(22159139617120607892 : Int)/10^30)
theorem v1030_pg_checked : Scalar.distance (sourceCoefficient 11 30 1 2) v1030_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1030_mb : Scalar.QComplex := ((-475058441055779647741926 : Int)/10^30,(-431477251807524049147426082 : Int)/10^30)
theorem v1030_mb_checked : Scalar.distance (sourceCoefficient 11 30 3 1) v1030_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1030_mg : Scalar.QComplex := ((-93086372649202584985069 : Int)/10^30,(102488524919951333327 : Int)/10^30)
theorem v1030_mg_checked : Scalar.distance (sourceCoefficient 11 30 3 2) v1030_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1030_upper : Scalar.QComplex := ((999998071432694139005760019292 : Int)/10^30,(-1963957966034440168875417500 : Int)/10^30)
theorem v1030_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 30 5) 1) 14) v1030_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1030 : Material (11 : Basis) (30 : Basis) where
  plus := ![v1030_pa,v1030_pb,v1030_pg]
  minus := ![(Primitive.Addresses.material1030 1).one,v1030_mb,v1030_mg]
  upper := v1030_upper
  lower := (Primitive.Addresses.material1030 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1030_pa_checked.trans (by decide +kernel)
    · exact v1030_pb_checked.trans (by decide +kernel)
    · exact v1030_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 30 Primitive.Addresses.material1030
    · exact v1030_mb_checked.trans (by decide +kernel)
    · exact v1030_mg_checked.trans (by decide +kernel)
  upper_error := v1030_upper_checked
  lower_error := reuse_lower_error 11 30 Primitive.Addresses.material1030

def v1031_pa : Scalar.QComplex := ((999999968963593802414531755246 : Int)/10^30,(-249144157932535971450381344 : Int)/10^30)
theorem v1031_pa_checked : Scalar.distance (sourceCoefficient 11 31 1 0) v1031_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1031_pb : Scalar.QComplex := ((-107500101592914300854801 : Int)/10^30,(-431477499406615393622411124 : Int)/10^30)
theorem v1031_pb_checked : Scalar.distance (sourceCoefficient 11 31 1 1) v1031_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1031_pg : Scalar.QComplex := ((-93086426123106405015204 : Int)/10^30,(23191939971185033768 : Int)/10^30)
theorem v1031_pg_checked : Scalar.distance (sourceCoefficient 11 31 1 2) v1031_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1031_mb : Scalar.QComplex := ((-479845710528437095215879 : Int)/10^30,(-431477245980076818814896887 : Int)/10^30)
theorem v1031_mb_checked : Scalar.distance (sourceCoefficient 11 31 3 1) v1031_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1031_mg : Scalar.QComplex := ((-93086371449176030613146 : Int)/10^30,(103521324623005420694 : Int)/10^30)
theorem v1031_mg_checked : Scalar.distance (sourceCoefficient 11 31 3 2) v1031_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1031_upper : Scalar.QComplex := ((999998049580893869082393257549 : Int)/10^30,(-1975053014004217977147737976 : Int)/10^30)
theorem v1031_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 31 5) 1) 14) v1031_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1031 : Material (11 : Basis) (31 : Basis) where
  plus := ![v1031_pa,v1031_pb,v1031_pg]
  minus := ![(Primitive.Addresses.material1031 1).one,v1031_mb,v1031_mg]
  upper := v1031_upper
  lower := (Primitive.Addresses.material1031 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1031_pa_checked.trans (by decide +kernel)
    · exact v1031_pb_checked.trans (by decide +kernel)
    · exact v1031_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 31 Primitive.Addresses.material1031
    · exact v1031_mb_checked.trans (by decide +kernel)
    · exact v1031_mg_checked.trans (by decide +kernel)
  upper_error := v1031_upper_checked
  lower_error := reuse_lower_error 11 31 Primitive.Addresses.material1031

def v1032_pa : Scalar.QComplex := ((999999967762253346679197227220 : Int)/10^30,(-253920247848353551227759775 : Int)/10^30)
theorem v1032_pa_checked : Scalar.distance (sourceCoefficient 11 32 1 0) v1032_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1032_pb : Scalar.QComplex := ((-109560876931366568537292 : Int)/10^30,(-431477498654627988959511283 : Int)/10^30)
theorem v1032_pb_checked : Scalar.distance (sourceCoefficient 11 32 1 1) v1032_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1032_pg : Scalar.QComplex := ((-93086425986075739022678 : Int)/10^30,(23636529119690207794 : Int)/10^30)
theorem v1032_pg_checked : Scalar.distance (sourceCoefficient 11 32 1 2) v1032_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1032_mb : Scalar.QComplex := ((-481906484450637260338309 : Int)/10^30,(-431477243449733390942799181 : Int)/10^30)
theorem v1032_mb_checked : Scalar.distance (sourceCoefficient 11 32 3 1) v1032_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1032_mg : Scalar.QComplex := ((-93086370928485004035374 : Int)/10^30,(103965913487718442885 : Int)/10^30)
theorem v1032_mg_checked : Scalar.distance (sourceCoefficient 11 32 3 2) v1032_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1032_upper : Scalar.QComplex := ((999998040136457291393943558422 : Int)/10^30,(-1979829094733206024402793463 : Int)/10^30)
theorem v1032_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 32 5) 1) 14) v1032_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1032 : Material (11 : Basis) (32 : Basis) where
  plus := ![v1032_pa,v1032_pb,v1032_pg]
  minus := ![(Primitive.Addresses.material1032 1).one,v1032_mb,v1032_mg]
  upper := v1032_upper
  lower := (Primitive.Addresses.material1032 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1032_pa_checked.trans (by decide +kernel)
    · exact v1032_pb_checked.trans (by decide +kernel)
    · exact v1032_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 32 Primitive.Addresses.material1032
    · exact v1032_mb_checked.trans (by decide +kernel)
    · exact v1032_mg_checked.trans (by decide +kernel)
  upper_error := v1032_upper_checked
  lower_error := reuse_lower_error 11 32 Primitive.Addresses.material1032

def v1033_pa : Scalar.QComplex := ((999999966049978368708605638067 : Int)/10^30,(-260576365217528544677091391 : Int)/10^30)
theorem v1033_pa_checked : Scalar.distance (sourceCoefficient 11 33 1 0) v1033_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1033_pb : Scalar.QComplex := ((-112432841810885160928297 : Int)/10^30,(-431477497584744791687685426 : Int)/10^30)
theorem v1033_pb_checked : Scalar.distance (sourceCoefficient 11 33 1 1) v1033_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1033_pg : Scalar.QComplex := ((-93086425790973314060905 : Int)/10^30,(24256123307198941692 : Int)/10^30)
theorem v1033_pg_checked : Scalar.distance (sourceCoefficient 11 33 1 2) v1033_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1033_mb : Scalar.QComplex := ((-484778447337531059310286 : Int)/10^30,(-431477239901474249509370136 : Int)/10^30)
theorem v1033_mb_checked : Scalar.distance (sourceCoefficient 11 33 3 1) v1033_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1033_mg : Scalar.QComplex := ((-93086370198700773385418 : Int)/10^30,(104585507276159338265 : Int)/10^30)
theorem v1033_mg_checked : Scalar.distance (sourceCoefficient 11 33 3 2) v1033_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1033_upper : Scalar.QComplex := ((999998026936330122710561012232 : Int)/10^30,(-1986485199233644803331742786 : Int)/10^30)
theorem v1033_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 33 5) 1) 14) v1033_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1033 : Material (11 : Basis) (33 : Basis) where
  plus := ![v1033_pa,v1033_pb,v1033_pg]
  minus := ![(Primitive.Addresses.material1033 1).one,v1033_mb,v1033_mg]
  upper := v1033_upper
  lower := (Primitive.Addresses.material1033 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1033_pa_checked.trans (by decide +kernel)
    · exact v1033_pb_checked.trans (by decide +kernel)
    · exact v1033_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 33 Primitive.Addresses.material1033
    · exact v1033_mb_checked.trans (by decide +kernel)
    · exact v1033_mg_checked.trans (by decide +kernel)
  upper_error := v1033_upper_checked
  lower_error := reuse_lower_error 11 33 Primitive.Addresses.material1033

def v1034_pa : Scalar.QComplex := ((999999961706563956704142987058 : Int)/10^30,(-276743329856754578336854938 : Int)/10^30)
theorem v1034_pa_checked : Scalar.distance (sourceCoefficient 11 34 1 0) v1034_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1034_pb : Scalar.QComplex := ((-119408523263899214694895 : Int)/10^30,(-431477494879980456102067862 : Int)/10^30)
theorem v1034_pb_checked : Scalar.distance (sourceCoefficient 11 34 1 1) v1034_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1034_pg : Scalar.QComplex := ((-93086425297055577743459 : Int)/10^30,(25761048287648250548 : Int)/10^30)
theorem v1034_pg_checked : Scalar.distance (sourceCoefficient 11 34 1 2) v1034_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1034_mb : Scalar.QComplex := ((-491754123859090300181280 : Int)/10^30,(-431477231177012000109992819 : Int)/10^30)
theorem v1034_mb_checked : Scalar.distance (sourceCoefficient 11 34 3 1) v1034_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1034_mg : Scalar.QComplex := ((-93086368406100742153399 : Int)/10^30,(106090431270027537218 : Int)/10^30)
theorem v1034_mg_checked : Scalar.distance (sourceCoefficient 11 34 3 2) v1034_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1034_upper : Scalar.QComplex := ((999997994690207867982703615572 : Int)/10^30,(-2002652132297736868293457376 : Int)/10^30)
theorem v1034_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 34 5) 1) 14) v1034_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1034 : Material (11 : Basis) (34 : Basis) where
  plus := ![v1034_pa,v1034_pb,v1034_pg]
  minus := ![(Primitive.Addresses.material1034 1).one,v1034_mb,v1034_mg]
  upper := v1034_upper
  lower := (Primitive.Addresses.material1034 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1034_pa_checked.trans (by decide +kernel)
    · exact v1034_pb_checked.trans (by decide +kernel)
    · exact v1034_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 34 Primitive.Addresses.material1034
    · exact v1034_mb_checked.trans (by decide +kernel)
    · exact v1034_mg_checked.trans (by decide +kernel)
  upper_error := v1034_upper_checked
  lower_error := reuse_lower_error 11 34 Primitive.Addresses.material1034

def v1035_pa : Scalar.QComplex := ((999999946173411429225653516534 : Int)/10^30,(-328105431598209077559679697 : Int)/10^30)
theorem v1035_pa_checked : Scalar.distance (sourceCoefficient 11 35 1 0) v1035_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1035_pb : Scalar.QComplex := ((-141570114155992210325929 : Int)/10^30,(-431477485289300722581140133 : Int)/10^30)
theorem v1035_pb_checked : Scalar.distance (sourceCoefficient 11 35 1 1) v1035_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1035_pg : Scalar.QComplex := ((-93086423539551994951443 : Int)/10^30,(30542162815358828333 : Int)/10^30)
theorem v1035_pg_checked : Scalar.distance (sourceCoefficient 11 35 1 2) v1035_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1035_mb : Scalar.QComplex := ((-513915698223085510099239 : Int)/10^30,(-431477202461881018762977005 : Int)/10^30)
theorem v1035_mb_checked : Scalar.distance (sourceCoefficient 11 35 3 1) v1035_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1035_mg : Scalar.QComplex := ((-93086362522711309750835 : Int)/10^30,(110871542500864231681 : Int)/10^30)
theorem v1035_mg_checked : Scalar.distance (sourceCoefficient 11 35 3 2) v1035_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1035_upper : Scalar.QComplex := ((999997890510750403031492645089 : Int)/10^30,(-2054014130732562134076428326 : Int)/10^30)
theorem v1035_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 35 5) 1) 14) v1035_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1035 : Material (11 : Basis) (35 : Basis) where
  plus := ![v1035_pa,v1035_pb,v1035_pg]
  minus := ![(Primitive.Addresses.material1035 1).one,v1035_mb,v1035_mg]
  upper := v1035_upper
  lower := (Primitive.Addresses.material1035 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1035_pa_checked.trans (by decide +kernel)
    · exact v1035_pb_checked.trans (by decide +kernel)
    · exact v1035_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 35 Primitive.Addresses.material1035
    · exact v1035_mb_checked.trans (by decide +kernel)
    · exact v1035_mg_checked.trans (by decide +kernel)
  upper_error := v1035_upper_checked
  lower_error := reuse_lower_error 11 35 Primitive.Addresses.material1035

def v1036_pa : Scalar.QComplex := ((999999940745844780719901241781 : Int)/10^30,(-344250355014348949278053727 : Int)/10^30)
theorem v1036_pa_checked : Scalar.distance (sourceCoefficient 11 36 1 0) v1036_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1036_pb : Scalar.QComplex := ((-148536285147198404265203 : Int)/10^30,(-431477481961100838819984682 : Int)/10^30)
theorem v1036_pb_checked : Scalar.distance (sourceCoefficient 11 36 1 1) v1036_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1036_pg : Scalar.QComplex := ((-93086422927924718613577 : Int)/10^30,(32045036038755455605 : Int)/10^30)
theorem v1036_pg_checked : Scalar.distance (sourceCoefficient 11 36 1 2) v1036_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1036_mb : Scalar.QComplex := ((-520881863748381271142830 : Int)/10^30,(-431477193122190553526492557 : Int)/10^30)
theorem v1036_mb_checked : Scalar.distance (sourceCoefficient 11 36 3 1) v1036_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1036_mg : Scalar.QComplex := ((-93086360614172356255795 : Int)/10^30,(112374414636865680373 : Int)/10^30)
theorem v1036_mg_checked : Scalar.distance (sourceCoefficient 11 36 3 2) v1036_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1036_upper : Scalar.QComplex := ((999997857218518678002325297655 : Int)/10^30,(-2070159020735247443061024419 : Int)/10^30)
theorem v1036_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 36 5) 1) 14) v1036_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1036 : Material (11 : Basis) (36 : Basis) where
  plus := ![v1036_pa,v1036_pb,v1036_pg]
  minus := ![(Primitive.Addresses.material1036 1).one,v1036_mb,v1036_mg]
  upper := v1036_upper
  lower := (Primitive.Addresses.material1036 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1036_pa_checked.trans (by decide +kernel)
    · exact v1036_pb_checked.trans (by decide +kernel)
    · exact v1036_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 36 Primitive.Addresses.material1036
    · exact v1036_mb_checked.trans (by decide +kernel)
    · exact v1036_mg_checked.trans (by decide +kernel)
  upper_error := v1036_upper_checked
  lower_error := reuse_lower_error 11 36 Primitive.Addresses.material1036

def v1037_pa : Scalar.QComplex := ((999999938348799261547634129713 : Int)/10^30,(-351144411426458813929059751 : Int)/10^30)
theorem v1037_pa_checked : Scalar.distance (sourceCoefficient 11 37 1 0) v1037_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1037_pb : Scalar.QComplex := ((-151510915272749466959729 : Int)/10^30,(-431477480494235292966497145 : Int)/10^30)
theorem v1037_pb_checked : Scalar.distance (sourceCoefficient 11 37 1 1) v1037_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1037_pg : Scalar.QComplex := ((-93086422658128629205658 : Int)/10^30,(32686779111262337746 : Int)/10^30)
theorem v1037_pg_checked : Scalar.distance (sourceCoefficient 11 37 1 2) v1037_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1037_mb : Scalar.QComplex := ((-523856491500502689882196 : Int)/10^30,(-431477189088353727871086467 : Int)/10^30)
theorem v1037_mb_checked : Scalar.distance (sourceCoefficient 11 37 3 1) v1037_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1037_mg : Scalar.QComplex := ((-93086359790580998766905 : Int)/10^30,(113016157237600413519 : Int)/10^30)
theorem v1037_mg_checked : Scalar.distance (sourceCoefficient 11 37 3 2) v1037_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1037_upper : Scalar.QComplex := ((999997842922960785558318974543 : Int)/10^30,(-2077053062742387006807677171 : Int)/10^30)
theorem v1037_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 37 5) 1) 14) v1037_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1037 : Material (11 : Basis) (37 : Basis) where
  plus := ![v1037_pa,v1037_pb,v1037_pg]
  minus := ![(Primitive.Addresses.material1037 1).one,v1037_mb,v1037_mg]
  upper := v1037_upper
  lower := (Primitive.Addresses.material1037 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1037_pa_checked.trans (by decide +kernel)
    · exact v1037_pb_checked.trans (by decide +kernel)
    · exact v1037_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 37 Primitive.Addresses.material1037
    · exact v1037_mb_checked.trans (by decide +kernel)
    · exact v1037_mg_checked.trans (by decide +kernel)
  upper_error := v1037_upper_checked
  lower_error := reuse_lower_error 11 37 Primitive.Addresses.material1037

def v1038_pa : Scalar.QComplex := ((999999929895309052967839102421 : Int)/10^30,(-374445425902622863133575142 : Int)/10^30)
theorem v1038_pa_checked : Scalar.distance (sourceCoefficient 11 38 1 0) v1038_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1038_pb : Scalar.QComplex := ((-161564778345290287861541 : Int)/10^30,(-431477475334035660538667854 : Int)/10^30)
theorem v1038_pb_checked : Scalar.distance (sourceCoefficient 11 38 1 1) v1038_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1038_pg : Scalar.QComplex := ((-93086421708048455548440 : Int)/10^30,(34855787265775556322 : Int)/10^30)
theorem v1038_pg_checked : Scalar.distance (sourceCoefficient 11 38 1 2) v1038_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1038_mb : Scalar.QComplex := ((-533910346376510928614546 : Int)/10^30,(-431477175252124994402404887 : Int)/10^30)
theorem v1038_mb_checked : Scalar.distance (sourceCoefficient 11 38 3 1) v1038_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1038_mg : Scalar.QComplex := ((-93086356968744830023960 : Int)/10^30,(115185163764616367756 : Int)/10^30)
theorem v1038_mg_checked : Scalar.distance (sourceCoefficient 11 38 3 2) v1038_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1038_upper : Scalar.QComplex := ((999997794254046033120799686126 : Int)/10^30,(-2100354027924469917831411301 : Int)/10^30)
theorem v1038_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 38 5) 1) 14) v1038_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1038 : Material (11 : Basis) (38 : Basis) where
  plus := ![v1038_pa,v1038_pb,v1038_pg]
  minus := ![(Primitive.Addresses.material1038 1).one,v1038_mb,v1038_mg]
  upper := v1038_upper
  lower := (Primitive.Addresses.material1038 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1038_pa_checked.trans (by decide +kernel)
    · exact v1038_pb_checked.trans (by decide +kernel)
    · exact v1038_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 38 Primitive.Addresses.material1038
    · exact v1038_mb_checked.trans (by decide +kernel)
    · exact v1038_mg_checked.trans (by decide +kernel)
  upper_error := v1038_upper_checked
  lower_error := reuse_lower_error 11 38 Primitive.Addresses.material1038

def v1039_pa : Scalar.QComplex := ((999999924742422855180581062402 : Int)/10^30,(-387962818612732424001658338 : Int)/10^30)
theorem v1039_pa_checked : Scalar.distance (sourceCoefficient 11 39 1 0) v1039_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1039_pb : Scalar.QComplex := ((-167397228879485922063776 : Int)/10^30,(-431477472197337783012206921 : Int)/10^30)
theorem v1039_pb_checked : Scalar.distance (sourceCoefficient 11 39 1 1) v1039_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1039_pg : Scalar.QComplex := ((-93086421129862894003033 : Int)/10^30,(36114073033971058139 : Int)/10^30)
theorem v1039_pg_checked : Scalar.distance (sourceCoefficient 11 39 1 2) v1039_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1039_mb : Scalar.QComplex := ((-539742792032189676101011 : Int)/10^30,(-431477167082286157621863996 : Int)/10^30)
theorem v1039_mb_checked : Scalar.distance (sourceCoefficient 11 39 3 1) v1039_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1039_mg : Scalar.QComplex := ((-93086355304715536898014 : Int)/10^30,(116443448565346472471 : Int)/10^30)
theorem v1039_mg_checked : Scalar.distance (sourceCoefficient 11 39 3 2) v1039_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1039_upper : Scalar.QComplex := ((999997765771373980590553390289 : Int)/10^30,(-2113871391608596790283840229 : Int)/10^30)
theorem v1039_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 39 5) 1) 14) v1039_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1039 : Material (11 : Basis) (39 : Basis) where
  plus := ![v1039_pa,v1039_pb,v1039_pg]
  minus := ![(Primitive.Addresses.material1039 1).one,v1039_mb,v1039_mg]
  upper := v1039_upper
  lower := (Primitive.Addresses.material1039 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1039_pa_checked.trans (by decide +kernel)
    · exact v1039_pb_checked.trans (by decide +kernel)
    · exact v1039_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 39 Primitive.Addresses.material1039
    · exact v1039_mb_checked.trans (by decide +kernel)
    · exact v1039_mg_checked.trans (by decide +kernel)
  upper_error := v1039_upper_checked
  lower_error := reuse_lower_error 11 39 Primitive.Addresses.material1039

def v1040_pa : Scalar.QComplex := ((999999915663443287872093484158 : Int)/10^30,(-410698315447727414919218069 : Int)/10^30)
theorem v1040_pa_checked : Scalar.distance (sourceCoefficient 11 40 1 0) v1040_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1040_pb : Scalar.QComplex := ((-177207083666011246503517 : Int)/10^30,(-431477466684497340486098874 : Int)/10^30)
theorem v1040_pb_checked : Scalar.distance (sourceCoefficient 11 40 1 1) v1040_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1040_pg : Scalar.QComplex := ((-93086420112631287093427 : Int)/10^30,(38230439155540722037 : Int)/10^30)
theorem v1040_pg_checked : Scalar.distance (sourceCoefficient 11 40 1 2) v1040_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1040_mb : Scalar.QComplex := ((-549552638408724718222129 : Int)/10^30,(-431477153103984906465322825 : Int)/10^30)
theorem v1040_mb_checked : Scalar.distance (sourceCoefficient 11 40 3 1) v1040_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1040_mg : Scalar.QComplex := ((-93086352461155663427365 : Int)/10^30,(118559813021071244246 : Int)/10^30)
theorem v1040_mg_checked : Scalar.distance (sourceCoefficient 11 40 3 2) v1040_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1040_upper : Scalar.QComplex := ((999997717453002946315413834708 : Int)/10^30,(-2136606838912244849958961523 : Int)/10^30)
theorem v1040_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 40 5) 1) 14) v1040_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1040 : Material (11 : Basis) (40 : Basis) where
  plus := ![v1040_pa,v1040_pb,v1040_pg]
  minus := ![(Primitive.Addresses.material1040 1).one,v1040_mb,v1040_mg]
  upper := v1040_upper
  lower := (Primitive.Addresses.material1040 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1040_pa_checked.trans (by decide +kernel)
    · exact v1040_pb_checked.trans (by decide +kernel)
    · exact v1040_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 40 Primitive.Addresses.material1040
    · exact v1040_mb_checked.trans (by decide +kernel)
    · exact v1040_mg_checked.trans (by decide +kernel)
  upper_error := v1040_upper_checked
  lower_error := reuse_lower_error 11 40 Primitive.Addresses.material1040

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
