import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B159
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B160

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3825_pa : Scalar.QComplex := ((999998695173752055385586975847 : Int)/10^30,(-1615441361770117454989087500 : Int)/10^30)
theorem v3825_pa_checked : Scalar.distance (sourceCoefficient 54 73 1 0) v3825_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3825_pb : Scalar.QComplex := ((-697026617517914413960657 : Int)/10^30,(-431476947733666719989000210 : Int)/10^30)
theorem v3825_pb_checked : Scalar.distance (sourceCoefficient 54 73 1 1) v3825_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3825_pg : Scalar.QComplex := ((-93086307328210158573351 : Int)/10^30,(150375667286553210035 : Int)/10^30)
theorem v3825_pg_checked : Scalar.distance (sourceCoefficient 54 73 1 2) v3825_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3825_mb : Scalar.QComplex := ((-1069371530876864358590284 : Int)/10^30,(-431476185572501603604976319 : Int)/10^30)
theorem v3825_mb_checked : Scalar.distance (sourceCoefficient 54 73 3 1) v3825_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3825_mg : Scalar.QComplex := ((-93086142900495486217266 : Int)/10^30,(230704902067414196798 : Int)/10^30)
theorem v3825_mg_checked : Scalar.distance (sourceCoefficient 54 73 3 2) v3825_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3825_upper : Scalar.QComplex := ((999994417687924972818901140792 : Int)/10^30,(-3341345984456901344826025668 : Int)/10^30)
theorem v3825_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 73 5) 1) 14) v3825_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3825 : Material (54 : Basis) (73 : Basis) where
  plus := ![v3825_pa,v3825_pb,v3825_pg]
  minus := ![(Primitive.Addresses.material3825 1).one,v3825_mb,v3825_mg]
  upper := v3825_upper
  lower := (Primitive.Addresses.material3825 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3825_pa_checked.trans (by decide +kernel)
    · exact v3825_pb_checked.trans (by decide +kernel)
    · exact v3825_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 73 Primitive.Addresses.material3825
    · exact v3825_mb_checked.trans (by decide +kernel)
    · exact v3825_mg_checked.trans (by decide +kernel)
  upper_error := v3825_upper_checked
  lower_error := reuse_lower_error 54 73 Primitive.Addresses.material3825

def v3826_pa : Scalar.QComplex := ((999998677939956149531065626423 : Int)/10^30,(-1626074518544023652963778256 : Int)/10^30)
theorem v3826_pa_checked : Scalar.distance (sourceCoefficient 54 74 1 0) v3826_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3826_pb : Scalar.QComplex := ((-701614584581285637439057 : Int)/10^30,(-431476939711777414904665145 : Int)/10^30)
theorem v3826_pb_checked : Scalar.distance (sourceCoefficient 54 74 1 1) v3826_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3826_pg : Scalar.QComplex := ((-93086305660777623578380 : Int)/10^30,(151365469774630405507 : Int)/10^30)
theorem v3826_pg_checked : Scalar.distance (sourceCoefficient 54 74 1 2) v3826_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3826_mb : Scalar.QComplex := ((-1073959489309396586117070 : Int)/10^30,(-431476173591406344113188144 : Int)/10^30)
theorem v3826_mb_checked : Scalar.distance (sourceCoefficient 54 74 3 1) v3826_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3826_mg : Scalar.QComplex := ((-93086140378908603922225 : Int)/10^30,(231694702748023510423 : Int)/10^30)
theorem v3826_mg_checked : Scalar.distance (sourceCoefficient 54 74 3 2) v3826_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3826_upper : Scalar.QComplex := ((999994382102290775364093599605 : Int)/10^30,(-3351979095650001290650429909 : Int)/10^30)
theorem v3826_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 74 5) 1) 14) v3826_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3826 : Material (54 : Basis) (74 : Basis) where
  plus := ![v3826_pa,v3826_pb,v3826_pg]
  minus := ![(Primitive.Addresses.material3826 1).one,v3826_mb,v3826_mg]
  upper := v3826_upper
  lower := (Primitive.Addresses.material3826 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3826_pa_checked.trans (by decide +kernel)
    · exact v3826_pb_checked.trans (by decide +kernel)
    · exact v3826_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 74 Primitive.Addresses.material3826
    · exact v3826_mb_checked.trans (by decide +kernel)
    · exact v3826_mg_checked.trans (by decide +kernel)
  upper_error := v3826_upper_checked
  lower_error := reuse_lower_error 54 74 Primitive.Addresses.material3826

def v3827_pa : Scalar.QComplex := ((999998653739708612370607977086 : Int)/10^30,(-1640889627719819129986764105 : Int)/10^30)
theorem v3827_pa_checked : Scalar.distance (sourceCoefficient 54 75 1 0) v3827_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3827_pb : Scalar.QComplex := ((-708006969617087072062525 : Int)/10^30,(-431476928426480024095553249 : Int)/10^30)
theorem v3827_pb_checked : Scalar.distance (sourceCoefficient 54 75 1 1) v3827_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3827_pg : Scalar.QComplex := ((-93086303317082208877085 : Int)/10^30,(152744555229710621744 : Int)/10^30)
theorem v3827_pg_checked : Scalar.distance (sourceCoefficient 54 75 1 2) v3827_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3827_mb : Scalar.QComplex := ((-1080351862226317548141516 : Int)/10^30,(-431476156789772771773995806 : Int)/10^30)
theorem v3827_mb_checked : Scalar.distance (sourceCoefficient 54 75 3 1) v3827_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3827_mg : Scalar.QComplex := ((-93086136845125425854820 : Int)/10^30,(233073785667103597651 : Int)/10^30)
theorem v3827_mg_checked : Scalar.distance (sourceCoefficient 54 75 3 2) v3827_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3827_upper : Scalar.QComplex := ((999994332332544860412138169807 : Int)/10^30,(-3366794140993000135467467077 : Int)/10^30)
theorem v3827_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 75 5) 1) 14) v3827_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3827 : Material (54 : Basis) (75 : Basis) where
  plus := ![v3827_pa,v3827_pb,v3827_pg]
  minus := ![(Primitive.Addresses.material3827 1).one,v3827_mb,v3827_mg]
  upper := v3827_upper
  lower := (Primitive.Addresses.material3827 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3827_pa_checked.trans (by decide +kernel)
    · exact v3827_pb_checked.trans (by decide +kernel)
    · exact v3827_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 75 Primitive.Addresses.material3827
    · exact v3827_mb_checked.trans (by decide +kernel)
    · exact v3827_mg_checked.trans (by decide +kernel)
  upper_error := v3827_upper_checked
  lower_error := reuse_lower_error 54 75 Primitive.Addresses.material3827

def v3828_pa : Scalar.QComplex := ((999998633265892382671778778439 : Int)/10^30,(-1653319795826728591919242455 : Int)/10^30)
theorem v3828_pa_checked : Scalar.distance (sourceCoefficient 54 76 1 0) v3828_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3828_pb : Scalar.QComplex := ((-713370306381877313462525 : Int)/10^30,(-431476918860476060744338292 : Int)/10^30)
theorem v3828_pb_checked : Scalar.distance (sourceCoefficient 54 76 1 1) v3828_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3828_pg : Scalar.QComplex := ((-93086301332286012551759 : Int)/10^30,(153901635055574292509 : Int)/10^30)
theorem v3828_pg_checked : Scalar.distance (sourceCoefficient 54 76 1 2) v3828_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3828_mb : Scalar.QComplex := ((-1085715188739061811863949 : Int)/10^30,(-431476142595454297990182351 : Int)/10^30)
theorem v3828_mb_checked : Scalar.distance (sourceCoefficient 54 76 3 1) v3828_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3828_mg : Scalar.QComplex := ((-93086133861822191780313 : Int)/10^30,(234230863349343842560 : Int)/10^30)
theorem v3828_mg_checked : Scalar.distance (sourceCoefficient 54 76 3 2) v3828_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3828_upper : Scalar.QComplex := ((999994290405416627573721652090 : Int)/10^30,(-3379224255250684909913290874 : Int)/10^30)
theorem v3828_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 76 5) 1) 14) v3828_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3828 : Material (54 : Basis) (76 : Basis) where
  plus := ![v3828_pa,v3828_pb,v3828_pg]
  minus := ![(Primitive.Addresses.material3828 1).one,v3828_mb,v3828_mg]
  upper := v3828_upper
  lower := (Primitive.Addresses.material3828 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3828_pa_checked.trans (by decide +kernel)
    · exact v3828_pb_checked.trans (by decide +kernel)
    · exact v3828_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 76 Primitive.Addresses.material3828
    · exact v3828_mb_checked.trans (by decide +kernel)
    · exact v3828_mg_checked.trans (by decide +kernel)
  upper_error := v3828_upper_checked
  lower_error := reuse_lower_error 54 76 Primitive.Addresses.material3828

def v3829_pa : Scalar.QComplex := ((999998628504004311189919941981 : Int)/10^30,(-1656197485318811239039479742 : Int)/10^30)
theorem v3829_pa_checked : Scalar.distance (sourceCoefficient 54 77 1 0) v3829_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3829_pb : Scalar.QComplex := ((-714611964388456954680775 : Int)/10^30,(-431476916633193434772514417 : Int)/10^30)
theorem v3829_pb_checked : Scalar.distance (sourceCoefficient 54 77 1 1) v3829_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3829_pg : Scalar.QComplex := ((-93086300870396824857683 : Int)/10^30,(154169508862045552805 : Int)/10^30)
theorem v3829_pg_checked : Scalar.distance (sourceCoefficient 54 77 1 2) v3829_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3829_mb : Scalar.QComplex := ((-1086956844361270837530353 : Int)/10^30,(-431476139296677563859928277 : Int)/10^30)
theorem v3829_mb_checked : Scalar.distance (sourceCoefficient 54 77 3 1) v3829_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3829_mg : Scalar.QComplex := ((-93086133168770145672378 : Int)/10^30,(234498736657483876006 : Int)/10^30)
theorem v3829_mg_checked : Scalar.distance (sourceCoefficient 54 77 3 2) v3829_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3829_upper : Scalar.QComplex := ((999994280676904646981543378805 : Int)/10^30,(-3382101932238200279463576073 : Int)/10^30)
theorem v3829_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 77 5) 1) 14) v3829_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3829 : Material (54 : Basis) (77 : Basis) where
  plus := ![v3829_pa,v3829_pb,v3829_pg]
  minus := ![(Primitive.Addresses.material3829 1).one,v3829_mb,v3829_mg]
  upper := v3829_upper
  lower := (Primitive.Addresses.material3829 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3829_pa_checked.trans (by decide +kernel)
    · exact v3829_pb_checked.trans (by decide +kernel)
    · exact v3829_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 77 Primitive.Addresses.material3829
    · exact v3829_mb_checked.trans (by decide +kernel)
    · exact v3829_mg_checked.trans (by decide +kernel)
  upper_error := v3829_upper_checked
  lower_error := reuse_lower_error 54 77 Primitive.Addresses.material3829

def v3830_pa : Scalar.QComplex := ((999998599702830406005721820069 : Int)/10^30,(-1673497050596691485967139481 : Int)/10^30)
theorem v3830_pa_checked : Scalar.distance (sourceCoefficient 54 78 1 0) v3830_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3830_pb : Scalar.QComplex := ((-722076335932218002319967 : Int)/10^30,(-431476903143217355020664350 : Int)/10^30)
theorem v3830_pb_checked : Scalar.distance (sourceCoefficient 54 78 1 1) v3830_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3830_pg : Scalar.QComplex := ((-93086298074742170349469 : Int)/10^30,(155779863417147325882 : Int)/10^30)
theorem v3830_pg_checked : Scalar.distance (sourceCoefficient 54 78 1 2) v3830_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3830_mb : Scalar.QComplex := ((-1094421201484463429938043 : Int)/10^30,(-431476119365290047591549257 : Int)/10^30)
theorem v3830_mb_checked : Scalar.distance (sourceCoefficient 54 78 3 1) v3830_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3830_mg : Scalar.QComplex := ((-93086128983453078738138 : Int)/10^30,(236109088200452996151 : Int)/10^30)
theorem v3830_mg_checked : Scalar.distance (sourceCoefficient 54 78 3 2) v3830_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3830_upper : Scalar.QComplex := ((999994222018293372443842953511 : Int)/10^30,(-3399401422042196856415383885 : Int)/10^30)
theorem v3830_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 78 5) 1) 14) v3830_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3830 : Material (54 : Basis) (78 : Basis) where
  plus := ![v3830_pa,v3830_pb,v3830_pg]
  minus := ![(Primitive.Addresses.material3830 1).one,v3830_mb,v3830_mg]
  upper := v3830_upper
  lower := (Primitive.Addresses.material3830 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3830_pa_checked.trans (by decide +kernel)
    · exact v3830_pb_checked.trans (by decide +kernel)
    · exact v3830_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 78 Primitive.Addresses.material3830
    · exact v3830_mb_checked.trans (by decide +kernel)
    · exact v3830_mg_checked.trans (by decide +kernel)
  upper_error := v3830_upper_checked
  lower_error := reuse_lower_error 54 78 Primitive.Addresses.material3830

def v3831_pa : Scalar.QComplex := ((999998590354049789769332196114 : Int)/10^30,(-1679074123830975006876790937 : Int)/10^30)
theorem v3831_pa_checked : Scalar.distance (sourceCoefficient 54 79 1 0) v3831_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3831_pb : Scalar.QComplex := ((-724482716998831542718134 : Int)/10^30,(-431476898757588088383842163 : Int)/10^30)
theorem v3831_pb_checked : Scalar.distance (sourceCoefficient 54 79 1 1) v3831_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3831_pg : Scalar.QComplex := ((-93086297166544731714067 : Int)/10^30,(156299013181856820431 : Int)/10^30)
theorem v3831_pg_checked : Scalar.distance (sourceCoefficient 54 79 1 2) v3831_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3831_mb : Scalar.QComplex := ((-1096827577870470786490521 : Int)/10^30,(-431476112903063932817459409 : Int)/10^30)
theorem v3831_mb_checked : Scalar.distance (sourceCoefficient 54 79 3 1) v3831_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3831_mg : Scalar.QComplex := ((-93086127627253112959290 : Int)/10^30,(236628236988125821134 : Int)/10^30)
theorem v3831_mg_checked : Scalar.distance (sourceCoefficient 54 79 3 2) v3831_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3831_upper : Scalar.QComplex := ((999994203044004225876203499488 : Int)/10^30,(-3404978470834937695030522705 : Int)/10^30)
theorem v3831_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 79 5) 1) 14) v3831_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3831 : Material (54 : Basis) (79 : Basis) where
  plus := ![v3831_pa,v3831_pb,v3831_pg]
  minus := ![(Primitive.Addresses.material3831 1).one,v3831_mb,v3831_mg]
  upper := v3831_upper
  lower := (Primitive.Addresses.material3831 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3831_pa_checked.trans (by decide +kernel)
    · exact v3831_pb_checked.trans (by decide +kernel)
    · exact v3831_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 79 Primitive.Addresses.material3831
    · exact v3831_mb_checked.trans (by decide +kernel)
    · exact v3831_mg_checked.trans (by decide +kernel)
  upper_error := v3831_upper_checked
  lower_error := reuse_lower_error 54 79 Primitive.Addresses.material3831

def v3832_pa : Scalar.QComplex := ((999998575688087823067467791444 : Int)/10^30,(-1687786063365094235931561515 : Int)/10^30)
theorem v3832_pa_checked : Scalar.distance (sourceCoefficient 54 80 1 0) v3832_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3832_pb : Scalar.QComplex := ((-728241722007309864013295 : Int)/10^30,(-431476891870993331338989300 : Int)/10^30)
theorem v3832_pb_checked : Scalar.distance (sourceCoefficient 54 80 1 1) v3832_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3832_pg : Scalar.QComplex := ((-93086295741090968582024 : Int)/10^30,(157109976415705793934 : Int)/10^30)
theorem v3832_pg_checked : Scalar.distance (sourceCoefficient 54 80 1 2) v3832_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3832_mb : Scalar.QComplex := ((-1100586575536478633497912 : Int)/10^30,(-431476102772619716950672645 : Int)/10^30)
theorem v3832_mb_checked : Scalar.distance (sourceCoefficient 54 80 3 1) v3832_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3832_mg : Scalar.QComplex := ((-93086125501975134205368 : Int)/10^30,(237439198689913722295 : Int)/10^30)
theorem v3832_mg_checked : Scalar.distance (sourceCoefficient 54 80 3 2) v3832_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3832_upper : Scalar.QComplex := ((999994173342046807492844600540 : Int)/10^30,(-3413690372081526495469661338 : Int)/10^30)
theorem v3832_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 80 5) 1) 14) v3832_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3832 : Material (54 : Basis) (80 : Basis) where
  plus := ![v3832_pa,v3832_pb,v3832_pg]
  minus := ![(Primitive.Addresses.material3832 1).one,v3832_mb,v3832_mg]
  upper := v3832_upper
  lower := (Primitive.Addresses.material3832 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3832_pa_checked.trans (by decide +kernel)
    · exact v3832_pb_checked.trans (by decide +kernel)
    · exact v3832_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 80 Primitive.Addresses.material3832
    · exact v3832_mb_checked.trans (by decide +kernel)
    · exact v3832_mg_checked.trans (by decide +kernel)
  upper_error := v3832_upper_checked
  lower_error := reuse_lower_error 54 80 Primitive.Addresses.material3832

def v3833_pa : Scalar.QComplex := ((999998531069786399350338072696 : Int)/10^30,(-1714018164852790261993138460 : Int)/10^30)
theorem v3833_pa_checked : Scalar.distance (sourceCoefficient 54 81 1 0) v3833_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3833_pb : Scalar.QComplex := ((-739560280749898823328951 : Int)/10^30,(-431476870871421160195605590 : Int)/10^30)
theorem v3833_pb_checked : Scalar.distance (sourceCoefficient 54 81 1 1) v3833_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3833_pg : Scalar.QComplex := ((-93086291399200834136771 : Int)/10^30,(159551828727512140703 : Int)/10^30)
theorem v3833_pg_checked : Scalar.distance (sourceCoefficient 54 81 1 2) v3833_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3833_mb : Scalar.QComplex := ((-1111905111942965891183465 : Int)/10^30,(-431476072005648939015717042 : Int)/10^30)
theorem v3833_mb_checked : Scalar.distance (sourceCoefficient 54 81 3 1) v3833_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3833_mg : Scalar.QComplex := ((-93086119052878048300957 : Int)/10^30,(239881046345651220662 : Int)/10^30)
theorem v3833_mg_checked : Scalar.distance (sourceCoefficient 54 81 3 2) v3833_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3833_upper : Scalar.QComplex := ((999994083449584427388427798770 : Int)/10^30,(-3439922357492448278058221702 : Int)/10^30)
theorem v3833_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 81 5) 1) 14) v3833_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3833 : Material (54 : Basis) (81 : Basis) where
  plus := ![v3833_pa,v3833_pb,v3833_pg]
  minus := ![(Primitive.Addresses.material3833 1).one,v3833_mb,v3833_mg]
  upper := v3833_upper
  lower := (Primitive.Addresses.material3833 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3833_pa_checked.trans (by decide +kernel)
    · exact v3833_pb_checked.trans (by decide +kernel)
    · exact v3833_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 81 Primitive.Addresses.material3833
    · exact v3833_mb_checked.trans (by decide +kernel)
    · exact v3833_mg_checked.trans (by decide +kernel)
  upper_error := v3833_upper_checked
  lower_error := reuse_lower_error 54 81 Primitive.Addresses.material3833

def v3834_pa : Scalar.QComplex := ((999998513982597773628774220341 : Int)/10^30,(-1723958409070538665455001759 : Int)/10^30)
theorem v3834_pa_checked : Scalar.distance (sourceCoefficient 54 82 1 0) v3834_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3834_pb : Scalar.QComplex := ((-743849271334555489051303 : Int)/10^30,(-431476862810533064558777995 : Int)/10^30)
theorem v3834_pb_checked : Scalar.distance (sourceCoefficient 54 82 1 1) v3834_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3834_pg : Scalar.QComplex := ((-93086289734385097569445 : Int)/10^30,(160477130428578224268 : Int)/10^30)
theorem v3834_pg_checked : Scalar.distance (sourceCoefficient 54 82 1 2) v3834_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3834_mb : Scalar.QComplex := ((-1116194093974451968073243 : Int)/10^30,(-431476060243558139222389603 : Int)/10^30)
theorem v3834_mb_checked : Scalar.distance (sourceCoefficient 54 82 3 1) v3834_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3834_mg : Scalar.QComplex := ((-93086116589569237642187 : Int)/10^30,(240806346265524192402 : Int)/10^30)
theorem v3834_mg_checked : Scalar.distance (sourceCoefficient 54 82 3 2) v3834_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3834_upper : Scalar.QComplex := ((999994049206461503104553951719 : Int)/10^30,(-3449862557414433151941210031 : Int)/10^30)
theorem v3834_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 82 5) 1) 14) v3834_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3834 : Material (54 : Basis) (82 : Basis) where
  plus := ![v3834_pa,v3834_pb,v3834_pg]
  minus := ![(Primitive.Addresses.material3834 1).one,v3834_mb,v3834_mg]
  upper := v3834_upper
  lower := (Primitive.Addresses.material3834 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3834_pa_checked.trans (by decide +kernel)
    · exact v3834_pb_checked.trans (by decide +kernel)
    · exact v3834_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 82 Primitive.Addresses.material3834
    · exact v3834_mb_checked.trans (by decide +kernel)
    · exact v3834_mg_checked.trans (by decide +kernel)
  upper_error := v3834_upper_checked
  lower_error := reuse_lower_error 54 82 Primitive.Addresses.material3834

def v3835_pa : Scalar.QComplex := ((999998490498806215712016822657 : Int)/10^30,(-1737527009566965531654274663 : Int)/10^30)
theorem v3835_pa_checked : Scalar.distance (sourceCoefficient 54 83 1 0) v3835_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3835_pb : Scalar.QComplex := ((-749703815537457034329369 : Int)/10^30,(-431476851715529213550739317 : Int)/10^30)
theorem v3835_pb_checked : Scalar.distance (sourceCoefficient 54 83 1 1) v3835_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3835_pg : Scalar.QComplex := ((-93086287444562694423798 : Int)/10^30,(161740182802241011078 : Int)/10^30)
theorem v3835_pg_checked : Scalar.distance (sourceCoefficient 54 83 1 2) v3835_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3835_mb : Scalar.QComplex := ((-1122048626422950517726728 : Int)/10^30,(-431476044096350451169996268 : Int)/10^30)
theorem v3835_mb_checked : Scalar.distance (sourceCoefficient 54 83 3 1) v3835_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3835_mg : Scalar.QComplex := ((-93086113209790374398297 : Int)/10^30,(242069396192881252010 : Int)/10^30)
theorem v3835_mg_checked : Scalar.distance (sourceCoefficient 54 83 3 2) v3835_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3835_upper : Scalar.QComplex := ((999994002304531398525459589978 : Int)/10^30,(-3463431097171129662454705966 : Int)/10^30)
theorem v3835_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 83 5) 1) 14) v3835_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3835 : Material (54 : Basis) (83 : Basis) where
  plus := ![v3835_pa,v3835_pb,v3835_pg]
  minus := ![(Primitive.Addresses.material3835 1).one,v3835_mb,v3835_mg]
  upper := v3835_upper
  lower := (Primitive.Addresses.material3835 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3835_pa_checked.trans (by decide +kernel)
    · exact v3835_pb_checked.trans (by decide +kernel)
    · exact v3835_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 83 Primitive.Addresses.material3835
    · exact v3835_mb_checked.trans (by decide +kernel)
    · exact v3835_mg_checked.trans (by decide +kernel)
  upper_error := v3835_upper_checked
  lower_error := reuse_lower_error 54 83 Primitive.Addresses.material3835

def v3836_pa : Scalar.QComplex := ((999998428826369538041889440283 : Int)/10^30,(-1772666012631070659268521048 : Int)/10^30)
theorem v3836_pa_checked : Scalar.distance (sourceCoefficient 54 84 1 0) v3836_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3836_pb : Scalar.QComplex := ((-764865500202832383787445 : Int)/10^30,(-431476822490143874983817113 : Int)/10^30)
theorem v3836_pb_checked : Scalar.distance (sourceCoefficient 54 84 1 1) v3836_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3836_pg : Scalar.QComplex := ((-93086281421604867071263 : Int)/10^30,(165011146579452249265 : Int)/10^30)
theorem v3836_pg_checked : Scalar.distance (sourceCoefficient 54 84 1 2) v3836_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3836_mb : Scalar.QComplex := ((-1137210280222746458355688 : Int)/10^30,(-431476001787124985259262911 : Int)/10^30)
theorem v3836_mb_checked : Scalar.distance (sourceCoefficient 54 84 3 1) v3836_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3836_mg : Scalar.QComplex := ((-93086104364140368674722 : Int)/10^30,(245340353554621844458 : Int)/10^30)
theorem v3836_mg_checked : Scalar.distance (sourceCoefficient 54 84 3 2) v3836_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3836_upper : Scalar.QComplex := ((999993879985455071516122213355 : Int)/10^30,(-3498569941458786617432553369 : Int)/10^30)
theorem v3836_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 84 5) 1) 14) v3836_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3836 : Material (54 : Basis) (84 : Basis) where
  plus := ![v3836_pa,v3836_pb,v3836_pg]
  minus := ![(Primitive.Addresses.material3836 1).one,v3836_mb,v3836_mg]
  upper := v3836_upper
  lower := (Primitive.Addresses.material3836 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3836_pa_checked.trans (by decide +kernel)
    · exact v3836_pb_checked.trans (by decide +kernel)
    · exact v3836_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 84 Primitive.Addresses.material3836
    · exact v3836_mb_checked.trans (by decide +kernel)
    · exact v3836_mg_checked.trans (by decide +kernel)
  upper_error := v3836_upper_checked
  lower_error := reuse_lower_error 54 84 Primitive.Addresses.material3836

def v3837_pa : Scalar.QComplex := ((999998285560051050421563009351 : Int)/10^30,(-1851722700242889585921581292 : Int)/10^30)
theorem v3837_pa_checked : Scalar.distance (sourceCoefficient 54 85 1 0) v3837_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3837_pb : Scalar.QComplex := ((-798976670067836954394603 : Int)/10^30,(-431476754141165035801475861 : Int)/10^30)
theorem v3837_pb_checked : Scalar.distance (sourceCoefficient 54 85 1 1) v3837_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3837_pg : Scalar.QComplex := ((-93086267380767478326291 : Int)/10^30,(172370249908288821170 : Int)/10^30)
theorem v3837_pg_checked : Scalar.distance (sourceCoefficient 54 85 1 2) v3837_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3837_mb : Scalar.QComplex := ((-1171321378404513116264559 : Int)/10^30,(-431475904001768312086711328 : Int)/10^30)
theorem v3837_mb_checked : Scalar.distance (sourceCoefficient 54 85 3 1) v3837_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3837_mg : Scalar.QComplex := ((-93086083972733476899483 : Int)/10^30,(252699442026717628755 : Int)/10^30)
theorem v3837_mg_checked : Scalar.distance (sourceCoefficient 54 85 3 2) v3837_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3837_upper : Scalar.QComplex := ((999993600274679110924286796863 : Int)/10^30,(-3577626264060287306413224208 : Int)/10^30)
theorem v3837_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 85 5) 1) 14) v3837_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3837 : Material (54 : Basis) (85 : Basis) where
  plus := ![v3837_pa,v3837_pb,v3837_pg]
  minus := ![(Primitive.Addresses.material3837 1).one,v3837_mb,v3837_mg]
  upper := v3837_upper
  lower := (Primitive.Addresses.material3837 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3837_pa_checked.trans (by decide +kernel)
    · exact v3837_pb_checked.trans (by decide +kernel)
    · exact v3837_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 85 Primitive.Addresses.material3837
    · exact v3837_mb_checked.trans (by decide +kernel)
    · exact v3837_mg_checked.trans (by decide +kernel)
  upper_error := v3837_upper_checked
  lower_error := reuse_lower_error 54 85 Primitive.Addresses.material3837

def v3838_pa : Scalar.QComplex := ((999998258446978755903031944004 : Int)/10^30,(-1866307319141536274672320923 : Int)/10^30)
theorem v3838_pa_checked : Scalar.distance (sourceCoefficient 54 86 1 0) v3838_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3838_pb : Scalar.QComplex := ((-805269602446917582451251 : Int)/10^30,(-431476741139082954236914499 : Int)/10^30)
theorem v3838_pb_checked : Scalar.distance (sourceCoefficient 54 86 1 1) v3838_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3838_pg : Scalar.QComplex := ((-93086264716311324729466 : Int)/10^30,(173727879707912146802 : Int)/10^30)
theorem v3838_pg_checked : Scalar.distance (sourceCoefficient 54 86 1 2) v3838_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3838_mb : Scalar.QComplex := ((-1177614297220236174020515 : Int)/10^30,(-431475885569173851798143220 : Int)/10^30)
theorem v3838_mb_checked : Scalar.distance (sourceCoefficient 54 86 3 1) v3838_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3838_mg : Scalar.QComplex := ((-93086080136704943702878 : Int)/10^30,(254057069021527675336 : Int)/10^30)
theorem v3838_mg_checked : Scalar.distance (sourceCoefficient 54 86 3 2) v3838_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3838_upper : Scalar.QComplex := ((999993547989918085368774513077 : Int)/10^30,(-3592210814442154273678995805 : Int)/10^30)
theorem v3838_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 86 5) 1) 14) v3838_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3838 : Material (54 : Basis) (86 : Basis) where
  plus := ![v3838_pa,v3838_pb,v3838_pg]
  minus := ![(Primitive.Addresses.material3838 1).one,v3838_mb,v3838_mg]
  upper := v3838_upper
  lower := (Primitive.Addresses.material3838 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3838_pa_checked.trans (by decide +kernel)
    · exact v3838_pb_checked.trans (by decide +kernel)
    · exact v3838_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 86 Primitive.Addresses.material3838
    · exact v3838_mb_checked.trans (by decide +kernel)
    · exact v3838_mg_checked.trans (by decide +kernel)
  upper_error := v3838_upper_checked
  lower_error := reuse_lower_error 54 86 Primitive.Addresses.material3838

def v3839_pa : Scalar.QComplex := ((999998256644114100708440470211 : Int)/10^30,(-1867273073899165456328354658 : Int)/10^30)
theorem v3839_pa_checked : Scalar.distance (sourceCoefficient 54 87 1 0) v3839_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3839_pb : Scalar.QComplex := ((-805686303725009517411042 : Int)/10^30,(-431476740273799658604097191 : Int)/10^30)
theorem v3839_pb_checked : Scalar.distance (sourceCoefficient 54 87 1 1) v3839_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3839_pg : Scalar.QComplex := ((-93086264539062630338127 : Int)/10^30,(173817778349893320048 : Int)/10^30)
theorem v3839_pg_checked : Scalar.distance (sourceCoefficient 54 87 1 2) v3839_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3839_mb : Scalar.QComplex := ((-1178030997596470665739314 : Int)/10^30,(-431475884344296442885384247 : Int)/10^30)
theorem v3839_mb_checked : Scalar.distance (sourceCoefficient 54 87 3 1) v3839_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3839_mg : Scalar.QComplex := ((-93086079881877836164109 : Int)/10^30,(254146967477077835327 : Int)/10^30)
theorem v3839_mg_checked : Scalar.distance (sourceCoefficient 54 87 3 2) v3839_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3839_upper : Scalar.QComplex := ((999993544520251016248560200553 : Int)/10^30,(-3593176564649824349107343845 : Int)/10^30)
theorem v3839_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 87 5) 1) 14) v3839_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3839 : Material (54 : Basis) (87 : Basis) where
  plus := ![v3839_pa,v3839_pb,v3839_pg]
  minus := ![(Primitive.Addresses.material3839 1).one,v3839_mb,v3839_mg]
  upper := v3839_upper
  lower := (Primitive.Addresses.material3839 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3839_pa_checked.trans (by decide +kernel)
    · exact v3839_pb_checked.trans (by decide +kernel)
    · exact v3839_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 87 Primitive.Addresses.material3839
    · exact v3839_mb_checked.trans (by decide +kernel)
    · exact v3839_mg_checked.trans (by decide +kernel)
  upper_error := v3839_upper_checked
  lower_error := reuse_lower_error 54 87 Primitive.Addresses.material3839

def v3840_pa : Scalar.QComplex := ((999998234616597795386585838206 : Int)/10^30,(-1879032646824069964590876395 : Int)/10^30)
theorem v3840_pa_checked : Scalar.distance (sourceCoefficient 54 88 1 0) v3840_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3840_pb : Scalar.QComplex := ((-810760292743760856794753 : Int)/10^30,(-431476729694578104229844070 : Int)/10^30)
theorem v3840_pb_checked : Scalar.distance (sourceCoefficient 54 88 1 1) v3840_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3840_pg : Scalar.QComplex := ((-93086262372657077963079 : Int)/10^30,(174912434756562818626 : Int)/10^30)
theorem v3840_pg_checked : Scalar.distance (sourceCoefficient 54 88 1 2) v3840_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3840_mb : Scalar.QComplex := ((-1183104975596552269714424 : Int)/10^30,(-431475869386454828438599825 : Int)/10^30)
theorem v3840_mb_checked : Scalar.distance (sourceCoefficient 54 88 3 1) v3840_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3840_mg : Scalar.QComplex := ((-93086076770833912979479 : Int)/10^30,(255241621606646305017 : Int)/10^30)
theorem v3840_mg_checked : Scalar.distance (sourceCoefficient 54 88 3 2) v3840_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3840_upper : Scalar.QComplex := ((999993502196811470061733128443 : Int)/10^30,(-3604936082042731539880437757 : Int)/10^30)
theorem v3840_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 88 5) 1) 14) v3840_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3840 : Material (54 : Basis) (88 : Basis) where
  plus := ![v3840_pa,v3840_pb,v3840_pg]
  minus := ![(Primitive.Addresses.material3840 1).one,v3840_mb,v3840_mg]
  upper := v3840_upper
  lower := (Primitive.Addresses.material3840 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3840_pa_checked.trans (by decide +kernel)
    · exact v3840_pb_checked.trans (by decide +kernel)
    · exact v3840_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 88 Primitive.Addresses.material3840
    · exact v3840_mb_checked.trans (by decide +kernel)
    · exact v3840_mg_checked.trans (by decide +kernel)
  upper_error := v3840_upper_checked
  lower_error := reuse_lower_error 54 88 Primitive.Addresses.material3840

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
