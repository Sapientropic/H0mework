import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B158
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B159

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3809_pa : Scalar.QComplex := ((999999195562118759542711564971 : Int)/10^30,(-1268414409946768856966533454 : Int)/10^30)
theorem v3809_pa_checked : Scalar.distance (sourceCoefficient 54 57 1 0) v3809_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3809_pb : Scalar.QComplex := ((-547292305119015109835504 : Int)/10^30,(-431477173835734634901568307 : Int)/10^30)
theorem v3809_pb_checked : Scalar.distance (sourceCoefficient 54 57 1 1) v3809_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3809_pg : Scalar.QComplex := ((-93086355007384534630836 : Int)/10^30,(118072169042512605083 : Int)/10^30)
theorem v3809_pg_checked : Scalar.distance (sourceCoefficient 54 57 1 2) v3809_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3809_mb : Scalar.QComplex := ((-919637469346794108163726 : Int)/10^30,(-431476540888453147544933408 : Int)/10^30)
theorem v3809_mb_checked : Scalar.distance (sourceCoefficient 54 57 3 1) v3809_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3809_mg : Scalar.QComplex := ((-93086218456116198193477 : Int)/10^30,(198401456996422427144 : Int)/10^30)
theorem v3809_mg_checked : Scalar.distance (sourceCoefficient 54 57 3 2) v3809_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3809_upper : Scalar.QComplex := ((999995517012583215238026373400 : Int)/10^30,(-2994320413114358891712728692 : Int)/10^30)
theorem v3809_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 57 5) 1) 14) v3809_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3809 : Material (54 : Basis) (57 : Basis) where
  plus := ![v3809_pa,v3809_pb,v3809_pg]
  minus := ![(Primitive.Addresses.material3809 1).one,v3809_mb,v3809_mg]
  upper := v3809_upper
  lower := (Primitive.Addresses.material3809 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3809_pa_checked.trans (by decide +kernel)
    · exact v3809_pb_checked.trans (by decide +kernel)
    · exact v3809_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 57 Primitive.Addresses.material3809
    · exact v3809_mb_checked.trans (by decide +kernel)
    · exact v3809_mg_checked.trans (by decide +kernel)
  upper_error := v3809_upper_checked
  lower_error := reuse_lower_error 54 57 Primitive.Addresses.material3809

def v3810_pa : Scalar.QComplex := ((999999187435833133972119498914 : Int)/10^30,(-1274804955070198370587303719 : Int)/10^30)
theorem v3810_pa_checked : Scalar.distance (sourceCoefficient 54 58 1 0) v3810_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3810_pb : Scalar.QComplex := ((-550049681646491334344859 : Int)/10^30,(-431477170298213218067704757 : Int)/10^30)
theorem v3810_pb_checked : Scalar.distance (sourceCoefficient 54 58 1 1) v3810_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3810_pg : Scalar.QComplex := ((-93086354247570815442320 : Int)/10^30,(118667042068809255729 : Int)/10^30)
theorem v3810_pg_checked : Scalar.distance (sourceCoefficient 54 58 1 2) v3810_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3810_mb : Scalar.QComplex := ((-922394841794851374483548 : Int)/10^30,(-431476534971441292308720362 : Int)/10^30)
theorem v3810_mb_checked : Scalar.distance (sourceCoefficient 54 58 3 1) v3810_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3810_mg : Scalar.QComplex := ((-93086217182954132310860 : Int)/10^30,(198996329145535644139 : Int)/10^30)
theorem v3810_mg_checked : Scalar.distance (sourceCoefficient 54 58 3 2) v3810_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3810_upper : Scalar.QComplex := ((999995497856808555500824972002 : Int)/10^30,(-3000710934694590351286597825 : Int)/10^30)
theorem v3810_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 58 5) 1) 14) v3810_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3810 : Material (54 : Basis) (58 : Basis) where
  plus := ![v3810_pa,v3810_pb,v3810_pg]
  minus := ![(Primitive.Addresses.material3810 1).one,v3810_mb,v3810_mg]
  upper := v3810_upper
  lower := (Primitive.Addresses.material3810 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3810_pa_checked.trans (by decide +kernel)
    · exact v3810_pb_checked.trans (by decide +kernel)
    · exact v3810_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 58 Primitive.Addresses.material3810
    · exact v3810_mb_checked.trans (by decide +kernel)
    · exact v3810_mg_checked.trans (by decide +kernel)
  upper_error := v3810_upper_checked
  lower_error := reuse_lower_error 54 58 Primitive.Addresses.material3810

def v3811_pa : Scalar.QComplex := ((999999164888421555599737550002 : Int)/10^30,(-1292370867621772133933325038 : Int)/10^30)
theorem v3811_pa_checked : Scalar.distance (sourceCoefficient 54 59 1 0) v3811_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3811_pb : Scalar.QComplex := ((-557628977896628333464271 : Int)/10^30,(-431477160453456694234473663 : Int)/10^30)
theorem v3811_pb_checked : Scalar.distance (sourceCoefficient 54 59 1 1) v3811_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3811_pg : Scalar.QComplex := ((-93086352136193957567619 : Int)/10^30,(120302190139750684755 : Int)/10^30)
theorem v3811_pg_checked : Scalar.distance (sourceCoefficient 54 59 1 2) v3811_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3811_mb : Scalar.QComplex := ((-929974126727288500032558 : Int)/10^30,(-431476518586097129091311160 : Int)/10^30)
theorem v3811_mb_checked : Scalar.distance (sourceCoefficient 54 59 3 1) v3811_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3811_mg : Scalar.QComplex := ((-93086213660518919711114 : Int)/10^30,(200631474785613580933 : Int)/10^30)
theorem v3811_mg_checked : Scalar.distance (sourceCoefficient 54 59 3 2) v3811_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3811_upper : Scalar.QComplex := ((999995444992259061971483882345 : Int)/10^30,(-3018276782169013907029557813 : Int)/10^30)
theorem v3811_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 59 5) 1) 14) v3811_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3811 : Material (54 : Basis) (59 : Basis) where
  plus := ![v3811_pa,v3811_pb,v3811_pg]
  minus := ![(Primitive.Addresses.material3811 1).one,v3811_mb,v3811_mg]
  upper := v3811_upper
  lower := (Primitive.Addresses.material3811 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3811_pa_checked.trans (by decide +kernel)
    · exact v3811_pb_checked.trans (by decide +kernel)
    · exact v3811_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 59 Primitive.Addresses.material3811
    · exact v3811_mb_checked.trans (by decide +kernel)
    · exact v3811_mg_checked.trans (by decide +kernel)
  upper_error := v3811_upper_checked
  lower_error := reuse_lower_error 54 59 Primitive.Addresses.material3811

def v3812_pa : Scalar.QComplex := ((999999138494595241198281309136 : Int)/10^30,(-1312634780632465569880350379 : Int)/10^30)
theorem v3812_pa_checked : Scalar.distance (sourceCoefficient 54 60 1 0) v3812_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3812_pb : Scalar.QComplex := ((-566372400595793743842711 : Int)/10^30,(-431477148876106332863551122 : Int)/10^30)
theorem v3812_pb_checked : Scalar.distance (sourceCoefficient 54 60 1 1) v3812_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3812_pg : Scalar.QComplex := ((-93086349658898759745041 : Int)/10^30,(122188485430426157330 : Int)/10^30)
theorem v3812_pg_checked : Scalar.distance (sourceCoefficient 54 60 1 2) v3812_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3812_mb : Scalar.QComplex := ((-938717536180146107994994 : Int)/10^30,(-431476499463571078257520444 : Int)/10^30)
theorem v3812_mb_checked : Scalar.distance (sourceCoefficient 54 60 3 1) v3812_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3812_mg : Scalar.QComplex := ((-93086209555436764032015 : Int)/10^30,(202517767236140926348 : Int)/10^30)
theorem v3812_mg_checked : Scalar.distance (sourceCoefficient 54 60 3 2) v3812_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3812_upper : Scalar.QComplex := ((999995383624796529445117046841 : Int)/10^30,(-3038540619445639490544642798 : Int)/10^30)
theorem v3812_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 60 5) 1) 14) v3812_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3812 : Material (54 : Basis) (60 : Basis) where
  plus := ![v3812_pa,v3812_pb,v3812_pg]
  minus := ![(Primitive.Addresses.material3812 1).one,v3812_mb,v3812_mg]
  upper := v3812_upper
  lower := (Primitive.Addresses.material3812 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3812_pa_checked.trans (by decide +kernel)
    · exact v3812_pb_checked.trans (by decide +kernel)
    · exact v3812_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 60 Primitive.Addresses.material3812
    · exact v3812_mb_checked.trans (by decide +kernel)
    · exact v3812_mg_checked.trans (by decide +kernel)
  upper_error := v3812_upper_checked
  lower_error := reuse_lower_error 54 60 Primitive.Addresses.material3812

def v3813_pa : Scalar.QComplex := ((999999130786261667400368378602 : Int)/10^30,(-1318494111148273713483361882 : Int)/10^30)
theorem v3813_pa_checked : Scalar.distance (sourceCoefficient 54 61 1 0) v3813_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3813_pb : Scalar.QComplex := ((-568900569912537825222804 : Int)/10^30,(-431477145484474593421345718 : Int)/10^30)
theorem v3813_pb_checked : Scalar.distance (sourceCoefficient 54 61 1 1) v3813_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3813_pg : Scalar.QComplex := ((-93086348934274902591213 : Int)/10^30,(122733909580135210077 : Int)/10^30)
theorem v3813_pg_checked : Scalar.distance (sourceCoefficient 54 61 1 2) v3813_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3813_mb : Scalar.QComplex := ((-941245701628711771989996 : Int)/10^30,(-431476493890244345843851148 : Int)/10^30)
theorem v3813_mb_checked : Scalar.distance (sourceCoefficient 54 61 3 1) v3813_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3813_mg : Scalar.QComplex := ((-93086208360136700481661 : Int)/10^30,(203063190557445888168 : Int)/10^30)
theorem v3813_mg_checked : Scalar.distance (sourceCoefficient 54 61 3 2) v3813_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3813_upper : Scalar.QComplex := ((999995365803801520331841659757 : Int)/10^30,(-3044399927930778662347245245 : Int)/10^30)
theorem v3813_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 61 5) 1) 14) v3813_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3813 : Material (54 : Basis) (61 : Basis) where
  plus := ![v3813_pa,v3813_pb,v3813_pg]
  minus := ![(Primitive.Addresses.material3813 1).one,v3813_mb,v3813_mg]
  upper := v3813_upper
  lower := (Primitive.Addresses.material3813 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3813_pa_checked.trans (by decide +kernel)
    · exact v3813_pb_checked.trans (by decide +kernel)
    · exact v3813_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 61 Primitive.Addresses.material3813
    · exact v3813_mb_checked.trans (by decide +kernel)
    · exact v3813_mg_checked.trans (by decide +kernel)
  upper_error := v3813_upper_checked
  lower_error := reuse_lower_error 54 61 Primitive.Addresses.material3813

def v3814_pa : Scalar.QComplex := ((999999119525203720333071524623 : Int)/10^30,(-1327007466943372920081152814 : Int)/10^30)
theorem v3814_pa_checked : Scalar.distance (sourceCoefficient 54 62 1 0) v3814_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3814_pb : Scalar.QComplex := ((-572573891424129498683870 : Int)/10^30,(-431477140521382147193885353 : Int)/10^30)
theorem v3814_pb_checked : Scalar.distance (sourceCoefficient 54 62 1 1) v3814_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3814_pg : Scalar.QComplex := ((-93086347874783330898923 : Int)/10^30,(123526387462196688990 : Int)/10^30)
theorem v3814_pg_checked : Scalar.distance (sourceCoefficient 54 62 1 2) v3814_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3814_mb : Scalar.QComplex := ((-944919017489632715890687 : Int)/10^30,(-431476485757242723358369824 : Int)/10^30)
theorem v3814_mb_checked : Scalar.distance (sourceCoefficient 54 62 3 1) v3814_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3814_mg : Scalar.QComplex := ((-93086206616772802946312 : Int)/10^30,(203855667230138124919 : Int)/10^30)
theorem v3814_mg_checked : Scalar.distance (sourceCoefficient 54 62 3 2) v3814_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3814_upper : Scalar.QComplex := ((999995339849480568550964447448 : Int)/10^30,(-3052913251610670039724612373 : Int)/10^30)
theorem v3814_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 62 5) 1) 14) v3814_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3814 : Material (54 : Basis) (62 : Basis) where
  plus := ![v3814_pa,v3814_pb,v3814_pg]
  minus := ![(Primitive.Addresses.material3814 1).one,v3814_mb,v3814_mg]
  upper := v3814_upper
  lower := (Primitive.Addresses.material3814 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3814_pa_checked.trans (by decide +kernel)
    · exact v3814_pb_checked.trans (by decide +kernel)
    · exact v3814_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 62 Primitive.Addresses.material3814
    · exact v3814_mb_checked.trans (by decide +kernel)
    · exact v3814_mg_checked.trans (by decide +kernel)
  upper_error := v3814_upper_checked
  lower_error := reuse_lower_error 54 62 Primitive.Addresses.material3814

def v3815_pa : Scalar.QComplex := ((999999086314422859034855040413 : Int)/10^30,(-1351802618528532224747200401 : Int)/10^30)
theorem v3815_pa_checked : Scalar.distance (sourceCoefficient 54 63 1 0) v3815_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3815_pb : Scalar.QComplex := ((-583272441458160518921600 : Int)/10^30,(-431477125828804726845539421 : Int)/10^30)
theorem v3815_pb_checked : Scalar.distance (sourceCoefficient 54 63 1 1) v3815_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3815_pg : Scalar.QComplex := ((-93086344744167524639150 : Int)/10^30,(125834479547564402568 : Int)/10^30)
theorem v3815_pg_checked : Scalar.distance (sourceCoefficient 54 63 1 2) v3815_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3815_mb : Scalar.QComplex := ((-955617550861072025929447 : Int)/10^30,(-431476461832303939165923736 : Int)/10^30)
theorem v3815_mb_checked : Scalar.distance (sourceCoefficient 54 63 3 1) v3815_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3815_mg : Scalar.QComplex := ((-93086201494378645294165 : Int)/10^30,(206163755754517226995 : Int)/10^30)
theorem v3815_mg_checked : Scalar.distance (sourceCoefficient 54 63 3 2) v3815_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3815_upper : Scalar.QComplex := ((999995263844566933405136876374 : Int)/10^30,(-3077708308947568793306943712 : Int)/10^30)
theorem v3815_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 63 5) 1) 14) v3815_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3815 : Material (54 : Basis) (63 : Basis) where
  plus := ![v3815_pa,v3815_pb,v3815_pg]
  minus := ![(Primitive.Addresses.material3815 1).one,v3815_mb,v3815_mg]
  upper := v3815_upper
  lower := (Primitive.Addresses.material3815 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3815_pa_checked.trans (by decide +kernel)
    · exact v3815_pb_checked.trans (by decide +kernel)
    · exact v3815_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 63 Primitive.Addresses.material3815
    · exact v3815_mb_checked.trans (by decide +kernel)
    · exact v3815_mg_checked.trans (by decide +kernel)
  upper_error := v3815_upper_checked
  lower_error := reuse_lower_error 54 63 Primitive.Addresses.material3815

def v3816_pa : Scalar.QComplex := ((999999037782326990840083164053 : Int)/10^30,(-1387239856749895137797624754 : Int)/10^30)
theorem v3816_pa_checked : Scalar.distance (sourceCoefficient 54 64 1 0) v3816_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3816_pb : Scalar.QComplex := ((-598562812191434202077097 : Int)/10^30,(-431477104216183450609962543 : Int)/10^30)
theorem v3816_pb_checked : Scalar.distance (sourceCoefficient 54 64 1 1) v3816_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3816_pg : Scalar.QComplex := ((-93086340153987584220141 : Int)/10^30,(129133205434842189764 : Int)/10^30)
theorem v3816_pg_checked : Scalar.distance (sourceCoefficient 54 64 1 2) v3816_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3816_mb : Scalar.QComplex := ((-970907897250323115559808 : Int)/10^30,(-431476427024789420215640546 : Int)/10^30)
theorem v3816_mb_checked : Scalar.distance (sourceCoefficient 54 64 3 1) v3816_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3816_mg : Scalar.QComplex := ((-93086194057548542387018 : Int)/10^30,(209462476452410052585 : Int)/10^30)
theorem v3816_mg_checked : Scalar.distance (sourceCoefficient 54 64 3 2) v3816_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3816_upper : Scalar.QComplex := ((999995154151085019132273526927 : Int)/10^30,(-3113145410627333454896279345 : Int)/10^30)
theorem v3816_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 64 5) 1) 14) v3816_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3816 : Material (54 : Basis) (64 : Basis) where
  plus := ![v3816_pa,v3816_pb,v3816_pg]
  minus := ![(Primitive.Addresses.material3816 1).one,v3816_mb,v3816_mg]
  upper := v3816_upper
  lower := (Primitive.Addresses.material3816 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3816_pa_checked.trans (by decide +kernel)
    · exact v3816_pb_checked.trans (by decide +kernel)
    · exact v3816_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 64 Primitive.Addresses.material3816
    · exact v3816_mb_checked.trans (by decide +kernel)
    · exact v3816_mg_checked.trans (by decide +kernel)
  upper_error := v3816_upper_checked
  lower_error := reuse_lower_error 54 64 Primitive.Addresses.material3816

def v3817_pa : Scalar.QComplex := ((999998987241201571366627990718 : Int)/10^30,(-1423206440112214693673228048 : Int)/10^30)
theorem v3817_pa_checked : Scalar.distance (sourceCoefficient 54 65 1 0) v3817_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3817_pb : Scalar.QComplex := ((-614081583127906728578486 : Int)/10^30,(-431477081541987959437897656 : Int)/10^30)
theorem v3817_pb_checked : Scalar.distance (sourceCoefficient 54 65 1 1) v3817_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3817_pg : Scalar.QComplex := ((-93086335355789591723403 : Int)/10^30,(132481206136312233820 : Int)/10^30)
theorem v3817_pg_checked : Scalar.distance (sourceCoefficient 54 65 1 2) v3817_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3817_mb : Scalar.QComplex := ((-986426642841638478517783 : Int)/10^30,(-431476390958601993004153573 : Int)/10^30)
theorem v3817_mb_checked : Scalar.distance (sourceCoefficient 54 65 3 1) v3817_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3817_mg : Scalar.QComplex := ((-93086186370178519464101 : Int)/10^30,(212810471766637659584 : Int)/10^30)
theorem v3817_mg_checked : Scalar.distance (sourceCoefficient 54 65 3 2) v3817_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3817_upper : Scalar.QComplex := ((999995041534974854319142550717 : Int)/10^30,(-3149111853192254605334290972 : Int)/10^30)
theorem v3817_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 65 5) 1) 14) v3817_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3817 : Material (54 : Basis) (65 : Basis) where
  plus := ![v3817_pa,v3817_pb,v3817_pg]
  minus := ![(Primitive.Addresses.material3817 1).one,v3817_mb,v3817_mg]
  upper := v3817_upper
  lower := (Primitive.Addresses.material3817 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3817_pa_checked.trans (by decide +kernel)
    · exact v3817_pb_checked.trans (by decide +kernel)
    · exact v3817_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 65 Primitive.Addresses.material3817
    · exact v3817_mb_checked.trans (by decide +kernel)
    · exact v3817_mg_checked.trans (by decide +kernel)
  upper_error := v3817_upper_checked
  lower_error := reuse_lower_error 54 65 Primitive.Addresses.material3817

def v3818_pa : Scalar.QComplex := ((999998962055802544213527892801 : Int)/10^30,(-1440793988599139010190946479 : Int)/10^30)
theorem v3818_pa_checked : Scalar.distance (sourceCoefficient 54 66 1 0) v3818_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3818_pb : Scalar.QComplex := ((-621670214197661402295012 : Int)/10^30,(-431477070183440479477263685 : Int)/10^30)
theorem v3818_pb_checked : Scalar.distance (sourceCoefficient 54 66 1 1) v3818_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3818_pg : Scalar.QComplex := ((-93086332958340617433916 : Int)/10^30,(134118368154497067645 : Int)/10^30)
theorem v3818_pg_checked : Scalar.distance (sourceCoefficient 54 66 1 2) v3818_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3818_mb : Scalar.QComplex := ((-994015261283884082173721 : Int)/10^30,(-431476373051411908407513629 : Int)/10^30)
theorem v3818_mb_checked : Scalar.distance (sourceCoefficient 54 66 3 1) v3818_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3818_mg : Scalar.QComplex := ((-93086182559933351201049 : Int)/10^30,(214447631106341764320 : Int)/10^30)
theorem v3818_mg_checked : Scalar.distance (sourceCoefficient 54 66 3 2) v3818_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3818_upper : Scalar.QComplex := ((999994985995100179363176198598 : Int)/10^30,(-3166699332016877509836195642 : Int)/10^30)
theorem v3818_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 66 5) 1) 14) v3818_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3818 : Material (54 : Basis) (66 : Basis) where
  plus := ![v3818_pa,v3818_pb,v3818_pg]
  minus := ![(Primitive.Addresses.material3818 1).one,v3818_mb,v3818_mg]
  upper := v3818_upper
  lower := (Primitive.Addresses.material3818 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3818_pa_checked.trans (by decide +kernel)
    · exact v3818_pb_checked.trans (by decide +kernel)
    · exact v3818_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 66 Primitive.Addresses.material3818
    · exact v3818_mb_checked.trans (by decide +kernel)
    · exact v3818_mg_checked.trans (by decide +kernel)
  upper_error := v3818_upper_checked
  lower_error := reuse_lower_error 54 66 Primitive.Addresses.material3818

def v3819_pa : Scalar.QComplex := ((999998919092032301815229137737 : Int)/10^30,(-1470311112327705597928271170 : Int)/10^30)
theorem v3819_pa_checked : Scalar.distance (sourceCoefficient 54 67 1 0) v3819_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3819_pb : Scalar.QComplex := ((-634406188123407314065760 : Int)/10^30,(-431477050720477972924817505 : Int)/10^30)
theorem v3819_pb_checked : Scalar.distance (sourceCoefficient 54 67 1 1) v3819_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3819_pg : Scalar.QComplex := ((-93086328859210823685243 : Int)/10^30,(136866011667051386661 : Int)/10^30)
theorem v3819_pg_checked : Scalar.distance (sourceCoefficient 54 67 1 2) v3819_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3819_mb : Scalar.QComplex := ((-1006751213671784774762756 : Int)/10^30,(-431476342597884757859111994 : Int)/10^30)
theorem v3819_mb_checked : Scalar.distance (sourceCoefficient 54 67 3 1) v3819_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3819_mg : Scalar.QComplex := ((-93086176089712481681378 : Int)/10^30,(217195270058458436048 : Int)/10^30)
theorem v3819_mg_checked : Scalar.distance (sourceCoefficient 54 67 3 2) v3819_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3819_upper : Scalar.QComplex := ((999994892087516143494888432774 : Int)/10^30,(-3196216337631585833203248569 : Int)/10^30)
theorem v3819_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 67 5) 1) 14) v3819_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3819 : Material (54 : Basis) (67 : Basis) where
  plus := ![v3819_pa,v3819_pb,v3819_pg]
  minus := ![(Primitive.Addresses.material3819 1).one,v3819_mb,v3819_mg]
  upper := v3819_upper
  lower := (Primitive.Addresses.material3819 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3819_pa_checked.trans (by decide +kernel)
    · exact v3819_pb_checked.trans (by decide +kernel)
    · exact v3819_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 67 Primitive.Addresses.material3819
    · exact v3819_mb_checked.trans (by decide +kernel)
    · exact v3819_mg_checked.trans (by decide +kernel)
  upper_error := v3819_upper_checked
  lower_error := reuse_lower_error 54 67 Primitive.Addresses.material3819

def v3820_pa : Scalar.QComplex := ((999998845606251225803894231536 : Int)/10^30,(-1519469040462313928548817262 : Int)/10^30)
theorem v3820_pa_checked : Scalar.distance (sourceCoefficient 54 68 1 0) v3820_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3820_pb : Scalar.QComplex := ((-655616726137600869337772 : Int)/10^30,(-431477017194290967185225546 : Int)/10^30)
theorem v3820_pb_checked : Scalar.distance (sourceCoefficient 54 68 1 1) v3820_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3820_pg : Scalar.QComplex := ((-93086321822497138015072 : Int)/10^30,(141441947379495749177 : Int)/10^30)
theorem v3820_pg_checked : Scalar.distance (sourceCoefficient 54 68 1 2) v3820_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3820_mb : Scalar.QComplex := ((-1027961714856736235332429 : Int)/10^30,(-431476290767971216372359127 : Int)/10^30)
theorem v3820_mb_checked : Scalar.distance (sourceCoefficient 54 68 3 1) v3820_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3820_mg : Scalar.QComplex := ((-93086165104174988755796 : Int)/10^30,(221771197994705813313 : Int)/10^30)
theorem v3820_mg_checked : Scalar.distance (sourceCoefficient 54 68 3 2) v3820_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3820_upper : Scalar.QComplex := ((999994733759720127992345172212 : Int)/10^30,(-3245374065721443143986790878 : Int)/10^30)
theorem v3820_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 68 5) 1) 14) v3820_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3820 : Material (54 : Basis) (68 : Basis) where
  plus := ![v3820_pa,v3820_pb,v3820_pg]
  minus := ![(Primitive.Addresses.material3820 1).one,v3820_mb,v3820_mg]
  upper := v3820_upper
  lower := (Primitive.Addresses.material3820 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3820_pa_checked.trans (by decide +kernel)
    · exact v3820_pb_checked.trans (by decide +kernel)
    · exact v3820_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 68 Primitive.Addresses.material3820
    · exact v3820_mb_checked.trans (by decide +kernel)
    · exact v3820_mg_checked.trans (by decide +kernel)
  upper_error := v3820_upper_checked
  lower_error := reuse_lower_error 54 68 Primitive.Addresses.material3820

def v3821_pa : Scalar.QComplex := ((999998812497904604216546400603 : Int)/10^30,(-1541104402897590951471676737 : Int)/10^30)
theorem v3821_pa_checked : Scalar.distance (sourceCoefficient 54 69 1 0) v3821_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3821_pb : Scalar.QComplex := ((-664951897160223572409635 : Int)/10^30,(-431477001998182926792352331 : Int)/10^30)
theorem v3821_pb_checked : Scalar.distance (sourceCoefficient 54 69 1 1) v3821_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3821_pg : Scalar.QComplex := ((-93086318642333412425965 : Int)/10^30,(143455905863416932468 : Int)/10^30)
theorem v3821_pg_checked : Scalar.distance (sourceCoefficient 54 69 1 2) v3821_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3821_mb : Scalar.QComplex := ((-1037296869289891296730458 : Int)/10^30,(-431476267516036682156987148 : Int)/10^30)
theorem v3821_mb_checked : Scalar.distance (sourceCoefficient 54 69 3 1) v3821_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3821_mg : Scalar.QComplex := ((-93086160186056980985980 : Int)/10^30,(223785152984400144665 : Int)/10^30)
theorem v3821_mg_checked : Scalar.distance (sourceCoefficient 54 69 3 2) v3821_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3821_upper : Scalar.QComplex := ((999994663310749998857976798834 : Int)/10^30,(-3267009338791386584647756250 : Int)/10^30)
theorem v3821_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 69 5) 1) 14) v3821_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3821 : Material (54 : Basis) (69 : Basis) where
  plus := ![v3821_pa,v3821_pb,v3821_pg]
  minus := ![(Primitive.Addresses.material3821 1).one,v3821_mb,v3821_mg]
  upper := v3821_upper
  lower := (Primitive.Addresses.material3821 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3821_pa_checked.trans (by decide +kernel)
    · exact v3821_pb_checked.trans (by decide +kernel)
    · exact v3821_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 69 Primitive.Addresses.material3821
    · exact v3821_mb_checked.trans (by decide +kernel)
    · exact v3821_mg_checked.trans (by decide +kernel)
  upper_error := v3821_upper_checked
  lower_error := reuse_lower_error 54 69 Primitive.Addresses.material3821

def v3822_pa : Scalar.QComplex := ((999998790463684576770066731356 : Int)/10^30,(-1555336352005045093594677789 : Int)/10^30)
theorem v3822_pa_checked : Scalar.distance (sourceCoefficient 54 70 1 0) v3822_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3822_pb : Scalar.QComplex := ((-671092662197125721270035 : Int)/10^30,(-431476991855201580207407286 : Int)/10^30)
theorem v3822_pb_checked : Scalar.distance (sourceCoefficient 54 70 1 1) v3822_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3822_pg : Scalar.QComplex := ((-93086316522672811215171 : Int)/10^30,(144780707079483869953 : Int)/10^30)
theorem v3822_pg_checked : Scalar.distance (sourceCoefficient 54 70 1 2) v3822_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3822_mb : Scalar.QComplex := ((-1043437623287369896344746 : Int)/10^30,(-431476252073855455211508973 : Int)/10^30)
theorem v3822_mb_checked : Scalar.distance (sourceCoefficient 54 70 3 1) v3822_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3822_mg : Scalar.QComplex := ((-93086156923153386387769 : Int)/10^30,(225109951878011410126 : Int)/10^30)
theorem v3822_mg_checked : Scalar.distance (sourceCoefficient 54 70 3 2) v3822_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3822_upper : Scalar.QComplex := ((999994616713509741665469545035 : Int)/10^30,(-3281241228672959494851163041 : Int)/10^30)
theorem v3822_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 70 5) 1) 14) v3822_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3822 : Material (54 : Basis) (70 : Basis) where
  plus := ![v3822_pa,v3822_pb,v3822_pg]
  minus := ![(Primitive.Addresses.material3822 1).one,v3822_mb,v3822_mg]
  upper := v3822_upper
  lower := (Primitive.Addresses.material3822 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3822_pa_checked.trans (by decide +kernel)
    · exact v3822_pb_checked.trans (by decide +kernel)
    · exact v3822_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 70 Primitive.Addresses.material3822
    · exact v3822_mb_checked.trans (by decide +kernel)
    · exact v3822_mg_checked.trans (by decide +kernel)
  upper_error := v3822_upper_checked
  lower_error := reuse_lower_error 54 70 Primitive.Addresses.material3822

def v3823_pa : Scalar.QComplex := ((999998752385113863948682996077 : Int)/10^30,(-1579629138668060442326827055 : Int)/10^30)
theorem v3823_pa_checked : Scalar.distance (sourceCoefficient 54 71 1 0) v3823_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3823_pb : Scalar.QComplex := ((-681574451567990539213711 : Int)/10^30,(-431476974272746072051172824 : Int)/10^30)
theorem v3823_pb_checked : Scalar.distance (sourceCoefficient 54 71 1 1) v3823_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3823_pg : Scalar.QComplex := ((-93086312853765043087738 : Int)/10^30,(147042035646811039116 : Int)/10^30)
theorem v3823_pg_checked : Scalar.distance (sourceCoefficient 54 71 1 2) v3823_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3823_mb : Scalar.QComplex := ((-1053919393582518270937201 : Int)/10^30,(-431476225446094349019426414 : Int)/10^30)
theorem v3823_mb_checked : Scalar.distance (sourceCoefficient 54 71 3 1) v3823_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3823_mg : Scalar.QComplex := ((-93086151302822277216982 : Int)/10^30,(227371276437240443430 : Int)/10^30)
theorem v3823_mg_checked : Scalar.distance (sourceCoefficient 54 71 3 2) v3823_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3823_upper : Scalar.QComplex := ((999994536707849786428384878540 : Int)/10^30,(-3305533913434564150820635976 : Int)/10^30)
theorem v3823_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 71 5) 1) 14) v3823_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3823 : Material (54 : Basis) (71 : Basis) where
  plus := ![v3823_pa,v3823_pb,v3823_pg]
  minus := ![(Primitive.Addresses.material3823 1).one,v3823_mb,v3823_mg]
  upper := v3823_upper
  lower := (Primitive.Addresses.material3823 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3823_pa_checked.trans (by decide +kernel)
    · exact v3823_pb_checked.trans (by decide +kernel)
    · exact v3823_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 71 Primitive.Addresses.material3823
    · exact v3823_mb_checked.trans (by decide +kernel)
    · exact v3823_mg_checked.trans (by decide +kernel)
  upper_error := v3823_upper_checked
  lower_error := reuse_lower_error 54 71 Primitive.Addresses.material3823

def v3824_pa : Scalar.QComplex := ((999998710394447799313105668985 : Int)/10^30,(-1605991731398045997369154244 : Int)/10^30)
theorem v3824_pa_checked : Scalar.distance (sourceCoefficient 54 72 1 0) v3824_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3824_pb : Scalar.QComplex := ((-692949315341882500322456 : Int)/10^30,(-431476954808088216082956134 : Int)/10^30)
theorem v3824_pb_checked : Scalar.distance (sourceCoefficient 54 72 1 1) v3824_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3824_pg : Scalar.QComplex := ((-93086308799743769923006 : Int)/10^30,(149496035029670468294 : Int)/10^30)
theorem v3824_pg_checked : Scalar.distance (sourceCoefficient 54 72 1 2) v3824_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3824_mb : Scalar.QComplex := ((-1065294236323905518016322 : Int)/10^30,(-431476196165448608610872126 : Int)/10^30)
theorem v3824_mb_checked : Scalar.distance (sourceCoefficient 54 72 3 1) v3824_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3824_mg : Scalar.QComplex := ((-93086145131111570171319 : Int)/10^30,(229825271407925976656 : Int)/10^30)
theorem v3824_mg_checked : Scalar.distance (sourceCoefficient 54 72 3 2) v3824_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3824_upper : Scalar.QComplex := ((999994449217802805732616381810 : Int)/10^30,(-3331896394428484338134870564 : Int)/10^30)
theorem v3824_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 72 5) 1) 14) v3824_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3824 : Material (54 : Basis) (72 : Basis) where
  plus := ![v3824_pa,v3824_pb,v3824_pg]
  minus := ![(Primitive.Addresses.material3824 1).one,v3824_mb,v3824_mg]
  upper := v3824_upper
  lower := (Primitive.Addresses.material3824 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3824_pa_checked.trans (by decide +kernel)
    · exact v3824_pb_checked.trans (by decide +kernel)
    · exact v3824_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 72 Primitive.Addresses.material3824
    · exact v3824_mb_checked.trans (by decide +kernel)
    · exact v3824_mg_checked.trans (by decide +kernel)
  upper_error := v3824_upper_checked
  lower_error := reuse_lower_error 54 72 Primitive.Addresses.material3824

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
