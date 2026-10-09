import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B084

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2017_pa : Scalar.QComplex := ((999999592095327909849266645359 : Int)/10^30,(-903221555208953122632367957 : Int)/10^30)
theorem v2017_pa_checked : Scalar.distance (sourceCoefficient 23 63 1 0) v2017_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2017_pb : Scalar.QComplex := ((-389719776987286942791813 : Int)/10^30,(-431477322226450375092732800 : Int)/10^30)
theorem v2017_pb_checked : Scalar.distance (sourceCoefficient 23 63 1 1) v2017_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2017_pg : Scalar.QComplex := ((-93086389470130218941884 : Int)/10^30,(84077667761670832589 : Int)/10^30)
theorem v2017_pg_checked : Scalar.distance (sourceCoefficient 23 63 1 2) v2017_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2017_mb : Scalar.QComplex := ((-762065127941023998898104 : Int)/10^30,(-431476825257108609550911163 : Int)/10^30)
theorem v2017_mb_checked : Scalar.distance (sourceCoefficient 23 63 3 1) v2017_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2017_mg : Scalar.QComplex := ((-93086282254572600313494 : Int)/10^30,(164406998113084488079 : Int)/10^30)
theorem v2017_mg_checked : Scalar.distance (sourceCoefficient 23 63 3 2) v2017_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2017_upper : Scalar.QComplex := ((999996543834939016395404229101 : Int)/10^30,(-2629128786668747504879987305 : Int)/10^30)
theorem v2017_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 63 5) 1) 14) v2017_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2017 : Material (23 : Basis) (63 : Basis) where
  plus := ![v2017_pa,v2017_pb,v2017_pg]
  minus := ![(Primitive.Addresses.material2017 1).one,v2017_mb,v2017_mg]
  upper := v2017_upper
  lower := (Primitive.Addresses.material2017 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2017_pa_checked.trans (by decide +kernel)
    · exact v2017_pb_checked.trans (by decide +kernel)
    · exact v2017_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 63 Primitive.Addresses.material2017
    · exact v2017_mb_checked.trans (by decide +kernel)
    · exact v2017_mg_checked.trans (by decide +kernel)
  upper_error := v2017_upper_checked
  lower_error := reuse_lower_error 23 63 Primitive.Addresses.material2017

def v2018_pa : Scalar.QComplex := ((999999559459720631669722499056 : Int)/10^30,(-938658811635475357867583744 : Int)/10^30)
theorem v2018_pa_checked : Scalar.distance (sourceCoefficient 23 64 1 0) v2018_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2018_pb : Scalar.QComplex := ((-405010152957305199451512 : Int)/10^30,(-431477305186480664383794686 : Int)/10^30)
theorem v2018_pb_checked : Scalar.distance (sourceCoefficient 23 64 1 1) v2018_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2018_pg : Scalar.QComplex := ((-93086386113073076075997 : Int)/10^30,(87376395061159680114 : Int)/10^30)
theorem v2018_pg_checked : Scalar.distance (sourceCoefficient 23 64 1 2) v2018_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2018_mb : Scalar.QComplex := ((-777355483513010068621332 : Int)/10^30,(-431476795022239434445395678 : Int)/10^30)
theorem v2018_mb_checked : Scalar.distance (sourceCoefficient 23 64 3 1) v2018_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2018_mg : Scalar.QComplex := ((-93086276050863617136953 : Int)/10^30,(167705721287317284668 : Int)/10^30)
theorem v2018_mg_checked : Scalar.distance (sourceCoefficient 23 64 3 2) v2018_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2018_upper : Scalar.QComplex := ((999996450037890595731915566268 : Int)/10^30,(-2664565933989541562394438099 : Int)/10^30)
theorem v2018_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 64 5) 1) 14) v2018_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2018 : Material (23 : Basis) (64 : Basis) where
  plus := ![v2018_pa,v2018_pb,v2018_pg]
  minus := ![(Primitive.Addresses.material2018 1).one,v2018_mb,v2018_mg]
  upper := v2018_upper
  lower := (Primitive.Addresses.material2018 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2018_pa_checked.trans (by decide +kernel)
    · exact v2018_pb_checked.trans (by decide +kernel)
    · exact v2018_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 64 Primitive.Addresses.material2018
    · exact v2018_mb_checked.trans (by decide +kernel)
    · exact v2018_mg_checked.trans (by decide +kernel)
  upper_error := v2018_upper_checked
  lower_error := reuse_lower_error 23 64 Primitive.Addresses.material2018

def v2019_pa : Scalar.QComplex := ((999999525052538355501824784191 : Int)/10^30,(-974625414050908600602611284 : Int)/10^30)
theorem v2019_pa_checked : Scalar.distance (sourceCoefficient 23 65 1 0) v2019_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2019_pb : Scalar.QComplex := ((-420528929374437778559284 : Int)/10^30,(-431477287153240926273273500 : Int)/10^30)
theorem v2019_pb_checked : Scalar.distance (sourceCoefficient 23 65 1 1) v2019_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2019_pg : Scalar.QComplex := ((-93086382566417709480275 : Int)/10^30,(90724397240618318730 : Int)/10^30)
theorem v2019_pg_checked : Scalar.distance (sourceCoefficient 23 65 1 2) v2019_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2019_mb : Scalar.QComplex := ((-792874238589919237489688 : Int)/10^30,(-431476763597001302692737750 : Int)/10^30)
theorem v2019_mb_checked : Scalar.distance (sourceCoefficient 23 65 3 1) v2019_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2019_mg : Scalar.QComplex := ((-93086269615034478670943 : Int)/10^30,(171053719159557854668 : Int)/10^30)
theorem v2019_mg_checked : Scalar.distance (sourceCoefficient 23 65 3 2) v2019_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2019_upper : Scalar.QComplex := ((999996353555666660665517641007 : Int)/10^30,(-2700532423453270227774088439 : Int)/10^30)
theorem v2019_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 65 5) 1) 14) v2019_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2019 : Material (23 : Basis) (65 : Basis) where
  plus := ![v2019_pa,v2019_pb,v2019_pg]
  minus := ![(Primitive.Addresses.material2019 1).one,v2019_mb,v2019_mg]
  upper := v2019_upper
  lower := (Primitive.Addresses.material2019 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2019_pa_checked.trans (by decide +kernel)
    · exact v2019_pb_checked.trans (by decide +kernel)
    · exact v2019_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 65 Primitive.Addresses.material2019
    · exact v2019_mb_checked.trans (by decide +kernel)
    · exact v2019_mg_checked.trans (by decide +kernel)
  upper_error := v2019_upper_checked
  lower_error := reuse_lower_error 23 65 Primitive.Addresses.material2019

def v2020_pa : Scalar.QComplex := ((999999507756587880185513990842 : Int)/10^30,(-992212972066003678823316049 : Int)/10^30)
theorem v2020_pa_checked : Scalar.distance (sourceCoefficient 23 66 1 0) v2020_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2020_pb : Scalar.QComplex := ((-428117563184986719097540 : Int)/10^30,(-431477278064106524116782586 : Int)/10^30)
theorem v2020_pb_checked : Scalar.distance (sourceCoefficient 23 66 1 1) v2020_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2020_pg : Scalar.QComplex := ((-93086380780969227380742 : Int)/10^30,(92361559997922643806 : Int)/10^30)
theorem v2020_pg_checked : Scalar.distance (sourceCoefficient 23 66 1 2) v2020_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2020_mb : Scalar.QComplex := ((-800462861731359363018575 : Int)/10^30,(-431476747959221085712023220 : Int)/10^30)
theorem v2020_mb_checked : Scalar.distance (sourceCoefficient 23 66 3 1) v2020_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2020_mg : Scalar.QComplex := ((-93086266416788936895260 : Int)/10^30,(172690879766510036729 : Int)/10^30)
theorem v2020_mg_checked : Scalar.distance (sourceCoefficient 23 66 3 2) v2020_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2020_upper : Scalar.QComplex := ((999996305905212342381136560689 : Int)/10^30,(-2718119925422522178176501452 : Int)/10^30)
theorem v2020_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 66 5) 1) 14) v2020_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2020 : Material (23 : Basis) (66 : Basis) where
  plus := ![v2020_pa,v2020_pb,v2020_pg]
  minus := ![(Primitive.Addresses.material2020 1).one,v2020_mb,v2020_mg]
  upper := v2020_upper
  lower := (Primitive.Addresses.material2020 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2020_pa_checked.trans (by decide +kernel)
    · exact v2020_pb_checked.trans (by decide +kernel)
    · exact v2020_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 66 Primitive.Addresses.material2020
    · exact v2020_mb_checked.trans (by decide +kernel)
    · exact v2020_mg_checked.trans (by decide +kernel)
  upper_error := v2020_upper_checked
  lower_error := reuse_lower_error 23 66 Primitive.Addresses.material2020

def v2021_pa : Scalar.QComplex := ((999999478033652792159958219338 : Int)/10^30,(-1021730112097520822630110503 : Int)/10^30)
theorem v2021_pa_checked : Scalar.distance (sourceCoefficient 23 67 1 0) v2021_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2021_pb : Scalar.QComplex := ((-440853541800303635081104 : Int)/10^30,(-431477262409892398631188555 : Int)/10^30)
theorem v2021_pb_checked : Scalar.distance (sourceCoefficient 23 67 1 1) v2021_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2021_pg : Scalar.QComplex := ((-93086377708957814385715 : Int)/10^30,(95109204775129833542 : Int)/10^30)
theorem v2021_pg_checked : Scalar.distance (sourceCoefficient 23 67 1 2) v2021_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2021_mb : Scalar.QComplex := ((-813198822095607626880280 : Int)/10^30,(-431476721314436851170816864 : Int)/10^30)
theorem v2021_mb_checked : Scalar.distance (sourceCoefficient 23 67 3 1) v2021_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2021_mg : Scalar.QComplex := ((-93086260973684974347650 : Int)/10^30,(175438520869636011184 : Int)/10^30)
theorem v2021_mg_checked : Scalar.distance (sourceCoefficient 23 67 3 2) v2021_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2021_upper : Scalar.QComplex := ((999996225238415602803339442074 : Int)/10^30,(-2747636970192637053548652743 : Int)/10^30)
theorem v2021_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 67 5) 1) 14) v2021_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2021 : Material (23 : Basis) (67 : Basis) where
  plus := ![v2021_pa,v2021_pb,v2021_pg]
  minus := ![(Primitive.Addresses.material2021 1).one,v2021_mb,v2021_mg]
  upper := v2021_upper
  lower := (Primitive.Addresses.material2021 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2021_pa_checked.trans (by decide +kernel)
    · exact v2021_pb_checked.trans (by decide +kernel)
    · exact v2021_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 67 Primitive.Addresses.material2021
    · exact v2021_mb_checked.trans (by decide +kernel)
    · exact v2021_mg_checked.trans (by decide +kernel)
  upper_error := v2021_upper_checked
  lower_error := reuse_lower_error 23 67 Primitive.Addresses.material2021

def v2022_pa : Scalar.QComplex := ((999999426599208245045678927826 : Int)/10^30,(-1070888068250571487772460040 : Int)/10^30)
theorem v2022_pa_checked : Scalar.distance (sourceCoefficient 23 68 1 0) v2022_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2022_pb : Scalar.QComplex := ((-462064087874048977103065 : Int)/10^30,(-431477235226809209178586618 : Int)/10^30)
theorem v2022_pb_checked : Scalar.distance (sourceCoefficient 23 68 1 1) v2022_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2022_pg : Scalar.QComplex := ((-93086372382810928724313 : Int)/10^30,(99685142661021470725 : Int)/10^30)
theorem v2022_pg_checked : Scalar.distance (sourceCoefficient 23 68 1 2) v2022_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2022_mb : Scalar.QComplex := ((-834409336813920783925263 : Int)/10^30,(-431476675827617809113405823 : Int)/10^30)
theorem v2022_mb_checked : Scalar.distance (sourceCoefficient 23 68 3 1) v2022_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2022_mg : Scalar.QComplex := ((-93086251698711768921532 : Int)/10^30,(180014452455471961182 : Int)/10^30)
theorem v2022_mg_checked : Scalar.distance (sourceCoefficient 23 68 3 2) v2022_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2022_upper : Scalar.QComplex := ((999996088961874916032767802015 : Int)/10^30,(-2796794764359501335928739971 : Int)/10^30)
theorem v2022_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 68 5) 1) 14) v2022_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2022 : Material (23 : Basis) (68 : Basis) where
  plus := ![v2022_pa,v2022_pb,v2022_pg]
  minus := ![(Primitive.Addresses.material2022 1).one,v2022_mb,v2022_mg]
  upper := v2022_upper
  lower := (Primitive.Addresses.material2022 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2022_pa_checked.trans (by decide +kernel)
    · exact v2022_pb_checked.trans (by decide +kernel)
    · exact v2022_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 68 Primitive.Addresses.material2022
    · exact v2022_mb_checked.trans (by decide +kernel)
    · exact v2022_mg_checked.trans (by decide +kernel)
  upper_error := v2022_upper_checked
  lower_error := reuse_lower_error 23 68 Primitive.Addresses.material2022

def v2023_pa : Scalar.QComplex := ((999999403196084766025115041410 : Int)/10^30,(-1092523443360844560012562854 : Int)/10^30)
theorem v2023_pa_checked : Scalar.distance (sourceCoefficient 23 69 1 0) v2023_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2023_pb : Scalar.QComplex := ((-471399262542655474859001 : Int)/10^30,(-431477222822424820378861866 : Int)/10^30)
theorem v2023_pb_checked : Scalar.distance (sourceCoefficient 23 69 1 1) v2023_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2023_pg : Scalar.QComplex := ((-93086369955501001250995 : Int)/10^30,(101699102128167746757 : Int)/10^30)
theorem v2023_pg_checked : Scalar.distance (sourceCoefficient 23 69 1 2) v2023_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2023_mb : Scalar.QComplex := ((-843744497302190059200074 : Int)/10^30,(-431476655367402740685072946 : Int)/10^30)
theorem v2023_mb_checked : Scalar.distance (sourceCoefficient 23 69 3 1) v2023_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2023_mg : Scalar.QComplex := ((-93086247533446430466656 : Int)/10^30,(182028409078069939672 : Int)/10^30)
theorem v2023_mg_checked : Scalar.distance (sourceCoefficient 23 69 3 2) v2023_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2023_upper : Scalar.QComplex := ((999996028218091598782053652561 : Int)/10^30,(-2818430066854756641093723788 : Int)/10^30)
theorem v2023_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 69 5) 1) 14) v2023_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2023 : Material (23 : Basis) (69 : Basis) where
  plus := ![v2023_pa,v2023_pb,v2023_pg]
  minus := ![(Primitive.Addresses.material2023 1).one,v2023_mb,v2023_mg]
  upper := v2023_upper
  lower := (Primitive.Addresses.material2023 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2023_pa_checked.trans (by decide +kernel)
    · exact v2023_pb_checked.trans (by decide +kernel)
    · exact v2023_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 69 Primitive.Addresses.material2023
    · exact v2023_mb_checked.trans (by decide +kernel)
    · exact v2023_mg_checked.trans (by decide +kernel)
  upper_error := v2023_upper_checked
  lower_error := reuse_lower_error 23 69 Primitive.Addresses.material2023

def v2024_pa : Scalar.QComplex := ((999999387546053716705829836929 : Int)/10^30,(-1106755400920524996534281658 : Int)/10^30)
theorem v2024_pa_checked : Scalar.distance (sourceCoefficient 23 70 1 0) v2024_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2024_pb : Scalar.QComplex := ((-477540030010854637250216 : Int)/10^30,(-431477214515866096034159874 : Int)/10^30)
theorem v2024_pb_checked : Scalar.distance (sourceCoefficient 23 70 1 1) v2024_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2024_pg : Scalar.QComplex := ((-93086368331074857201549 : Int)/10^30,(103023903999890981142 : Int)/10^30)
theorem v2024_pg_checked : Scalar.distance (sourceCoefficient 23 70 1 2) v2024_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2024_mb : Scalar.QComplex := ((-849885255315714780650924 : Int)/10^30,(-431476641761641354095945780 : Int)/10^30)
theorem v2024_mb_checked : Scalar.distance (sourceCoefficient 23 70 3 1) v2024_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2024_mg : Scalar.QComplex := ((-93086244765776542829517 : Int)/10^30,(183353209054702289900 : Int)/10^30)
theorem v2024_mg_checked : Scalar.distance (sourceCoefficient 23 70 3 2) v2024_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2024_upper : Scalar.QComplex := ((999995988005016223441393308305 : Int)/10^30,(-2832661976207074264245313743 : Int)/10^30)
theorem v2024_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 70 5) 1) 14) v2024_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2024 : Material (23 : Basis) (70 : Basis) where
  plus := ![v2024_pa,v2024_pb,v2024_pg]
  minus := ![(Primitive.Addresses.material2024 1).one,v2024_mb,v2024_mg]
  upper := v2024_upper
  lower := (Primitive.Addresses.material2024 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2024_pa_checked.trans (by decide +kernel)
    · exact v2024_pb_checked.trans (by decide +kernel)
    · exact v2024_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 70 Primitive.Addresses.material2024
    · exact v2024_mb_checked.trans (by decide +kernel)
    · exact v2024_mg_checked.trans (by decide +kernel)
  upper_error := v2024_upper_checked
  lower_error := reuse_lower_error 23 70 Primitive.Addresses.material2024

def v2025_pa : Scalar.QComplex := ((999999360364777560034532700138 : Int)/10^30,(-1131048202220715767835554462 : Int)/10^30)
theorem v2025_pa_checked : Scalar.distance (sourceCoefficient 23 71 1 0) v2025_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2025_pb : Scalar.QComplex := ((-488021823592127409032345 : Int)/10^30,(-431477200068035560705299423 : Int)/10^30)
theorem v2025_pb_checked : Scalar.distance (sourceCoefficient 23 71 1 1) v2025_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2025_pg : Scalar.QComplex := ((-93086365507492276929498 : Int)/10^30,(105285233702653465029 : Int)/10^30)
theorem v2025_pg_checked : Scalar.distance (sourceCoefficient 23 71 1 2) v2025_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2025_mb : Scalar.QComplex := ((-860367032526309714636557 : Int)/10^30,(-431476618268500420174665983 : Int)/10^30)
theorem v2025_mb_checked : Scalar.distance (sourceCoefficient 23 71 3 1) v2025_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2025_mg : Scalar.QComplex := ((-93086239990769326931373 : Int)/10^30,(185614535478843780240 : Int)/10^30)
theorem v2025_mg_checked : Scalar.distance (sourceCoefficient 23 71 3 2) v2025_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2025_upper : Scalar.QComplex := ((999995918896609331677334821700 : Int)/10^30,(-2856954694413574351505916329 : Int)/10^30)
theorem v2025_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 71 5) 1) 14) v2025_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2025 : Material (23 : Basis) (71 : Basis) where
  plus := ![v2025_pa,v2025_pb,v2025_pg]
  minus := ![(Primitive.Addresses.material2025 1).one,v2025_mb,v2025_mg]
  upper := v2025_upper
  lower := (Primitive.Addresses.material2025 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2025_pa_checked.trans (by decide +kernel)
    · exact v2025_pb_checked.trans (by decide +kernel)
    · exact v2025_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 71 Primitive.Addresses.material2025
    · exact v2025_mb_checked.trans (by decide +kernel)
    · exact v2025_mg_checked.trans (by decide +kernel)
  upper_error := v2025_upper_checked
  lower_error := reuse_lower_error 23 71 Primitive.Addresses.material2025

def v2026_pa : Scalar.QComplex := ((999999330199882818366461283826 : Int)/10^30,(-1157410811134521112523214900 : Int)/10^30)
theorem v2026_pa_checked : Scalar.distance (sourceCoefficient 23 72 1 0) v2026_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2026_pb : Scalar.QComplex := ((-499396692021322145803349 : Int)/10^30,(-431477184005080559923051791 : Int)/10^30)
theorem v2026_pb_checked : Scalar.distance (sourceCoefficient 23 72 1 1) v2026_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2026_pg : Scalar.QComplex := ((-93086362370820011482890 : Int)/10^30,(107739234340924539863 : Int)/10^30)
theorem v2026_pg_checked : Scalar.distance (sourceCoefficient 23 72 1 2) v2026_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2026_mb : Scalar.QComplex := ((-871741882858514361012161 : Int)/10^30,(-431476592389552251026013923 : Int)/10^30)
theorem v2026_mb_checked : Scalar.distance (sourceCoefficient 23 72 3 1) v2026_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2026_mg : Scalar.QComplex := ((-93086234736406202669166 : Int)/10^30,(188068532496571369470 : Int)/10^30)
theorem v2026_mg_checked : Scalar.distance (sourceCoefficient 23 72 3 2) v2026_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2026_upper : Scalar.QComplex := ((999995843232288129047067092541 : Int)/10^30,(-2883317212001498702414941729 : Int)/10^30)
theorem v2026_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 72 5) 1) 14) v2026_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2026 : Material (23 : Basis) (72 : Basis) where
  plus := ![v2026_pa,v2026_pb,v2026_pg]
  minus := ![(Primitive.Addresses.material2026 1).one,v2026_mb,v2026_mg]
  upper := v2026_upper
  lower := (Primitive.Addresses.material2026 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2026_pa_checked.trans (by decide +kernel)
    · exact v2026_pb_checked.trans (by decide +kernel)
    · exact v2026_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 72 Primitive.Addresses.material2026
    · exact v2026_mb_checked.trans (by decide +kernel)
    · exact v2026_mg_checked.trans (by decide +kernel)
  upper_error := v2026_upper_checked
  lower_error := reuse_lower_error 23 72 Primitive.Addresses.material2026

def v2027_pa : Scalar.QComplex := ((999999319218116433931888663201 : Int)/10^30,(-1166860447383560615180814184 : Int)/10^30)
theorem v2027_pa_checked : Scalar.distance (sourceCoefficient 23 73 1 0) v2027_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2027_pb : Scalar.QComplex := ((-503473995887873723614644 : Int)/10^30,(-431477178149994165193814146 : Int)/10^30)
theorem v2027_pb_checked : Scalar.distance (sourceCoefficient 23 73 1 1) v2027_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2027_pg : Scalar.QComplex := ((-93086361228108726441982 : Int)/10^30,(108618867053695583106 : Int)/10^30)
theorem v2027_pg_checked : Scalar.distance (sourceCoefficient 23 73 1 2) v2027_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2027_mb : Scalar.QComplex := ((-875819180154223511964880 : Int)/10^30,(-431476583015938434528319789 : Int)/10^30)
theorem v2027_mb_checked : Scalar.distance (sourceCoefficient 23 73 3 1) v2027_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2027_mg : Scalar.QComplex := ((-93086232834611929177207 : Int)/10^30,(188948163895706579363 : Int)/10^30)
theorem v2027_mg_checked : Scalar.distance (sourceCoefficient 23 73 3 2) v2027_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2027_upper : Scalar.QComplex := ((999995815941323199125265221471 : Int)/10^30,(-2892766815222882522907509247 : Int)/10^30)
theorem v2027_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 73 5) 1) 14) v2027_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2027 : Material (23 : Basis) (73 : Basis) where
  plus := ![v2027_pa,v2027_pb,v2027_pg]
  minus := ![(Primitive.Addresses.material2027 1).one,v2027_mb,v2027_mg]
  upper := v2027_upper
  lower := (Primitive.Addresses.material2027 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2027_pa_checked.trans (by decide +kernel)
    · exact v2027_pb_checked.trans (by decide +kernel)
    · exact v2027_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 73 Primitive.Addresses.material2027
    · exact v2027_mb_checked.trans (by decide +kernel)
    · exact v2027_mg_checked.trans (by decide +kernel)
  upper_error := v2027_upper_checked
  lower_error := reuse_lower_error 23 73 Primitive.Addresses.material2027

def v2028_pa : Scalar.QComplex := ((999999306754157946028730142958 : Int)/10^30,(-1177493610818396336743020676 : Int)/10^30)
theorem v2028_pa_checked : Scalar.distance (sourceCoefficient 23 74 1 0) v2028_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2028_pb : Scalar.QComplex := ((-508061964867272436358003 : Int)/10^30,(-431477171500156548455992701 : Int)/10^30)
theorem v2028_pb_checked : Scalar.distance (sourceCoefficient 23 74 1 1) v2028_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2028_pg : Scalar.QComplex := ((-93086359930682129676249 : Int)/10^30,(109608670058474557706 : Int)/10^30)
theorem v2028_pg_checked : Scalar.distance (sourceCoefficient 23 74 1 2) v2028_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2028_mb : Scalar.QComplex := ((-880407141686801327460957 : Int)/10^30,(-431476572406892699060067241 : Int)/10^30)
theorem v2028_mb_checked : Scalar.distance (sourceCoefficient 23 74 3 1) v2028_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2028_mg : Scalar.QComplex := ((-93086230683030401450918 : Int)/10^30,(189937965412315939968 : Int)/10^30)
theorem v2028_mg_checked : Scalar.distance (sourceCoefficient 23 74 3 2) v2028_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2028_upper : Scalar.QComplex := ((999995785125507819349208027256 : Int)/10^30,(-2903399941309208738761041286 : Int)/10^30)
theorem v2028_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 74 5) 1) 14) v2028_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2028 : Material (23 : Basis) (74 : Basis) where
  plus := ![v2028_pa,v2028_pb,v2028_pg]
  minus := ![(Primitive.Addresses.material2028 1).one,v2028_mb,v2028_mg]
  upper := v2028_upper
  lower := (Primitive.Addresses.material2028 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2028_pa_checked.trans (by decide +kernel)
    · exact v2028_pb_checked.trans (by decide +kernel)
    · exact v2028_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 74 Primitive.Addresses.material2028
    · exact v2028_mb_checked.trans (by decide +kernel)
    · exact v2028_mg_checked.trans (by decide +kernel)
  upper_error := v2028_upper_checked
  lower_error := reuse_lower_error 23 74 Primitive.Addresses.material2028

def v2029_pa : Scalar.QComplex := ((999999289199694328167890606047 : Int)/10^30,(-1192308729359384366500258648 : Int)/10^30)
theorem v2029_pa_checked : Scalar.distance (sourceCoefficient 23 75 1 0) v2029_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2029_pb : Scalar.QComplex := ((-514454352596987127683195 : Int)/10^30,(-431477162126529982797833917 : Int)/10^30)
theorem v2029_pb_checked : Scalar.distance (sourceCoefficient 23 75 1 1) v2029_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2029_pg : Scalar.QComplex := ((-93086358102513618002944 : Int)/10^30,(110987756240031706668 : Int)/10^30)
theorem v2029_pg_checked : Scalar.distance (sourceCoefficient 23 75 1 2) v2029_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2029_mb : Scalar.QComplex := ((-886799518947320366767537 : Int)/10^30,(-431476557516926915343600954 : Int)/10^30)
theorem v2029_mb_checked : Scalar.distance (sourceCoefficient 23 75 3 1) v2029_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2029_mg : Scalar.QComplex := ((-93086227664773307540404 : Int)/10^30,(191317049502749188263 : Int)/10^30)
theorem v2029_mg_checked : Scalar.distance (sourceCoefficient 23 75 3 2) v2029_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2029_upper : Scalar.QComplex := ((999995742001519762109649143569 : Int)/10^30,(-2918215007487406331861720729 : Int)/10^30)
theorem v2029_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 75 5) 1) 14) v2029_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2029 : Material (23 : Basis) (75 : Basis) where
  plus := ![v2029_pa,v2029_pb,v2029_pg]
  minus := ![(Primitive.Addresses.material2029 1).one,v2029_mb,v2029_mg]
  upper := v2029_upper
  lower := (Primitive.Addresses.material2029 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2029_pa_checked.trans (by decide +kernel)
    · exact v2029_pb_checked.trans (by decide +kernel)
    · exact v2029_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 75 Primitive.Addresses.material2029
    · exact v2029_mb_checked.trans (by decide +kernel)
    · exact v2029_mg_checked.trans (by decide +kernel)
  upper_error := v2029_upper_checked
  lower_error := reuse_lower_error 23 75 Primitive.Addresses.material2029

def v2030_pa : Scalar.QComplex := ((999999274301821589081843168691 : Int)/10^30,(-1204738905399833995390873456 : Int)/10^30)
theorem v2030_pa_checked : Scalar.distance (sourceCoefficient 23 76 1 0) v2030_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2030_pb : Scalar.QComplex := ((-519817691643873425506947 : Int)/10^30,(-431477154164455458761989302 : Int)/10^30)
theorem v2030_pb_checked : Scalar.distance (sourceCoefficient 23 76 1 1) v2030_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2030_pg : Scalar.QComplex := ((-93086356550254637924120 : Int)/10^30,(112144836681316137641 : Int)/10^30)
theorem v2030_pg_checked : Scalar.distance (sourceCoefficient 23 76 1 2) v2030_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2030_mb : Scalar.QComplex := ((-892162849126278705013892 : Int)/10^30,(-431476544926535314312809485 : Int)/10^30)
theorem v2030_mb_checked : Scalar.distance (sourceCoefficient 23 76 3 1) v2030_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2030_mg : Scalar.QComplex := ((-93086225114006597578627 : Int)/10^30,(192474128173670101098 : Int)/10^30)
theorem v2030_mg_checked : Scalar.distance (sourceCoefficient 23 76 3 2) v2030_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2030_upper : Scalar.QComplex := ((999995705650313022600578424813 : Int)/10^30,(-2930645139302192076345183628 : Int)/10^30)
theorem v2030_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 76 5) 1) 14) v2030_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2030 : Material (23 : Basis) (76 : Basis) where
  plus := ![v2030_pa,v2030_pb,v2030_pg]
  minus := ![(Primitive.Addresses.material2030 1).one,v2030_mb,v2030_mg]
  upper := v2030_upper
  lower := (Primitive.Addresses.material2030 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2030_pa_checked.trans (by decide +kernel)
    · exact v2030_pb_checked.trans (by decide +kernel)
    · exact v2030_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 76 Primitive.Addresses.material2030
    · exact v2030_mb_checked.trans (by decide +kernel)
    · exact v2030_mg_checked.trans (by decide +kernel)
  upper_error := v2030_upper_checked
  lower_error := reuse_lower_error 23 76 Primitive.Addresses.material2030

def v2031_pa : Scalar.QComplex := ((999999270830811797034502046695 : Int)/10^30,(-1207616596738478901622158640 : Int)/10^30)
theorem v2031_pa_checked : Scalar.distance (sourceCoefficient 23 77 1 0) v2031_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2031_pb : Scalar.QComplex := ((-521059350181619778774857 : Int)/10^30,(-431477152308496121203194296 : Int)/10^30)
theorem v2031_pb_checked : Scalar.distance (sourceCoefficient 23 77 1 1) v2031_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2031_pg : Scalar.QComplex := ((-93086356188501489648865 : Int)/10^30,(112412710631028967867 : Int)/10^30)
theorem v2031_pg_checked : Scalar.distance (sourceCoefficient 23 77 1 2) v2031_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2031_mb : Scalar.QComplex := ((-893404505600089519072664 : Int)/10^30,(-431476541999081271962004052 : Int)/10^30)
theorem v2031_mb_checked : Scalar.distance (sourceCoefficient 23 77 3 1) v2031_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2031_mg : Scalar.QComplex := ((-93086224521090429993266 : Int)/10^30,(192742001711464543198 : Int)/10^30)
theorem v2031_mg_checked : Scalar.distance (sourceCoefficient 23 77 3 2) v2031_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2031_upper : Scalar.QComplex := ((999995697212674211832417456806 : Int)/10^30,(-2933522820364205757510205572 : Int)/10^30)
theorem v2031_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 77 5) 1) 14) v2031_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2031 : Material (23 : Basis) (77 : Basis) where
  plus := ![v2031_pa,v2031_pb,v2031_pg]
  minus := ![(Primitive.Addresses.material2031 1).one,v2031_mb,v2031_mg]
  upper := v2031_upper
  lower := (Primitive.Addresses.material2031 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2031_pa_checked.trans (by decide +kernel)
    · exact v2031_pb_checked.trans (by decide +kernel)
    · exact v2031_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 77 Primitive.Addresses.material2031
    · exact v2031_mb_checked.trans (by decide +kernel)
    · exact v2031_mg_checked.trans (by decide +kernel)
  upper_error := v2031_upper_checked
  lower_error := reuse_lower_error 23 77 Primitive.Addresses.material2031

def v2032_pa : Scalar.QComplex := ((999999249789902914483152576678 : Int)/10^30,(-1224916173195473783146718122 : Int)/10^30)
theorem v2032_pa_checked : Scalar.distance (sourceCoefficient 23 78 1 0) v2032_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2032_pb : Scalar.QComplex := ((-528523724941071782454711 : Int)/10^30,(-431477141050773205287511682 : Int)/10^30)
theorem v2032_pb_checked : Scalar.distance (sourceCoefficient 23 78 1 1) v2032_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2032_pg : Scalar.QComplex := ((-93086353994826290506490 : Int)/10^30,(114023066053317277189 : Int)/10^30)
theorem v2032_pg_checked : Scalar.distance (sourceCoefficient 23 78 1 2) v2032_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2032_mb : Scalar.QComplex := ((-900868867865305813612529 : Int)/10^30,(-431476524299943313363454861 : Int)/10^30)
theorem v2032_mb_checked : Scalar.distance (sourceCoefficient 23 78 3 1) v2032_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2032_mg : Scalar.QComplex := ((-93086220937751845937477 : Int)/10^30,(194352354641101034527 : Int)/10^30)
theorem v2032_mg_checked : Scalar.distance (sourceCoefficient 23 78 3 2) v2032_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2032_upper : Scalar.QComplex := ((999995646314297107786701279882 : Int)/10^30,(-2950822334740813742401690538 : Int)/10^30)
theorem v2032_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 78 5) 1) 14) v2032_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2032 : Material (23 : Basis) (78 : Basis) where
  plus := ![v2032_pa,v2032_pb,v2032_pg]
  minus := ![(Primitive.Addresses.material2032 1).one,v2032_mb,v2032_mg]
  upper := v2032_upper
  lower := (Primitive.Addresses.material2032 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2032_pa_checked.trans (by decide +kernel)
    · exact v2032_pb_checked.trans (by decide +kernel)
    · exact v2032_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 78 Primitive.Addresses.material2032
    · exact v2032_mb_checked.trans (by decide +kernel)
    · exact v2032_mg_checked.trans (by decide +kernel)
  upper_error := v2032_upper_checked
  lower_error := reuse_lower_error 23 78 Primitive.Addresses.material2032

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
