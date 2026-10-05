import BecknerOnofri.EntropyScalarCertificate.Bessel0081
import BecknerOnofri.EntropyScalarCertificate.Bessel0082
import BecknerOnofri.EntropyScalarCertificate.Bessel0529
import BecknerOnofri.EntropyScalarCertificate.Bessel0530
import BecknerOnofri.EntropyScalarCertificate.Brackets0032
import BecknerOnofri.EntropyScalarCertificate.Brackets0033
import BecknerOnofri.EntropyScalarCertificate.Logs0065
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0520
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (813063762679068669112797403164976839883/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (813063762679068669112797403164976839883/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (814103886331971809757700196441161736001/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (814103886331971809757700196441161736001/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (406791912252760119717624399901534643971/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (406791912252760119717624399901534643971/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0520 BracketBatch0032.bracket0521 (406791912252760119717624399901534643971/2500000000000000000000000000000000000000) (104393832549473323130114791215896377/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0520 BracketBatch0032.bracket0521
  (406791912252760119717624399901534643971/2500000000000000000000000000000000000000) (104393832549473323130114791215896377/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0520
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0521
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1628207772663943619515400392882323471999/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1628207772663943619515400392882323471999/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (407572056847193141176770090787807956523/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (407572056847193141176770090787807956523/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (3258496000052716184222480756033555298091/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3258496000052716184222480756033555298091/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0521 BracketBatch0032.bracket0522 (3258496000052716184222480756033555298091/20000000000000000000000000000000000000000) (262295792184852686081971683073932943/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0521 BracketBatch0032.bracket0522
  (3258496000052716184222480756033555298091/20000000000000000000000000000000000000000) (262295792184852686081971683073932943/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0521
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0522
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1630288227388772564707080363151231826089/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1630288227388772564707080363151231826089/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (81618444491453776057465891025233975041/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (81618444491453776057465891025233975041/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (3262657117217848085856398183655911326909/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3262657117217848085856398183655911326909/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0522 BracketBatch0032.bracket0523 (3262657117217848085856398183655911326909/20000000000000000000000000000000000000000) (263611959894133462496235098813921647/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0522 BracketBatch0032.bracket0523
  (3262657117217848085856398183655911326909/20000000000000000000000000000000000000000) (263611959894133462496235098813921647/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0522
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0523
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1632368889829075521149317820504679500817/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1632368889829075521149317820504679500817/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1634449760281456943176602638355588660061/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1634449760281456943176602638355588660061/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (1633409325055266232162960229430134080439/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1633409325055266232162960229430134080439/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0523 BracketBatch0032.bracket0524 (1633409325055266232162960229430134080439/10000000000000000000000000000000000000000) (2119464777416293214435759018516743/40000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0523 BracketBatch0032.bracket0524
  (1633409325055266232162960229430134080439/10000000000000000000000000000000000000000) (2119464777416293214435759018516743/40000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0523
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0524
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (817224880140728471588301319177794330029/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (817224880140728471588301319177794330029/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (818265419521337324564847799918499269243/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (818265419521337324564847799918499269243/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (204436287457758224519143639887036699909/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (204436287457758224519143639887036699909/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0524 BracketBatch0032.bracket0525 (204436287457758224519143639887036699909/1250000000000000000000000000000000000000) (133129608363263190797166299937332381/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0524 BracketBatch0032.bracket0525
  (204436287457758224519143639887036699909/1250000000000000000000000000000000000000) (133129608363263190797166299937332381/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0524
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0525
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1636530839042674649129695599836998538483/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1636530839042674649129695599836998538483/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (819306063204820039328282381907544915751/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (819306063204820039328282381907544915751/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (655028593090462945557252072730417673997/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (655028593090462945557252072730417673997/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0525 BracketBatch0032.bracket0526 (655028593090462945557252072730417673997/4000000000000000000000000000000000000000) (535180662506053105423015474463893471/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0525 BracketBatch0032.bracket0526
  (655028593090462945557252072730417673997/4000000000000000000000000000000000000000) (535180662506053105423015474463893471/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0525
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0526
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1638612126409640078656564763815089831499/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1638612126409640078656564763815089831499/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (820346811339709275147178623258159838353/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (820346811339709275147178623258159838353/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (655861149817811725790184402066281901641/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (655861149817811725790184402066281901641/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0526 BracketBatch0032.bracket0527 (655861149817811725790184402066281901641/4000000000000000000000000000000000000000) (13446322674221375517549672851423989/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0526 BracketBatch0032.bracket0527
  (655861149817811725790184402066281901641/4000000000000000000000000000000000000000) (13446322674221375517549672851423989/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0526
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0527
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1640693622679418550294357246516319676703/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1640693622679418550294357246516319676703/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1642775328149229519332970567477114670113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1642775328149229519332970567477114670113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (51304202356697626087926997093647411669/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51304202356697626087926997093647411669/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0065.rows ScalarLogs0065.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0527 BracketBatch0033.bracket0528 (51304202356697626087926997093647411669/312500000000000000000000000000000000000) (540535192332185451686107105542575289/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0527 BracketBatch0033.bracket0528
  (51304202356697626087926997093647411669/312500000000000000000000000000000000000) (540535192332185451686107105542575289/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0527
