import BecknerOnofri.EntropyScalarCertificate.Bessel0118
import BecknerOnofri.EntropyScalarCertificate.Bessel0119
import BecknerOnofri.EntropyScalarCertificate.Bessel0120
import BecknerOnofri.EntropyScalarCertificate.Bessel0548
import BecknerOnofri.EntropyScalarCertificate.Brackets0047
import BecknerOnofri.EntropyScalarCertificate.Brackets0048
import BecknerOnofri.EntropyScalarCertificate.Logs0095
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0760
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1247262602352268912896655144993086004049/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1247262602352268912896655144993086004049/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (501097088457766821481752290632520463933/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (501097088457766821481752290632520463933/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (5000010646993371933202071743148774327763/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5000010646993371933202071743148774327763/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0760 BracketBatch0047.bracket0761 (5000010646993371933202071743148774327763/20000000000000000000000000000000000000000) (1361867268416321511902460288236947557/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0760 BracketBatch0047.bracket0761
  (5000010646993371933202071743148774327763/20000000000000000000000000000000000000000) (1361867268416321511902460288236947557/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0760
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0761
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1252742721144417053704380726581301159831/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1252742721144417053704380726581301159831/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (251645432225905015342358260656812718727/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (251645432225905015342358260656812718727/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1255484941136971065208086014932682376733/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1255484941136971065208086014932682376733/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0761 BracketBatch0047.bracket0762 (1255484941136971065208086014932682376733/5000000000000000000000000000000000000000) (1384890704351672374491849886063231979/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0761 BracketBatch0047.bracket0762
  (1255484941136971065208086014932682376733/5000000000000000000000000000000000000000) (1384890704351672374491849886063231979/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0761
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0762
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2516454322259050153423582606568127187267/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2516454322259050153423582606568127187267/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (252743189283412077651548284644185849429/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (252743189283412077651548284644185849429/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (5043886215093170929939065453009985681557/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5043886215093170929939065453009985681557/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0762 BracketBatch0047.bracket0763 (5043886215093170929939065453009985681557/20000000000000000000000000000000000000000) (2816414812134782251403429081483662547/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0762 BracketBatch0047.bracket0763
  (5043886215093170929939065453009985681557/20000000000000000000000000000000000000000) (2816414812134782251403429081483662547/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0762
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0763
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2527431892834120776515482846441858494287/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2527431892834120776515482846441858494287/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1269209101207799027955337379991600014951/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1269209101207799027955337379991600014951/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (5065850095249718832426157606425058524189/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5065850095249718832426157606425058524189/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0763 BracketBatch0047.bracket0764 (5065850095249718832426157606425058524189/20000000000000000000000000000000000000000) (2863639894366224841796802703231321391/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0763 BracketBatch0047.bracket0764
  (5065850095249718832426157606425058524189/20000000000000000000000000000000000000000) (2863639894366224841796802703231321391/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0763
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0764
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (2538418202415598055910674759983200029899/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2538418202415598055910674759983200029899/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2549413299589020663901664339853375268631/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2549413299589020663901664339853375268631/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (508783150200461871981233909983657529853/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (508783150200461871981233909983657529853/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0764 BracketBatch0047.bracket0765 (508783150200461871981233909983657529853/2000000000000000000000000000000000000000) (1455730914615310025020301910336847229/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0764 BracketBatch0047.bracket0765
  (508783150200461871981233909983657529853/2000000000000000000000000000000000000000) (1455730914615310025020301910336847229/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0764
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0765
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (637353324897255165975416084963343817157/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (637353324897255165975416084963343817157/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1280208616562646578470878585260048012309/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1280208616562646578470878585260048012309/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (2554915266357156910421710755186735646623/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2554915266357156910421710755186735646623/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0765 BracketBatch0047.bracket0766 (2554915266357156910421710755186735646623/10000000000000000000000000000000000000000) (2959885817231380151382779788322945337/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0765 BracketBatch0047.bracket0766
  (2554915266357156910421710755186735646623/10000000000000000000000000000000000000000) (2959885817231380151382779788322945337/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0765
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0766
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (512083446625058631388351434104019204923/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (512083446625058631388351434104019204923/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (2571430051982075329920462418549385573801/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2571430051982075329920462418549385573801/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (320740455319210530428888724316842599901/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (320740455319210530428888724316842599901/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0766 BracketBatch0047.bracket0767 (320740455319210530428888724316842599901/1250000000000000000000000000000000000000) (3008917085619708896088060160607116519/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0766 BracketBatch0047.bracket0767
  (320740455319210530428888724316842599901/1250000000000000000000000000000000000000) (3008917085619708896088060160607116519/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0766
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0767
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1285715025991037664960231209274692786899/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1285715025991037664960231209274692786899/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (2582451805305181733266997525551832163061/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2582451805305181733266997525551832163061/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (5153881857287257063187459944101217736859/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5153881857287257063187459944101217736859/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0095.rows ScalarLogs0095.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0767 BracketBatch0048.bracket0768 (5153881857287257063187459944101217736859/20000000000000000000000000000000000000000) (122342435538898883819614981200312181/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0767 BracketBatch0048.bracket0768
  (5153881857287257063187459944101217736859/20000000000000000000000000000000000000000) (122342435538898883819614981200312181/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0767
