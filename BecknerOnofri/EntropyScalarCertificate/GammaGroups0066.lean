import BecknerOnofri.EntropyScalarCertificate.Bessel0082
import BecknerOnofri.EntropyScalarCertificate.Bessel0083
import BecknerOnofri.EntropyScalarCertificate.Bessel0530
import BecknerOnofri.EntropyScalarCertificate.Brackets0033
import BecknerOnofri.EntropyScalarCertificate.Logs0066
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0528
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (164277532814922951933297056747711467011/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (164277532814922951933297056747711467011/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (164485724311644683596078867025567832657/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (164485724311644683596078867025567832657/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (82190814281641908882343980943319824917/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (82190814281641908882343980943319824917/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0528 BracketBatch0033.bracket0529 (82190814281641908882343980943319824917/500000000000000000000000000000000000000) (13580688603043274457200013580196009/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0528 BracketBatch0033.bracket0529
  (82190814281641908882343980943319824917/500000000000000000000000000000000000000) (13580688603043274457200013580196009/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0528
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0529
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1644857243116446835960788670255678326567/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1644857243116446835960788670255678326567/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (32938787357571980073862973847616114003/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (32938787357571980073862973847616114003/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (3291796610995045839653937362636484026717/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3291796610995045839653937362636484026717/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0529 BracketBatch0033.bracket0530 (3291796610995045839653937362636484026717/20000000000000000000000000000000000000000) (136482496974537806020996757573413601/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0529 BracketBatch0033.bracket0530
  (3291796610995045839653937362636484026717/20000000000000000000000000000000000000000) (136482496974537806020996757573413601/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0529
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0530
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1646939367878599003693148692380805700147/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1646939367878599003693148692380805700147/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1649021702733369438084105525357460399147/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1649021702733369438084105525357460399147/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (1647980535305984220888627108869133049647/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1647980535305984220888627108869133049647/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0530 BracketBatch0033.bracket0531 (1647980535305984220888627108869133049647/10000000000000000000000000000000000000000) (274321274628546142088062329718936161/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0530 BracketBatch0033.bracket0531
  (1647980535305984220888627108869133049647/10000000000000000000000000000000000000000) (274321274628546142088062329718936161/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0530
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0531
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (206127712841671179760513190669682549893/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (206127712841671179760513190669682549893/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1651104247978596725722062174208571798057/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1651104247978596725722062174208571798057/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (3300125950711966163806167699566032197201/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3300125950711966163806167699566032197201/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0531 BracketBatch0033.bracket0532 (3300125950711966163806167699566032197201/20000000000000000000000000000000000000000) (17230164182162505453910949453472727/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0531 BracketBatch0033.bracket0532
  (3300125950711966163806167699566032197201/20000000000000000000000000000000000000000) (17230164182162505453910949453472727/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0531
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0532
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (825552123989298362861031087104285899027/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (825552123989298362861031087104285899027/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (66127480156490995340393395880495268399/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (66127480156490995340393395880495268399/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (3304291251890871609231897071220953508029/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3304291251890871609231897071220953508029/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0532 BracketBatch0033.bracket0533 (3304291251890871609231897071220953508029/20000000000000000000000000000000000000000) (554098127280134302774812913301059971/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0532 BracketBatch0033.bracket0533
  (3304291251890871609231897071220953508029/20000000000000000000000000000000000000000) (554098127280134302774812913301059971/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0532
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0533
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (413296750978068720877458724253095427493/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (413296750978068720877458724253095427493/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1655269970832553618229723078200054031737/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1655269970832553618229723078200054031737/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (3308456974744828501739557975212435741709/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3308456974744828501739557975212435741709/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0533 BracketBatch0033.bracket0534 (3308456974744828501739557975212435741709/20000000000000000000000000000000000000000) (556841195310580960588133865303507549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0533 BracketBatch0033.bracket0534
  (3308456974744828501739557975212435741709/20000000000000000000000000000000000000000) (556841195310580960588133865303507549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0533
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0534
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (827634985416276809114861539100027015867/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (827634985416276809114861539100027015867/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (331470629807547717278830953002903379863/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (331470629807547717278830953002903379863/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (3312623119870292204623877843214570931049/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3312623119870292204623877843214570931049/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0534 BracketBatch0033.bracket0535 (3312623119870292204623877843214570931049/20000000000000000000000000000000000000000) (559594483656266837516174193673286361/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0534 BracketBatch0033.bracket0535
  (3312623119870292204623877843214570931049/20000000000000000000000000000000000000000) (559594483656266837516174193673286361/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0534
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0535
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (103584571814858661649634672813407306207/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (103584571814858661649634672813407306207/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (12964347959580403549863123238312568887/78125000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12964347959580403549863123238312568887/78125000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (207299355491501890048539658719907857303/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (207299355491501890048539658719907857303/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0066.rows ScalarLogs0066.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0535 BracketBatch0033.bracket0536 (207299355491501890048539658719907857303/1250000000000000000000000000000000000000) (562358018087972556419925202608331411/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0535 BracketBatch0033.bracket0536
  (207299355491501890048539658719907857303/1250000000000000000000000000000000000000) (562358018087972556419925202608331411/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0535
