import BecknerOnofri.EntropyScalarCertificate.Bessel0057
import BecknerOnofri.EntropyScalarCertificate.Bessel0058
import BecknerOnofri.EntropyScalarCertificate.Bessel0517
import BecknerOnofri.EntropyScalarCertificate.Bessel0518
import BecknerOnofri.EntropyScalarCertificate.Brackets0023
import BecknerOnofri.EntropyScalarCertificate.Logs0046
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0368
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1312168211228660587099675376994720646949/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1312168211228660587099675376994720646949/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1314220292341847672792604407964563994243/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1314220292341847672792604407964563994243/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (328298562946313532486534973119910580149/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (328298562946313532486534973119910580149/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0368 BracketBatch0023.bracket0369 (328298562946313532486534973119910580149/2500000000000000000000000000000000000000) (112151448963803199600145977877593229/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0368 BracketBatch0023.bracket0369
  (328298562946313532486534973119910580149/2500000000000000000000000000000000000000) (112151448963803199600145977877593229/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0368
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0369
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (2053469206784136988738444387444631241/15625000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2053469206784136988738444387444631241/15625000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (658136268723231097415364126813101300259/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (658136268723231097415364126813101300259/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (1315246414894154933811666330795383297379/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1315246414894154933811666330795383297379/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0369 BracketBatch0023.bracket0370 (1315246414894154933811666330795383297379/10000000000000000000000000000000000000000) (28211584030676476311983868989642763/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0369 BracketBatch0023.bracket0370
  (1315246414894154933811666330795383297379/10000000000000000000000000000000000000000) (28211584030676476311983868989642763/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0369
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0370
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (263254507489292438966145650725240520103/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (263254507489292438966145650725240520103/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (131832494681851683316722274214613216139/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (131832494681851683316722274214613216139/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (526919496852995805599590199154466952381/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (526919496852995805599590199154466952381/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0370 BracketBatch0023.bracket0371 (526919496852995805599590199154466952381/4000000000000000000000000000000000000000) (5677222639885049612919083584673293/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0370 BracketBatch0023.bracket0371
  (526919496852995805599590199154466952381/4000000000000000000000000000000000000000) (5677222639885049612919083584673293/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0370
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0371
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1318324946818516833167222742146132161387/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1318324946818516833167222742146132161387/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (660188760367070626709022077522468973983/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (660188760367070626709022077522468973983/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (2638702467552658086585266897191070109353/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2638702467552658086585266897191070109353/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0371 BracketBatch0023.bracket0372 (2638702467552658086585266897191070109353/20000000000000000000000000000000000000000) (114245809083227320849768918344591727/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0371 BracketBatch0023.bracket0372
  (2638702467552658086585266897191070109353/20000000000000000000000000000000000000000) (114245809083227320849768918344591727/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0371
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0372
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1320377520734141253418044155044937947963/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1320377520734141253418044155044937947963/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1322430259469582327276317088578284421639/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1322430259469582327276317088578284421639/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (1321403890101861790347180621811611184801/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1321403890101861790347180621811611184801/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0372 BracketBatch0023.bracket0373 (1321403890101861790347180621811611184801/10000000000000000000000000000000000000000) (57475207545142289189252450147979713/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0372 BracketBatch0023.bracket0373
  (1321403890101861790347180621811611184801/10000000000000000000000000000000000000000) (57475207545142289189252450147979713/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0372
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0373
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (330607564867395581819079272144571105409/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (330607564867395581819079272144571105409/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (41390098853162636035358937510544496773/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41390098853162636035358937510544496773/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (661728355692696670101950772228927079593/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (661728355692696670101950772228927079593/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0373 BracketBatch0023.bracket0374 (661728355692696670101950772228927079593/5000000000000000000000000000000000000000) (231316561892876847774667441456494977/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0373 BracketBatch0023.bracket0374
  (661728355692696670101950772228927079593/5000000000000000000000000000000000000000) (231316561892876847774667441456494977/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0373
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0374
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (1324483163301204353131486000337423896733/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1324483163301204353131486000337423896733/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1326536232505489276893671691531537584659/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1326536232505489276893671691531537584659/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (165688712237918351876572355741810092587/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (165688712237918351876572355741810092587/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0374 BracketBatch0023.bracket0375 (165688712237918351876572355741810092587/1250000000000000000000000000000000000000) (46547766718330256807534355555421383/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0374 BracketBatch0023.bracket0375
  (165688712237918351876572355741810092587/1250000000000000000000000000000000000000) (46547766718330256807534355555421383/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0374
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0375
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (82908514531593079805854480720721099041/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (82908514531593079805854480720721099041/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1328589467359036913023674638837111541339/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1328589467359036913023674638837111541339/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (531025139972905237983469266073729825199/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (531025139972905237983469266073729825199/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0046.rows ScalarLogs0046.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0375 BracketBatch0023.bracket0376 (531025139972905237983469266073729825199/4000000000000000000000000000000000000000) (234167665598318612603234454683951669/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0375 BracketBatch0023.bracket0376
  (531025139972905237983469266073729825199/4000000000000000000000000000000000000000) (234167665598318612603234454683951669/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0375
