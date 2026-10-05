import BecknerOnofri.EntropyScalarCertificate.Bessel0348
import BecknerOnofri.EntropyScalarCertificate.Bessel0349
import BecknerOnofri.EntropyScalarCertificate.Bessel0350
import BecknerOnofri.EntropyScalarCertificate.Bessel0663
import BecknerOnofri.EntropyScalarCertificate.Brackets0139
import BecknerOnofri.EntropyScalarCertificate.Brackets0140
import BecknerOnofri.EntropyScalarCertificate.Logs0279
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2232
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (102925273225837151088185315216014608944101/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (102925273225837151088185315216014608944101/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (25834964753242604505285443662547481304791/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (25834964753242604505285443662547481304791/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (41253026447761513821865417973240906832653/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41253026447761513821865417973240906832653/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2232 BracketBatch0139.bracket2233 (41253026447761513821865417973240906832653/4000000000000000000000000000000000000000) (1401077582473302766442596668638248302301/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2232 BracketBatch0139.bracket2233
  (41253026447761513821865417973240906832653/4000000000000000000000000000000000000000) (1401077582473302766442596668638248302301/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2232
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2233
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (103339859012970418021141774650189925219161/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (103339859012970418021141774650189925219161/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (5187892246408123319617040865881160432679/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5187892246408123319617040865881160432679/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (207097703941132884413482591967813133872741/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (207097703941132884413482591967813133872741/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2233 BracketBatch0139.bracket2234 (207097703941132884413482591967813133872741/20000000000000000000000000000000000000000) (2807481222277208398002743077893034333793/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2233 BracketBatch0139.bracket2234
  (207097703941132884413482591967813133872741/20000000000000000000000000000000000000000) (2807481222277208398002743077893034333793/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2233
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2234
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (103757844928162466392340817317623208653577/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (103757844928162466392340817317623208653577/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (104179272946545395086126096690178589675951/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (104179272946545395086126096690178589675951/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (25992139734338482684808364250975224791191/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25992139734338482684808364250975224791191/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2234 BracketBatch0139.bracket2235 (25992139734338482684808364250975224791191/2500000000000000000000000000000000000000) (2812830620519186446678964547936801805837/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2234 BracketBatch0139.bracket2235
  (25992139734338482684808364250975224791191/2500000000000000000000000000000000000000) (2812830620519186446678964547936801805837/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2234
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2235
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (26044818236636348771531524172544647418987/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26044818236636348771531524172544647418987/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (4184167429482347050786009263141265994309/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4184167429482347050786009263141265994309/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (208783458683604071355776328268710239533673/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (208783458683604071355776328268710239533673/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2235 BracketBatch0139.bracket2236 (208783458683604071355776328268710239533673/20000000000000000000000000000000000000000) (352275443676949679332321038619272375147/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2235 BracketBatch0139.bracket2236
  (208783458683604071355776328268710239533673/20000000000000000000000000000000000000000) (352275443676949679332321038619272375147/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2235
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2236
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (52302092868529338134825115789265824928861/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (52302092868529338134825115789265824928861/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1641134791825679473848572669653401365503/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1641134791825679473848572669653401365503/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (104818406206951081297979441218174668624957/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (104818406206951081297979441218174668624957/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2236 BracketBatch0139.bracket2237 (104818406206951081297979441218174668624957/10000000000000000000000000000000000000000) (2823600200908298711468281566563816254049/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2236 BracketBatch0139.bracket2237
  (104818406206951081297979441218174668624957/10000000000000000000000000000000000000000) (2823600200908298711468281566563816254049/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2236
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2237
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (105032626676843486326308650857817687392189/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (105032626676843486326308650857817687392189/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (105464639865996895139338318034642951642007/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (105464639865996895139338318034642951642007/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (52624316635710095366411742223115159758549/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (52624316635710095366411742223115159758549/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2237 BracketBatch0139.bracket2238 (52624316635710095366411742223115159758549/5000000000000000000000000000000000000000) (1414510384584766865421456735561959272361/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2237 BracketBatch0139.bracket2238
  (52624316635710095366411742223115159758549/5000000000000000000000000000000000000000) (1414510384584766865421456735561959272361/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2237
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2238
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (26366159966499223784834579508660737910501/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26366159966499223784834579508660737910501/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (52950135071348226754592720976292537071521/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52950135071348226754592720976292537071521/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (105682455004346674324261879993614012892523/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (105682455004346674324261879993614012892523/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2238 BracketBatch0139.bracket2239 (105682455004346674324261879993614012892523/10000000000000000000000000000000000000000) (177154090664626373542723208149788261051/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2238 BracketBatch0139.bracket2239
  (105682455004346674324261879993614012892523/10000000000000000000000000000000000000000) (177154090664626373542723208149788261051/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2238
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2239
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (105900270142696453509185441952585074143039/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (105900270142696453509185441952585074143039/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (21267912619741214553339374656306868507267/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21267912619741214553339374656306868507267/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (106119916620701263137941157617059708339687/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (106119916620701263137941157617059708339687/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0279.rows ScalarLogs0279.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2239 BracketBatch0140.bracket2240 (106119916620701263137941157617059708339687/10000000000000000000000000000000000000000) (283993444403155956027994003625092058399/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2239 BracketBatch0140.bracket2240
  (106119916620701263137941157617059708339687/10000000000000000000000000000000000000000) (283993444403155956027994003625092058399/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2239
