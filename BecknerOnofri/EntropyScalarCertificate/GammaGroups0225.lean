import BecknerOnofri.EntropyScalarCertificate.Bessel0281
import BecknerOnofri.EntropyScalarCertificate.Bessel0282
import BecknerOnofri.EntropyScalarCertificate.Bessel0629
import BecknerOnofri.EntropyScalarCertificate.Bessel0630
import BecknerOnofri.EntropyScalarCertificate.Brackets0112
import BecknerOnofri.EntropyScalarCertificate.Brackets0113
import BecknerOnofri.EntropyScalarCertificate.Logs0225
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1800
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (10603321303135945453767654329575087558179/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10603321303135945453767654329575087558179/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (21221524826478998449632657146479869343769/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21221524826478998449632657146479869343769/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (42428167432750889357167965805630044460127/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42428167432750889357167965805630044460127/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1800 BracketBatch0112.bracket1801 (42428167432750889357167965805630044460127/20000000000000000000000000000000000000000) (862180996817036804343842533960893922897/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1800 BracketBatch0112.bracket1801
  (42428167432750889357167965805630044460127/20000000000000000000000000000000000000000) (862180996817036804343842533960893922897/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1800
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1801
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (10610762413239499224816328573239934671883/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10610762413239499224816328573239934671883/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1327276931620185652600863581630675146849/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1327276931620185652600863581630675146849/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (849159114648039377824929489051413433867/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (849159114648039377824929489051413433867/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1801 BracketBatch0112.bracket1802 (849159114648039377824929489051413433867/400000000000000000000000000000000000000) (86291768955883208304430831018445615059/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1801 BracketBatch0112.bracket1802
  (849159114648039377824929489051413433867/400000000000000000000000000000000000000) (86291768955883208304430831018445615059/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1801
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1802
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (21236430905922970441613817306090802349581/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21236430905922970441613817306090802349581/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (5312840225662053235567278416477770056527/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5312840225662053235567278416477770056527/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (42487791808571183383882930972001882575689/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42487791808571183383882930972001882575689/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1802 BracketBatch0112.bracket1803 (42487791808571183383882930972001882575689/20000000000000000000000000000000000000000) (863655263147130291135366873397161893543/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1802 BracketBatch0112.bracket1803
  (42487791808571183383882930972001882575689/20000000000000000000000000000000000000000) (863655263147130291135366873397161893543/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1802
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1803
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (4250272180529642588453822733182216045221/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4250272180529642588453822733182216045221/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (21266314874878670031034772414989253769461/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21266314874878670031034772414989253769461/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (21258837888763441486651943040450166997783/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21258837888763441486651943040450166997783/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1803 BracketBatch0112.bracket1804 (21258837888763441486651943040450166997783/10000000000000000000000000000000000000000) (43219685952625193817629001433587893151/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1803 BracketBatch0112.bracket1804
  (21258837888763441486651943040450166997783/10000000000000000000000000000000000000000) (43219685952625193817629001433587893151/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1803
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1804
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (10633157437439335015517386207494626884729/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10633157437439335015517386207494626884729/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (21281292881018505013428726673547493274613/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21281292881018505013428726673547493274613/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (42547607755897175044463499088536747044071/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42547607755897175044463499088536747044071/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1804 BracketBatch0112.bracket1805 (42547607755897175044463499088536747044071/20000000000000000000000000000000000000000) (216283264687116121596750216941694208283/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1804 BracketBatch0112.bracket1805
  (42547607755897175044463499088536747044071/20000000000000000000000000000000000000000) (216283264687116121596750216941694208283/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1804
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1805
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (2128129288101850501342872667354749327461/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2128129288101850501342872667354749327461/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (66550921811414952496557787985744686933/31250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (66550921811414952496557787985744686933/31250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (4257758786067128981232721882898579309317/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4257758786067128981232721882898579309317/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1805 BracketBatch0112.bracket1806 (4257758786067128981232721882898579309317/2000000000000000000000000000000000000000) (865873283711470308667394856725894407393/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1805 BracketBatch0112.bracket1806
  (4257758786067128981232721882898579309317/2000000000000000000000000000000000000000) (865873283711470308667394856725894407393/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1805
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1806
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (21296294979652784798898492155438299818557/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21296294979652784798898492155438299818557/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2663915153693520933628532668877644910873/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2663915153693520933628532668877644910873/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (42607616209200952267926753506459459105541/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42607616209200952267926753506459459105541/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1806 BracketBatch0112.bracket1807 (42607616209200952267926753506459459105541/20000000000000000000000000000000000000000) (866614395420933441302649073482814123011/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1806 BracketBatch0112.bracket1807
  (42607616209200952267926753506459459105541/20000000000000000000000000000000000000000) (866614395420933441302649073482814123011/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1806
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1807
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (21311321229548167469028261351021159286981/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21311321229548167469028261351021159286981/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2665796461206699131771292264313921344617/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2665796461206699131771292264313921344617/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (42637692919201760523198599465532530043917/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42637692919201760523198599465532530043917/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0225.rows ScalarLogs0225.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1807 BracketBatch0113.bracket1808 (42637692919201760523198599465532530043917/20000000000000000000000000000000000000000) (34694255814369091815721880482844723911/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1807 BracketBatch0113.bracket1808
  (42637692919201760523198599465532530043917/20000000000000000000000000000000000000000) (34694255814369091815721880482844723911/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1807
