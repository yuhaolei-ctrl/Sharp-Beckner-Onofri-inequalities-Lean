import BecknerOnofri.EntropyScalarCertificate.Bessel0241
import BecknerOnofri.EntropyScalarCertificate.Bessel0242
import BecknerOnofri.EntropyScalarCertificate.Bessel0609
import BecknerOnofri.EntropyScalarCertificate.Bessel0610
import BecknerOnofri.EntropyScalarCertificate.Brackets0096
import BecknerOnofri.EntropyScalarCertificate.Brackets0097
import BecknerOnofri.EntropyScalarCertificate.Logs0193
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1544
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (18044941804088762140946066171265154685039/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18044941804088762140946066171265154685039/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (4513804522928929845027890349757993474339/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4513804522928929845027890349757993474339/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (7220031979160896304211525514059425716479/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7220031979160896304211525514059425716479/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1544 BracketBatch0096.bracket1545 (7220031979160896304211525514059425716479/4000000000000000000000000000000000000000) (349441212217162905002678298914839737629/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1544 BracketBatch0096.bracket1545
  (7220031979160896304211525514059425716479/4000000000000000000000000000000000000000) (349441212217162905002678298914839737629/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1544
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1545
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (18055218091715719380111561399031973897353/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18055218091715719380111561399031973897353/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (9032753903328717375540467663300529990123/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9032753903328717375540467663300529990123/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (36120725898373154131192496725633033877599/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36120725898373154131192496725633033877599/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1545 BracketBatch0096.bracket1546 (36120725898373154131192496725633033877599/20000000000000000000000000000000000000000) (699434796831171805355482744190741952481/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1545 BracketBatch0096.bracket1546
  (36120725898373154131192496725633033877599/20000000000000000000000000000000000000000) (699434796831171805355482744190741952481/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1545
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1546
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (18065507806657434751080935326601059980243/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18065507806657434751080935326601059980243/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2259476372108448863790671153689059402037/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2259476372108448863790671153689059402037/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (36141318783525025661406304556113535196539/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36141318783525025661406304556113535196539/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1546 BracketBatch0096.bracket1547 (36141318783525025661406304556113535196539/20000000000000000000000000000000000000000) (349993876869406038196798629459454594339/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1546 BracketBatch0096.bracket1547
  (36141318783525025661406304556113535196539/20000000000000000000000000000000000000000) (349993876869406038196798629459454594339/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1546
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1547
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (18075810976867590910325369229512475216293/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18075810976867590910325369229512475216293/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (3617225526074834137021119813522055262361/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3617225526074834137021119813522055262361/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (18080969303620880797715484148561375764049/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18080969303620880797715484148561375764049/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1547 BracketBatch0096.bracket1548 (18080969303620880797715484148561375764049/10000000000000000000000000000000000000000) (175135324014018260699555087505183598407/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1547 BracketBatch0096.bracket1548
  (18080969303620880797715484148561375764049/10000000000000000000000000000000000000000) (175135324014018260699555087505183598407/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1547
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1548
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (9043063815187085342552799533805138155901/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9043063815187085342552799533805138155901/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (2262057224409961640735533342011082011047/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2262057224409961640735533342011082011047/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (18091292712826931905494932901849466200089/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18091292712826931905494932901849466200089/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1548 BracketBatch0096.bracket1549 (18091292712826931905494932901849466200089/10000000000000000000000000000000000000000) (350547712341737451745616464000203873637/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1548 BracketBatch0096.bracket1549
  (18091292712826931905494932901849466200089/10000000000000000000000000000000000000000) (350547712341737451745616464000203873637/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1548
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1549
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (18096457795279693125884266736088656088373/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18096457795279693125884266736088656088373/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (18106801499761450439724026032301674233649/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18106801499761450439724026032301674233649/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (18101629647520571782804146384195165161011/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18101629647520571782804146384195165161011/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1549 BracketBatch0096.bracket1550 (18101629647520571782804146384195165161011/10000000000000000000000000000000000000000) (70165014052323499947361446006935200007/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1549 BracketBatch0096.bracket1550
  (18101629647520571782804146384195165161011/10000000000000000000000000000000000000000) (70165014052323499947361446006935200007/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1549
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1550
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (9053400749880725219862013016150837116823/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9053400749880725219862013016150837116823/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (4529289693017936452144466850195739922479/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4529289693017936452144466850195739922479/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (18111980135916598124150946716542316961781/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18111980135916598124150946716542316961781/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1550 BracketBatch0096.bracket1551 (18111980135916598124150946716542316961781/10000000000000000000000000000000000000000) (140441088895854236802141812090898862449/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1550 BracketBatch0096.bracket1551
  (18111980135916598124150946716542316961781/10000000000000000000000000000000000000000) (140441088895854236802141812090898862449/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1550
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1551
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (18117158772071745808577867400782959689913/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18117158772071745808577867400782959689913/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (18127529640538132096398966416894488275159/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18127529640538132096398966416894488275159/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (2265293025788117369061052113604840497817/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2265293025788117369061052113604840497817/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0193.rows ScalarLogs0193.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1551 BracketBatch0097.bracket1552 (2265293025788117369061052113604840497817/1250000000000000000000000000000000000000) (351380668728602600097977313638419993863/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1551 BracketBatch0097.bracket1552
  (2265293025788117369061052113604840497817/1250000000000000000000000000000000000000) (351380668728602600097977313638419993863/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1551
