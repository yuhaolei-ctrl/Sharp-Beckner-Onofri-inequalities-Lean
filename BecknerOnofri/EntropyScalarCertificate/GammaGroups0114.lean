import BecknerOnofri.EntropyScalarCertificate.Bessel0142
import BecknerOnofri.EntropyScalarCertificate.Bessel0143
import BecknerOnofri.EntropyScalarCertificate.Bessel0560
import BecknerOnofri.EntropyScalarCertificate.Brackets0057
import BecknerOnofri.EntropyScalarCertificate.Logs0114
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0912
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (171691717569272294438127623054833978219/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (171691717569272294438127623054833978219/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (43052625018488542676319059344958991289/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (43052625018488542676319059344958991289/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (2751217741145811721147230883477359547/6400000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2751217741145811721147230883477359547/6400000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0912 BracketBatch0057.bracket0913 (2751217741145811721147230883477359547/6400000000000000000000000000000000000) (20046537901515901003722246584721290229/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0912 BracketBatch0057.bracket0913
  (2751217741145811721147230883477359547/6400000000000000000000000000000000000) (20046537901515901003722246584721290229/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0912
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0913
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (4305262501848854267631905934495899128897/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4305262501848854267631905934495899128897/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (2159125607357205935087484248418064071179/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2159125607357205935087484248418064071179/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (1724702743312653227561374886266405454251/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1724702743312653227561374886266405454251/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0913 BracketBatch0057.bracket0914 (1724702743312653227561374886266405454251/4000000000000000000000000000000000000000) (1266154598203539263784898365066143217/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0913 BracketBatch0057.bracket0914
  (1724702743312653227561374886266405454251/4000000000000000000000000000000000000000) (1266154598203539263784898365066143217/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0913
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0914
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (863650242942882374034993699367225628471/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (863650242942882374034993699367225628471/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (866251835657435625572671145455171315819/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (866251835657435625572671145455171315819/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (172990207860031799960766484482239694429/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (172990207860031799960766484482239694429/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0914 BracketBatch0057.bracket0915 (172990207860031799960766484482239694429/400000000000000000000000000000000000000) (2047215015061851802667838674749292569/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0914 BracketBatch0057.bracket0915
  (172990207860031799960766484482239694429/400000000000000000000000000000000000000) (2047215015061851802667838674749292569/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0914
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0915
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1082814794571794531965838931818964144773/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1082814794571794531965838931818964144773/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (4344286493622139961332897238916232081483/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4344286493622139961332897238916232081483/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (347021826876372723567850118647683546423/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (347021826876372723567850118647683546423/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0915 BracketBatch0057.bracket0916 (347021826876372723567850118647683546423/800000000000000000000000000000000000000) (10343789141931035338931714236995978287/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0915 BracketBatch0057.bracket0916
  (347021826876372723567850118647683546423/800000000000000000000000000000000000000) (10343789141931035338931714236995978287/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0915
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0916
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (108607162340553499033322430972905802037/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (108607162340553499033322430972905802037/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (435733326237564412386944542169587724083/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (435733326237564412386944542169587724083/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (870161975599778408520234266061210932231/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (870161975599778408520234266061210932231/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0916 BracketBatch0057.bracket0917 (870161975599778408520234266061210932231/2000000000000000000000000000000000000000) (20904768665419291638303093889160013797/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0916 BracketBatch0057.bracket0917
  (870161975599778408520234266061210932231/2000000000000000000000000000000000000000) (20904768665419291638303093889160013797/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0916
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0917
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (4357333262375644123869445421695877240827/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4357333262375644123869445421695877240827/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (2185199793405259582601784573886250089383/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2185199793405259582601784573886250089383/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (8727732849186163289073014569468377419593/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8727732849186163289073014569468377419593/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0917 BracketBatch0057.bracket0918 (8727732849186163289073014569468377419593/20000000000000000000000000000000000000000) (10561866020082498419025277876331280051/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0917 BracketBatch0057.bracket0918
  (8727732849186163289073014569468377419593/20000000000000000000000000000000000000000) (10561866020082498419025277876331280051/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0917
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0918
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (4370399586810519165203569147772500178763/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4370399586810519165203569147772500178763/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (273967848112578069114579997713306192573/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (273967848112578069114579997713306192573/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (8753885156611768271036849111185399259931/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8753885156611768271036849111185399259931/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0918 BracketBatch0057.bracket0919 (8753885156611768271036849111185399259931/20000000000000000000000000000000000000000) (21344479203690578837458905059243122387/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0918 BracketBatch0057.bracket0919
  (8753885156611768271036849111185399259931/20000000000000000000000000000000000000000) (21344479203690578837458905059243122387/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0918
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0919
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (876697113960249821166655992682579816233/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (876697113960249821166655992682579816233/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (4396591314839199448472279087823487346023/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4396591314839199448472279087823487346023/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (2195019221160112138576389762809096606797/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2195019221160112138576389762809096606797/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0114.rows ScalarLogs0114.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0919 BracketBatch0057.bracket0920 (2195019221160112138576389762809096606797/5000000000000000000000000000000000000000) (21567021002580261886984668338192237323/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0919 BracketBatch0057.bracket0920
  (2195019221160112138576389762809096606797/5000000000000000000000000000000000000000) (21567021002580261886984668338192237323/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0919
