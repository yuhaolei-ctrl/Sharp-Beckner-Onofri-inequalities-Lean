import BecknerOnofri.EntropyScalarCertificate.Bessel0383
import BecknerOnofri.EntropyScalarCertificate.Bessel0384
import BecknerOnofri.EntropyScalarCertificate.Bessel0385
import BecknerOnofri.EntropyScalarCertificate.Bessel0680
import BecknerOnofri.EntropyScalarCertificate.Bessel0681
import BecknerOnofri.EntropyScalarCertificate.Brackets0153
import BecknerOnofri.EntropyScalarCertificate.Brackets0154
import BecknerOnofri.EntropyScalarCertificate.Logs0307
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2456
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (297474700598342880752248554633150229122137/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (297474700598342880752248554633150229122137/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (149089122323973070665889537795756519046009/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (149089122323973070665889537795756519046009/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (119130589049257804416805526044932653442831/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (119130589049257804416805526044932653442831/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2456 BracketBatch0153.bracket2457 (119130589049257804416805526044932653442831/4000000000000000000000000000000000000000) (2142811813720223759461296471847419063251/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2456 BracketBatch0153.bracket2457
  (119130589049257804416805526044932653442831/4000000000000000000000000000000000000000) (2142811813720223759461296471847419063251/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2456
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2457
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (59635648929589228266355815118302607618403/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (59635648929589228266355815118302607618403/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (37360642387239124912496368645332334195379/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (37360642387239124912496368645332334195379/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (597063383745859140631750024754171711655047/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (597063383745859140631750024754171711655047/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2457 BracketBatch0153.bracket2458 (597063383745859140631750024754171711655047/20000000000000000000000000000000000000000) (1072259879884414230885350546064277148371/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2457 BracketBatch0153.bracket2458
  (597063383745859140631750024754171711655047/20000000000000000000000000000000000000000) (1072259879884414230885350546064277148371/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2457
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2458
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (298885139097912999299970949162658673563029/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (298885139097912999299970949162658673563029/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (299595407936759632790284883578059219483901/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (299595407936759632790284883578059219483901/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (59848054703467263209025583274071789304693/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (59848054703467263209025583274071789304693/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2458 BracketBatch0153.bracket2459 (59848054703467263209025583274071789304693/2000000000000000000000000000000000000000) (4292464004215735256295231522918081904533/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2458 BracketBatch0153.bracket2459
  (59848054703467263209025583274071789304693/2000000000000000000000000000000000000000) (4292464004215735256295231522918081904533/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2458
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2459
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (149797703968379816395142441789029609741949/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (149797703968379816395142441789029609741949/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (150154537691278704293201575145915033009761/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (150154537691278704293201575145915033009761/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (29995224165965852068834401693494464275171/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29995224165965852068834401693494464275171/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2459 BracketBatch0153.bracket2460 (29995224165965852068834401693494464275171/1000000000000000000000000000000000000000) (4295897122286490446627181961340615420391/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2459 BracketBatch0153.bracket2460
  (29995224165965852068834401693494464275171/1000000000000000000000000000000000000000) (4295897122286490446627181961340615420391/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2459
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2460
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (300309075382557408586403150291830066019519/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (300309075382557408586403150291830066019519/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (75256541471421335603083698378611218197579/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (75256541471421335603083698378611218197579/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (120267048253648550199747588761254987761967/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (120267048253648550199747588761254987761967/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2460 BracketBatch0153.bracket2461 (120267048253648550199747588761254987761967/4000000000000000000000000000000000000000) (429933891484506945577994250888699458611/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2460 BracketBatch0153.bracket2461
  (120267048253648550199747588761254987761967/4000000000000000000000000000000000000000) (429933891484506945577994250888699458611/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2460
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2461
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (301026165885685342412334793514444872790313/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (301026165885685342412334793514444872790313/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (301746704131622258169017288425059278676029/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (301746704131622258169017288425059278676029/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (301386435008653800290676040969752075733171/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (301386435008653800290676040969752075733171/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2461 BracketBatch0153.bracket2462 (301386435008653800290676040969752075733171/10000000000000000000000000000000000000000) (1075697355818130773772175788750849501017/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2461 BracketBatch0153.bracket2462
  (301386435008653800290676040969752075733171/10000000000000000000000000000000000000000) (1075697355818130773772175788750849501017/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2461
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2462
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (150873352065811129084508644212529639338013/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (150873352065811129084508644212529639338013/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (30247071504377931573819892020490762366509/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30247071504377931573819892020490762366509/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (151054354793850393476804052157491725585279/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (151054354793850393476804052157491725585279/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2462 BracketBatch0153.bracket2463 (151054354793850393476804052157491725585279/5000000000000000000000000000000000000000) (107656217230959977206790766538701722403/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2462 BracketBatch0153.bracket2463
  (151054354793850393476804052157491725585279/5000000000000000000000000000000000000000) (107656217230959977206790766538701722403/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2462
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2463
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (302470715043779315738198920204907623665087/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (302470715043779315738198920204907623665087/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (303198223786373589913918219272299249411449/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (303198223786373589913918219272299249411449/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (75708617353769113206514642434650859134567/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (75708617353769113206514642434650859134567/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0307.rows ScalarLogs0307.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2463 BracketBatch0154.bracket2464 (75708617353769113206514642434650859134567/2500000000000000000000000000000000000000) (269357297168960233563185131720459608039/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2463 BracketBatch0154.bracket2464
  (75708617353769113206514642434650859134567/2500000000000000000000000000000000000000) (269357297168960233563185131720459608039/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2463
