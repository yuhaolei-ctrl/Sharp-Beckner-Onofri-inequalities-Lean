import BecknerOnofri.EntropyScalarCertificate.Bessel0416
import BecknerOnofri.EntropyScalarCertificate.Bessel0417
import BecknerOnofri.EntropyScalarCertificate.Bessel0697
import BecknerOnofri.EntropyScalarCertificate.Brackets0166
import BecknerOnofri.EntropyScalarCertificate.Brackets0167
import BecknerOnofri.EntropyScalarCertificate.Logs0333
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2664
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (585370261789487840089060785050924059661743/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (585370261789487840089060785050924059661743/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (294056267015262396181355470222223396991733/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (294056267015262396181355470222223396991733/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (1173482795820012632451771725495370853645209/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1173482795820012632451771725495370853645209/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2664 BracketBatch0166.bracket2665 (1173482795820012632451771725495370853645209/20000000000000000000000000000000000000000) (2638530822454353770560608210427069158691/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2664 BracketBatch0166.bracket2665
  (1173482795820012632451771725495370853645209/20000000000000000000000000000000000000000) (2638530822454353770560608210427069158691/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2664
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2665
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (588112534030524792362710940444446793983463/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (588112534030524792362710940444446793983463/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (295440338564923836391725487509794230085073/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (295440338564923836391725487509794230085073/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (1178993211160372465146161915464035254153609/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1178993211160372465146161915464035254153609/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2665 BracketBatch0166.bracket2666 (1178993211160372465146161915464035254153609/20000000000000000000000000000000000000000) (5283923778161071103424114573796672324767/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2665 BracketBatch0166.bracket2666
  (1178993211160372465146161915464035254153609/20000000000000000000000000000000000000000) (5283923778161071103424114573796672324767/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2665
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2666
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (590880677129847672783450975019588460170143/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (590880677129847672783450975019588460170143/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (118735011783901591097516781367146366682181/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (118735011783901591097516781367146366682181/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (148069467006169453533879360231915036697631/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (148069467006169453533879360231915036697631/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2666 BracketBatch0166.bracket2667 (148069467006169453533879360231915036697631/2500000000000000000000000000000000000000) (2645408497171551877087192730168959945809/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2666 BracketBatch0166.bracket2667
  (148069467006169453533879360231915036697631/2500000000000000000000000000000000000000) (2645408497171551877087192730168959945809/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2666
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2667
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (296837529459753977743791953417865916705451/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (296837529459753977743791953417865916705451/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (596496054237881922248754758399395074490647/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (596496054237881922248754758399395074490647/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (1190171113157389877736338665235126907901549/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1190171113157389877736338665235126907901549/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2667 BracketBatch0166.bracket2668 (1190171113157389877736338665235126907901549/20000000000000000000000000000000000000000) (2648870768527718884548531651435585078429/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2667 BracketBatch0166.bracket2668
  (1190171113157389877736338665235126907901549/20000000000000000000000000000000000000000) (2648870768527718884548531651435585078429/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2667
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2668
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (149124013559470480562188689599848768622661/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (149124013559470480562188689599848768622661/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (59934404509728608848876429121842571811483/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (59934404509728608848876429121842571811483/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (597920049667584005368759524808910396302737/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (597920049667584005368759524808910396302737/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2668 BracketBatch0166.bracket2669 (597920049667584005368759524808910396302737/10000000000000000000000000000000000000000) (2652348826087705982554519548947236658521/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2668 BracketBatch0166.bracket2669
  (597920049667584005368759524808910396302737/10000000000000000000000000000000000000000) (2652348826087705982554519548947236658521/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2668
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2669
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (599344045097286088488764291218425718114827/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (599344045097286088488764291218425718114827/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (301109710428213844827043246364420480518337/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (301109710428213844827043246364420480518337/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (1201563465953713778142850783947266679151501/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1201563465953713778142850783947266679151501/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2669 BracketBatch0166.bracket2670 (1201563465953713778142850783947266679151501/20000000000000000000000000000000000000000) (5311685587866845935631004259657538486271/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2669 BracketBatch0166.bracket2670
  (1201563465953713778142850783947266679151501/20000000000000000000000000000000000000000) (5311685587866845935631004259657538486271/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2669
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2670
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (602219420856427689654086492728840961036671/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (602219420856427689654086492728840961036671/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (151280644599463433103725261447657199468981/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (151280644599463433103725261447657199468981/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (241468399850856284413797507703893951782519/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (241468399850856284413797507703893951782519/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2670 BracketBatch0166.bracket2671 (241468399850856284413797507703893951782519/4000000000000000000000000000000000000000) (5318705594588931767560297800203637800819/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2670 BracketBatch0166.bracket2671
  (241468399850856284413797507703893951782519/4000000000000000000000000000000000000000) (5318705594588931767560297800203637800819/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2670
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2671
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (605122578397853732414901045790628797875921/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (605122578397853732414901045790628797875921/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (60805392231056846483109516553071951834023/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (60805392231056846483109516553071951834023/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (1213176500708422197245996211321348316216151/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1213176500708422197245996211321348316216151/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0333.rows ScalarLogs0333.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2671 BracketBatch0167.bracket2672 (1213176500708422197245996211321348316216151/20000000000000000000000000000000000000000) (5325757925104175041142884930523083663523/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2671 BracketBatch0167.bracket2672
  (1213176500708422197245996211321348316216151/20000000000000000000000000000000000000000) (5325757925104175041142884930523083663523/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2671
