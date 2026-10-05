import BecknerOnofri.EntropyScalarCertificate.Bessel0445
import BecknerOnofri.EntropyScalarCertificate.Bessel0446
import BecknerOnofri.EntropyScalarCertificate.Bessel0711
import BecknerOnofri.EntropyScalarCertificate.Bessel0712
import BecknerOnofri.EntropyScalarCertificate.Brackets0178
import BecknerOnofri.EntropyScalarCertificate.Logs0356
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2848
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (65182574619331699412611705400023226232603/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (65182574619331699412611705400023226232603/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1045095853870648542430975747869437423120773/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1045095853870648542430975747869437423120773/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (2088017047779955733032763034269809042842421/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2088017047779955733032763034269809042842421/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2848 BracketBatch0178.bracket2849 (2088017047779955733032763034269809042842421/20000000000000000000000000000000000000000) (772273446159001757447776712672814822923/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2848 BracketBatch0178.bracket2849
  (2088017047779955733032763034269809042842421/20000000000000000000000000000000000000000) (772273446159001757447776712672814822923/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2848
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2849
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (104509585387064854243097574786943742312077/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (104509585387064854243097574786943742312077/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (523639806433793659259713603823972424624903/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (523639806433793659259713603823972424624903/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (130773466671139741309400184719836392023161/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (130773466671139741309400184719836392023161/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2849 BracketBatch0178.bracket2850 (130773466671139741309400184719836392023161/1250000000000000000000000000000000000000) (3090697448609683284124565090123440529933/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2849 BracketBatch0178.bracket2850
  (130773466671139741309400184719836392023161/1250000000000000000000000000000000000000) (3090697448609683284124565090123440529933/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2849
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2850
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1047279612867587318519427207647944849249803/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1047279612867587318519427207647944849249803/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1049472528126760968540526966913607132884243/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1049472528126760968540526966913607132884243/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1048376070497174143529977087280775991067023/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1048376070497174143529977087280775991067023/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2850 BracketBatch0178.bracket2851 (1048376070497174143529977087280775991067023/10000000000000000000000000000000000000000) (3092304492801974232088587175669645870139/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2850 BracketBatch0178.bracket2851
  (1048376070497174143529977087280775991067023/10000000000000000000000000000000000000000) (3092304492801974232088587175669645870139/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2850
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2851
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (13118406601584512106756587086420089161053/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13118406601584512106756587086420089161053/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (210334931471140611061234328112221132751591/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (210334931471140611061234328112221132751591/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (420229437096492804769339721494942559328439/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (420229437096492804769339721494942559328439/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2851 BracketBatch0178.bracket2852 (420229437096492804769339721494942559328439/4000000000000000000000000000000000000000) (3093914930749424353994305934592653234673/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2851 BracketBatch0178.bracket2852
  (420229437096492804769339721494942559328439/4000000000000000000000000000000000000000) (3093914930749424353994305934592653234673/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2851
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2852
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (8216208260591430119579465941883637998109/78125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8216208260591430119579465941883637998109/78125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (13173575734348816488944760368532770311069/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13173575734348816488944760368532770311069/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (131597544756475523401359529377732955540217/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (131597544756475523401359529377732955540217/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2852 BracketBatch0178.bracket2853 (131597544756475523401359529377732955540217/1250000000000000000000000000000000000000) (6191057552133880851299841915300021393263/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2852 BracketBatch0178.bracket2853
  (131597544756475523401359529377732955540217/1250000000000000000000000000000000000000) (6191057552133880851299841915300021393263/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2852
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2853
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1053886058747905319115580829482621624885517/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1053886058747905319115580829482621624885517/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (337954173116142022037765697330538834727/3200000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (337954173116142022037765697330538834727/3200000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (65937276554245285561987457301267358856481/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (65937276554245285561987457301267358856481/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2853 BracketBatch0178.bracket2854 (65937276554245285561987457301267358856481/625000000000000000000000000000000000000) (6194292084896729225043419896753562909791/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2853 BracketBatch0178.bracket2854
  (65937276554245285561987457301267358856481/625000000000000000000000000000000000000) (6194292084896729225043419896753562909791/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2853
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2854
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (66006674436746488679251112759870866157617/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (66006674436746488679251112759870866157617/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1058336913256670098221337514731291856316293/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1058336913256670098221337514731291856316293/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (422888740848922783417871063777845142967633/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (422888740848922783417871063777845142967633/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2854 BracketBatch0178.bracket2855 (422888740848922783417871063777845142967633/4000000000000000000000000000000000000000) (619753348733410469482746426193129331589/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2854 BracketBatch0178.bracket2855
  (422888740848922783417871063777845142967633/4000000000000000000000000000000000000000) (619753348733410469482746426193129331589/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2854
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2855
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (105833691325667009822133751473129185631629/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (105833691325667009822133751473129185631629/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1060576485236468341150855129450191818001349/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1060576485236468341150855129450191818001349/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (2118913398493138439372192644181483674317639/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2118913398493138439372192644181483674317639/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0356.rows ScalarLogs0356.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2855 BracketBatch0178.bracket2856 (2118913398493138439372192644181483674317639/20000000000000000000000000000000000000000) (1550195446788227515651483333083382387239/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2855 BracketBatch0178.bracket2856
  (2118913398493138439372192644181483674317639/20000000000000000000000000000000000000000) (1550195446788227515651483333083382387239/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2855
