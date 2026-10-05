import BecknerOnofri.EntropyScalarCertificate.Bessel0482
import BecknerOnofri.EntropyScalarCertificate.Bessel0483
import BecknerOnofri.EntropyScalarCertificate.Bessel0730
import BecknerOnofri.EntropyScalarCertificate.Brackets0193
import BecknerOnofri.EntropyScalarCertificate.Logs0386
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3088
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (416917118022696406630510924789641365680197/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (416917118022696406630510924789641365680197/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (2093302456553660776409577239553959165233411/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2093302456553660776409577239553959165233411/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1044472011666785702390532965875541498408599/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1044472011666785702390532965875541498408599/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3088 BracketBatch0193.bracket3089 (1044472011666785702390532965875541498408599/5000000000000000000000000000000000000000) (7234606156178809057955939167320047171669/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3088 BracketBatch0193.bracket3089
  (1044472011666785702390532965875541498408599/5000000000000000000000000000000000000000) (7234606156178809057955939167320047171669/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3088
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3089
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (8176962720912737407849911092007652989193/39062500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8176962720912737407849911092007652989193/39062500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (262761571756477789309456583022649891180419/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (262761571756477789309456583022649891180419/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (104884875765137077272130747593378957366919/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (104884875765137077272130747593378957366919/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3089 BracketBatch0193.bracket3090 (104884875765137077272130747593378957366919/500000000000000000000000000000000000000) (724079022177393122960868843991948460591/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3089 BracketBatch0193.bracket3090
  (104884875765137077272130747593378957366919/500000000000000000000000000000000000000) (724079022177393122960868843991948460591/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3089
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3090
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (2102092574051822314475652664181199129443349/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2102092574051822314475652664181199129443349/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (2110956869836545688130524351166507830581477/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2110956869836545688130524351166507830581477/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (2106524721944184001303088507673853480012413/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2106524721944184001303088507673853480012413/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3090 BracketBatch0193.bracket3091 (2106524721944184001303088507673853480012413/10000000000000000000000000000000000000000) (7246995775988877306733452394532211937017/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3090 BracketBatch0193.bracket3091
  (2106524721944184001303088507673853480012413/10000000000000000000000000000000000000000) (7246995775988877306733452394532211937017/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3090
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3091
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1055478434918272844065262175583253915290737/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1055478434918272844065262175583253915290737/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (2119896286852148566190847479184784863332063/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2119896286852148566190847479184784863332063/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (4230853156688694254321371830351292693913537/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4230853156688694254321371830351292693913537/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3091 BracketBatch0193.bracket3092 (4230853156688694254321371830351292693913537/20000000000000000000000000000000000000000) (3626611459205201941571195841092658313387/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3091 BracketBatch0193.bracket3092
  (4230853156688694254321371830351292693913537/20000000000000000000000000000000000000000) (3626611459205201941571195841092658313387/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3091
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3092
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (105994814342607428309542373959239243166603/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (105994814342607428309542373959239243166603/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1064455892046532331563983529724634933692659/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1064455892046532331563983529724634933692659/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (2124404035472606614659407269317027365358689/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2124404035472606614659407269317027365358689/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3092 BracketBatch0193.bracket3093 (2124404035472606614659407269317027365358689/10000000000000000000000000000000000000000) (453716984261585466166627798344018253639/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3092 BracketBatch0193.bracket3093
  (2124404035472606614659407269317027365358689/10000000000000000000000000000000000000000) (453716984261585466166627798344018253639/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3092
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3093
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (425782356818612932625593411889853973477063/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (425782356818612932625593411889853973477063/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (427600867389358987324922687120982057410203/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (427600867389358987324922687120982057410203/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (426691612103985959975258049505418015443633/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (426691612103985959975258049505418015443633/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3093 BracketBatch0193.bracket3094 (426691612103985959975258049505418015443633/2000000000000000000000000000000000000000) (7265742363970217257735246595946691172709/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3093 BracketBatch0193.bracket3094
  (426691612103985959975258049505418015443633/2000000000000000000000000000000000000000) (7265742363970217257735246595946691172709/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3093
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3094
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (534501084236698734156153358901227571762753/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (534501084236698734156153358901227571762753/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (2147174937545690146442070634463287720712841/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2147174937545690146442070634463287720712841/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (4285179274492485083066684070068198007763853/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4285179274492485083066684070068198007763853/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3094 BracketBatch0193.bracket3095 (4285179274492485083066684070068198007763853/20000000000000000000000000000000000000000) (3636017431939066273180596489146849883089/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3094 BracketBatch0193.bracket3095
  (4285179274492485083066684070068198007763853/20000000000000000000000000000000000000000) (3636017431939066273180596489146849883089/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3094
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3095
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1073587468772845073221035317231643860356419/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1073587468772845073221035317231643860356419/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1078212297563915619042816779383454622450817/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1078212297563915619042816779383454622450817/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (537949941584190173065963024153774620701809/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (537949941584190173065963024153774620701809/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0386.rows ScalarLogs0386.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3095 BracketBatch0193.bracket3096 (537949941584190173065963024153774620701809/2500000000000000000000000000000000000000) (1819587336355925049108007830724265416603/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3095 BracketBatch0193.bracket3096
  (537949941584190173065963024153774620701809/2500000000000000000000000000000000000000) (1819587336355925049108007830724265416603/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3095
