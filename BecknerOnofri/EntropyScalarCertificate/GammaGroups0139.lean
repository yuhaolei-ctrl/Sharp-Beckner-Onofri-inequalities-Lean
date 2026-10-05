import BecknerOnofri.EntropyScalarCertificate.Bessel0173
import BecknerOnofri.EntropyScalarCertificate.Bessel0174
import BecknerOnofri.EntropyScalarCertificate.Bessel0175
import BecknerOnofri.EntropyScalarCertificate.Bessel0575
import BecknerOnofri.EntropyScalarCertificate.Bessel0576
import BecknerOnofri.EntropyScalarCertificate.Brackets0069
import BecknerOnofri.EntropyScalarCertificate.Brackets0070
import BecknerOnofri.EntropyScalarCertificate.Logs0139
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1112
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (7456998271887894846834258890012170579963/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7456998271887894846834258890012170579963/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (7477120021947600115399727364186083539821/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7477120021947600115399727364186083539821/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1866764786729436870279248281774781764973/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1866764786729436870279248281774781764973/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1112 BracketBatch0069.bracket1113 (1866764786729436870279248281774781764973/2500000000000000000000000000000000000000) (57619934249063729794404678333603504269/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1112 BracketBatch0069.bracket1113
  (1866764786729436870279248281774781764973/2500000000000000000000000000000000000000) (57619934249063729794404678333603504269/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1112
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1113
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (3738560010973800057699863682093041769909/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3738560010973800057699863682093041769909/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (7497305644042519091847806734844891092689/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7497305644042519091847806734844891092689/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (14974425665990119207247534099030974632507/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14974425665990119207247534099030974632507/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1113 BracketBatch0069.bracket1114 (14974425665990119207247534099030974632507/20000000000000000000000000000000000000000) (116103841371753811463591940597443539003/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1113 BracketBatch0069.bracket1114
  (14974425665990119207247534099030974632507/20000000000000000000000000000000000000000) (116103841371753811463591940597443539003/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1113
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1114
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (3748652822021259545923903367422445546343/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3748652822021259545923903367422445546343/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (469847225533681691553440473109508884677/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (469847225533681691553440473109508884677/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (7507430626290713078351427152298516623759/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7507430626290713078351427152298516623759/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1114 BracketBatch0069.bracket1115 (7507430626290713078351427152298516623759/10000000000000000000000000000000000000000) (116973298221129766223451361214922222243/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1114 BracketBatch0069.bracket1115
  (7507430626290713078351427152298516623759/10000000000000000000000000000000000000000) (116973298221129766223451361214922222243/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1114
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1115
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (7517555608538907064855047569752142154829/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7517555608538907064855047569752142154829/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1507574078106945501001494323696271045683/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1507574078106945501001494323696271045683/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (3763856499768408642465629797058374345811/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3763856499768408642465629797058374345811/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1115 BracketBatch0069.bracket1116 (3763856499768408642465629797058374345811/5000000000000000000000000000000000000000) (58924135813131018815368455355985385113/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1115 BracketBatch0069.bracket1116
  (3763856499768408642465629797058374345811/5000000000000000000000000000000000000000) (58924135813131018815368455355985385113/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1115
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1116
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1884467597633681876251867904620338807103/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1884467597633681876251867904620338807103/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (7558250469921494914509507488937753591043/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7558250469921494914509507488937753591043/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (3019224172091244483903395821483821763891/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3019224172091244483903395821483821763891/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1116 BracketBatch0069.bracket1117 (3019224172091244483903395821483821763891/4000000000000000000000000000000000000000) (118728794407078332754800829764151745703/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1116 BracketBatch0069.bracket1117
  (3019224172091244483903395821483821763891/4000000000000000000000000000000000000000) (118728794407078332754800829764151745703/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1116
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1117
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (5904883179626167901960552725732619993/7812500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5904883179626167901960552725732619993/7812500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (378934816572354884929556280237844514397/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (378934816572354884929556280237844514397/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (756847340068429630655031654684732193949/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (756847340068429630655031654684732193949/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1117 BracketBatch0069.bracket1118 (756847340068429630655031654684732193949/1000000000000000000000000000000000000000) (59807449813058215265770981737196501253/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1117 BracketBatch0069.bracket1118
  (756847340068429630655031654684732193949/1000000000000000000000000000000000000000) (59807449813058215265770981737196501253/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1117
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1118
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (7578696331447097698591125604756890287937/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7578696331447097698591125604756890287937/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (474950529048726203141547099397489845021/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (474950529048726203141547099397489845021/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (15177904796226716948855879195116727808273/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15177904796226716948855879195116727808273/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1118 BracketBatch0069.bracket1119 (15177904796226716948855879195116727808273/20000000000000000000000000000000000000000) (120506620591253437412117718212281148327/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1118 BracketBatch0069.bracket1119
  (15177904796226716948855879195116727808273/20000000000000000000000000000000000000000) (120506620591253437412117718212281148327/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1118
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1119
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (7599208464779619250264753590359837520333/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7599208464779619250264753590359837520333/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (3809893682286087912687715519868362970483/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3809893682286087912687715519868362970483/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (15218995829351795075640184630096563461299/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15218995829351795075640184630096563461299/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0139.rows ScalarLogs0139.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1119 BracketBatch0070.bracket1120 (15218995829351795075640184630096563461299/20000000000000000000000000000000000000000) (6070199542923796284477775933781265799/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1119 BracketBatch0070.bracket1120
  (15218995829351795075640184630096563461299/20000000000000000000000000000000000000000) (6070199542923796284477775933781265799/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1119
