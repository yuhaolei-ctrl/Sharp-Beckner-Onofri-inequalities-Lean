import BecknerOnofri.EntropyScalarCertificate.Bessel0336
import BecknerOnofri.EntropyScalarCertificate.Bessel0337
import BecknerOnofri.EntropyScalarCertificate.Bessel0657
import BecknerOnofri.EntropyScalarCertificate.Brackets0134
import BecknerOnofri.EntropyScalarCertificate.Brackets0135
import BecknerOnofri.EntropyScalarCertificate.Logs0269
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2152
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (39001973130853314778634309269543084309371/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39001973130853314778634309269543084309371/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (7823968149620016425066436264571175241201/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7823968149620016425066436264571175241201/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (4882613367434587306497905662024935032211/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4882613367434587306497905662024935032211/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2152 BracketBatch0134.bracket2153 (4882613367434587306497905662024935032211/625000000000000000000000000000000000000) (97519082852109836780855469156017549763/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2152 BracketBatch0134.bracket2153
  (4882613367434587306497905662024935032211/625000000000000000000000000000000000000) (97519082852109836780855469156017549763/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2152
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2153
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (78239681496200164250664362645711752412007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (78239681496200164250664362645711752412007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (7847687342018902859144954713908980853829/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7847687342018902859144954713908980853829/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (156716554916389192842113909784801560950297/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (156716554916389192842113909784801560950297/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2153 BracketBatch0134.bracket2154 (156716554916389192842113909784801560950297/20000000000000000000000000000000000000000) (2441903383659141889522073196920146087479/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2153 BracketBatch0134.bracket2154
  (156716554916389192842113909784801560950297/20000000000000000000000000000000000000000) (2441903383659141889522073196920146087479/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2153
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2154
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (78476873420189028591449547139089808538287/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (78476873420189028591449547139089808538287/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (15743107112345050234970346423705224892089/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15743107112345050234970346423705224892089/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (39298102245478569941575319814403983249683/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39298102245478569941575319814403983249683/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2154 BracketBatch0134.bracket2155 (39298102245478569941575319814403983249683/5000000000000000000000000000000000000000) (2445842939053757065482992727585939500529/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2154 BracketBatch0134.bracket2155
  (39298102245478569941575319814403983249683/5000000000000000000000000000000000000000) (2445842939053757065482992727585939500529/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2154
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2155
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (39357767780862625587425866059263062230221/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39357767780862625587425866059263062230221/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (19738920404228720015069675281376539573971/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19738920404228720015069675281376539573971/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (78835608589320065617565216622016141378163/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (78835608589320065617565216622016141378163/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2155 BracketBatch0134.bracket2156 (78835608589320065617565216622016141378163/10000000000000000000000000000000000000000) (612448955321548391768980403560987803591/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2155 BracketBatch0134.bracket2156
  (78835608589320065617565216622016141378163/10000000000000000000000000000000000000000) (612448955321548391768980403560987803591/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2155
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2156
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (78955681616914880060278701125506158295881/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (78955681616914880060278701125506158295881/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (79197325452535629560362946139940246828719/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (79197325452535629560362946139940246828719/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (790765035347252548103208236327232025623/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (790765035347252548103208236327232025623/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2156 BracketBatch0134.bracket2157 (790765035347252548103208236327232025623/100000000000000000000000000000000000000) (306720264367793433543874027682185374763/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2156 BracketBatch0134.bracket2157
  (790765035347252548103208236327232025623/100000000000000000000000000000000000000) (306720264367793433543874027682185374763/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2156
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2157
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (19799331363133907390090736534985061707179/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19799331363133907390090736534985061707179/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (79440481108703608051459388284907863347797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (79440481108703608051459388284907863347797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (158637806561239237611822334424848110176513/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (158637806561239237611822334424848110176513/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2157 BracketBatch0134.bracket2158 (158637806561239237611822334424848110176513/20000000000000000000000000000000000000000) (245774190540402789300776079049582362341/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2157 BracketBatch0134.bracket2158
  (158637806561239237611822334424848110176513/20000000000000000000000000000000000000000) (245774190540402789300776079049582362341/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2157
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2158
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (39720240554351804025729694142453931673897/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39720240554351804025729694142453931673897/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (79685162801590203816758984978225974531897/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (79685162801590203816758984978225974531897/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (159125643910293811868218373263133837879691/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (159125643910293811868218373263133837879691/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2158 BracketBatch0134.bracket2159 (159125643910293811868218373263133837879691/20000000000000000000000000000000000000000) (2461735278858720649261231124967223707161/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2158 BracketBatch0134.bracket2159
  (159125643910293811868218373263133837879691/20000000000000000000000000000000000000000) (2461735278858720649261231124967223707161/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2158
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2159
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (39842581400795101908379492489112987265947/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39842581400795101908379492489112987265947/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (9991423115773779128477810797914226724187/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9991423115773779128477810797914226724187/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (15961654772778043684458147136153978832539/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15961654772778043684458147136153978832539/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0269.rows ScalarLogs0269.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2159 BracketBatch0135.bracket2160 (15961654772778043684458147136153978832539/2000000000000000000000000000000000000000) (2465742322309498966360932371691314778179/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2159 BracketBatch0135.bracket2160
  (15961654772778043684458147136153978832539/2000000000000000000000000000000000000000) (2465742322309498966360932371691314778179/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2159
