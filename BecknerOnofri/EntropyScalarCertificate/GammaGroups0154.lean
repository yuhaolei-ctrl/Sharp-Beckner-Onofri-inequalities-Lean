import BecknerOnofri.EntropyScalarCertificate.Bessel0192
import BecknerOnofri.EntropyScalarCertificate.Bessel0193
import BecknerOnofri.EntropyScalarCertificate.Bessel0585
import BecknerOnofri.EntropyScalarCertificate.Brackets0077
import BecknerOnofri.EntropyScalarCertificate.Logs0154
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1232
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (10515526972567115435640989395637082697209/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10515526972567115435640989395637082697209/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (5274398047820698575010954840277554425191/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5274398047820698575010954840277554425191/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (21064323068208512585662899076192191547591/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21064323068208512585662899076192191547591/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1232 BracketBatch0077.bracket1233 (21064323068208512585662899076192191547591/20000000000000000000000000000000000000000) (134995173123381166636495035166131464803/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1232 BracketBatch0077.bracket1233
  (21064323068208512585662899076192191547591/20000000000000000000000000000000000000000) (134995173123381166636495035166131464803/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1232
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1233
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (10548796095641397150021909680555108850379/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10548796095641397150021909680555108850379/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (5291125231502706889705429311567156623893/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5291125231502706889705429311567156623893/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (4226209311729362185886553660737884419633/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4226209311729362185886553660737884419633/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1233 BracketBatch0077.bracket1234 (4226209311729362185886553660737884419633/4000000000000000000000000000000000000000) (54369904897771553044774651208257848847/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1233 BracketBatch0077.bracket1234
  (4226209311729362185886553660737884419633/4000000000000000000000000000000000000000) (54369904897771553044774651208257848847/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1233
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1234
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (10582250463005413779410858623134313247783/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10582250463005413779410858623134313247783/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (10615892109179928450397740036388053198551/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10615892109179928450397740036388053198551/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (10599071286092671114904299329761183223167/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10599071286092671114904299329761183223167/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1234 BracketBatch0077.bracket1235 (10599071286092671114904299329761183223167/10000000000000000000000000000000000000000) (68430301815531767289212173274243596487/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1234 BracketBatch0077.bracket1235
  (10599071286092671114904299329761183223167/10000000000000000000000000000000000000000) (68430301815531767289212173274243596487/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1234
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1235
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (2653973027294982112599435009097013299637/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2653973027294982112599435009097013299637/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1331215387427419361767399830661475486001/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1331215387427419361767399830661475486001/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (5316403802149820836134234670419964271639/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5316403802149820836134234670419964271639/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1235 BracketBatch0077.bracket1236 (5316403802149820836134234670419964271639/5000000000000000000000000000000000000000) (11024219966624687686663523199714421499/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1235 BracketBatch0077.bracket1236
  (5316403802149820836134234670419964271639/5000000000000000000000000000000000000000) (11024219966624687686663523199714421499/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1235
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1236
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (2129944619883870978827839729058360777601/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2129944619883870978827839729058360777601/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (2136749106059418191481132637630397073563/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2136749106059418191481132637630397073563/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (1066673431485822292577243091672189462791/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1066673431485822292577243091672189462791/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1236 BracketBatch0077.bracket1237 (1066673431485822292577243091672189462791/1000000000000000000000000000000000000000) (138751253061801572014184668804614798119/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1236 BracketBatch0077.bracket1237
  (1066673431485822292577243091672189462791/1000000000000000000000000000000000000000) (138751253061801572014184668804614798119/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1236
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1237
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (2670936382574272739351415797037996341953/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2670936382574272739351415797037996341953/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (10717961530304122589271189615014486775137/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10717961530304122589271189615014486775137/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (21401707060601213546676852803166472142949/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21401707060601213546676852803166472142949/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1237 BracketBatch0077.bracket1238 (21401707060601213546676852803166472142949/20000000000000000000000000000000000000000) (279412335408513343238208379201578070843/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1237 BracketBatch0077.bracket1238
  (21401707060601213546676852803166472142949/20000000000000000000000000000000000000000) (279412335408513343238208379201578070843/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1237
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1238
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (5358980765152061294635594807507243387567/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5358980765152061294635594807507243387567/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (10752373260461243836348848277265063886199/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10752373260461243836348848277265063886199/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (21470334790765366425620037892279550661333/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21470334790765366425620037892279550661333/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1238 BracketBatch0077.bracket1239 (21470334790765366425620037892279550661333/20000000000000000000000000000000000000000) (17583443479020045627205155395457696641/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1238 BracketBatch0077.bracket1239
  (21470334790765366425620037892279550661333/20000000000000000000000000000000000000000) (17583443479020045627205155395457696641/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1238
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1239
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (2688093315115310959087212069316265971549/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2688093315115310959087212069316265971549/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (5393491457472624225699110129760379951543/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5393491457472624225699110129760379951543/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (10769678087703246143873534268392911894641/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10769678087703246143873534268392911894641/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0154.rows ScalarLogs0154.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1239 BracketBatch0077.bracket1240 (10769678087703246143873534268392911894641/10000000000000000000000000000000000000000) (70817724232602492388645694427783558663/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1239 BracketBatch0077.bracket1240
  (10769678087703246143873534268392911894641/10000000000000000000000000000000000000000) (70817724232602492388645694427783558663/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1239
