import BecknerOnofri.EntropyScalarCertificate.Bessel0127
import BecknerOnofri.EntropyScalarCertificate.Bessel0128
import BecknerOnofri.EntropyScalarCertificate.Bessel0552
import BecknerOnofri.EntropyScalarCertificate.Bessel0553
import BecknerOnofri.EntropyScalarCertificate.Brackets0051
import BecknerOnofri.EntropyScalarCertificate.Logs0102
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0816
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (3123017064675549315888865855506718600561/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3123017064675549315888865855506718600561/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (626908227929569400394769874361115720853/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (626908227929569400394769874361115720853/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (3128779102161698158931357613656148602413/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3128779102161698158931357613656148602413/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0816 BracketBatch0051.bracket0817 (3128779102161698158931357613656148602413/10000000000000000000000000000000000000000) (6358557949995225277523458589192739081/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0816 BracketBatch0051.bracket0817
  (3128779102161698158931357613656148602413/10000000000000000000000000000000000000000) (6358557949995225277523458589192739081/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0816
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0817
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1567270569823923500986924685902789302131/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1567270569823923500986924685902789302131/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1573038440264225815689194796617559491873/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1573038440264225815689194796617559491873/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (785077252522037329169029870630087198501/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (785077252522037329169029870630087198501/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0817 BracketBatch0051.bracket0818 (785077252522037329169029870630087198501/2500000000000000000000000000000000000000) (1289232123112259706814501612491569179/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0817 BracketBatch0051.bracket0818
  (785077252522037329169029870630087198501/2500000000000000000000000000000000000000) (1289232123112259706814501612491569179/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0817
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0818
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (3146076880528451631378389593235118983743/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3146076880528451631378389593235118983743/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (315762434818851697778365628139328122487/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (315762434818851697778365628139328122487/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (6303701228716968609162045874628400208613/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6303701228716968609162045874628400208613/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0818 BracketBatch0051.bracket0819 (6303701228716968609162045874628400208613/20000000000000000000000000000000000000000) (3267341116252405437093661394872002611/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0818 BracketBatch0051.bracket0819
  (6303701228716968609162045874628400208613/20000000000000000000000000000000000000000) (3267341116252405437093661394872002611/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0818
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0819
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (3157624348188516977783656281393281224867/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3157624348188516977783656281393281224867/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (3169183603777014715567992758541404693113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3169183603777014715567992758541404693113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (316340397598276584667582451996734295899/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (316340397598276584667582451996734295899/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0819 BracketBatch0051.bracket0820 (316340397598276584667582451996734295899/1000000000000000000000000000000000000000) (66241295998104417633622934328263207/100000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0819 BracketBatch0051.bracket0820
  (316340397598276584667582451996734295899/1000000000000000000000000000000000000000) (66241295998104417633622934328263207/100000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0819
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0820
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (316918360377701471556799275854140469311/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (316918360377701471556799275854140469311/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (3180754708722848116014642363170165041739/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3180754708722848116014642363170165041739/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (6349938312499862831582635121711569734849/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6349938312499862831582635121711569734849/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0820 BracketBatch0051.bracket0821 (6349938312499862831582635121711569734849/20000000000000000000000000000000000000000) (1342901909779520160164216001982094229/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0820 BracketBatch0051.bracket0821
  (6349938312499862831582635121711569734849/20000000000000000000000000000000000000000) (1342901909779520160164216001982094229/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0820
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0821
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (397594338590356014501830295396270630217/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (397594338590356014501830295396270630217/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (3192337724736983276766647302521137756069/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3192337724736983276766647302521137756069/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (1274618486691966278556257933138260559561/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1274618486691966278556257933138260559561/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0821 BracketBatch0051.bracket0822 (1274618486691966278556257933138260559561/4000000000000000000000000000000000000000) (1361165788748734885968057297670116789/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0821 BracketBatch0051.bracket0822
  (1274618486691966278556257933138260559561/4000000000000000000000000000000000000000) (1361165788748734885968057297670116789/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0821
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0822
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (1596168862368491638383323651260568878033/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1596168862368491638383323651260568878033/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (3203932713814598067861542216262091083449/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3203932713814598067861542216262091083449/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (1279254087710316268925637903756645767903/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1279254087710316268925637903756645767903/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0822 BracketBatch0051.bracket0823 (1279254087710316268925637903756645767903/4000000000000000000000000000000000000000) (3449047340504107145684547202641562167/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0822 BracketBatch0051.bracket0823
  (1279254087710316268925637903756645767903/4000000000000000000000000000000000000000) (3449047340504107145684547202641562167/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0822
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0823
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1601966356907299033930771108131045541723/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1601966356907299033930771108131045541723/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (12862158952948995919303782823594841697/40000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12862158952948995919303782823594841697/40000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (401217028253240440480467995135050094231/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (401217028253240440480467995135050094231/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0102.rows ScalarLogs0102.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0823 BracketBatch0051.bracket0824 (401217028253240440480467995135050094231/1250000000000000000000000000000000000000) (6991313690158075509532521201162742703/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0823 BracketBatch0051.bracket0824
  (401217028253240440480467995135050094231/1250000000000000000000000000000000000000) (6991313690158075509532521201162742703/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0823
