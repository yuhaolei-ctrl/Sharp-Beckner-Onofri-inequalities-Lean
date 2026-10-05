import BecknerOnofri.EntropyScalarCertificate.Bessel0133
import BecknerOnofri.EntropyScalarCertificate.Bessel0134
import BecknerOnofri.EntropyScalarCertificate.Bessel0135
import BecknerOnofri.EntropyScalarCertificate.Bessel0555
import BecknerOnofri.EntropyScalarCertificate.Bessel0556
import BecknerOnofri.EntropyScalarCertificate.Brackets0053
import BecknerOnofri.EntropyScalarCertificate.Brackets0054
import BecknerOnofri.EntropyScalarCertificate.Logs0107
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0856
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (3593707730543803494757963736015396932761/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3593707730543803494757963736015396932761/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (360574887164298220732042381142958993301/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (360574887164298220732042381142958993301/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (7199456602186785702078387547444986865771/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7199456602186785702078387547444986865771/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0856 BracketBatch0053.bracket0857 (7199456602186785702078387547444986865771/20000000000000000000000000000000000000000) (5324834849888325588395111614686880023/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0856 BracketBatch0053.bracket0857
  (7199456602186785702078387547444986865771/20000000000000000000000000000000000000000) (5324834849888325588395111614686880023/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0856
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0857
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (3605748871642982207320423811429589933007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3605748871642982207320423811429589933007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (904451088202428872969677962907486095997/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (904451088202428872969677962907486095997/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1444710644890539539839827132611906863399/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1444710644890539539839827132611906863399/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0857 BracketBatch0053.bracket0858 (1444710644890539539839827132611906863399/4000000000000000000000000000000000000000) (1077966600049022206628110218985087727/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0857 BracketBatch0053.bracket0858
  (1444710644890539539839827132611906863399/4000000000000000000000000000000000000000) (1077966600049022206628110218985087727/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0857
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0858
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (723560870561943098375742370325988876797/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (723560870561943098375742370325988876797/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (725974849573614450588675342444156298591/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (725974849573614450588675342444156298591/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (362383930033889387241104428192536293847/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (362383930033889387241104428192536293847/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0858 BracketBatch0053.bracket0859 (362383930033889387241104428192536293847/1000000000000000000000000000000000000000) (2727719955161684057261693300440922023/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0858 BracketBatch0053.bracket0859
  (362383930033889387241104428192536293847/1000000000000000000000000000000000000000) (2727719955161684057261693300440922023/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0858
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0859
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (453734280983509031617922089027597686619/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (453734280983509031617922089027597686619/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (455244828877523938870132650753831144709/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (455244828877523938870132650753831144709/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (28405597183157280327751710618169650979/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28405597183157280327751710618169650979/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0859 BracketBatch0053.bracket0860 (28405597183157280327751710618169650979/78125000000000000000000000000000000000) (5521659681441533976405953374665803151/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0859 BracketBatch0053.bracket0860
  (28405597183157280327751710618169650979/78125000000000000000000000000000000000) (5521659681441533976405953374665803151/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0859
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0860
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (3641958631020191510961061206030649157669/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3641958631020191510961061206030649157669/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (3654057576849264604770646991367454917737/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3654057576849264604770646991367454917737/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (3648008103934728057865854098699052037703/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3648008103934728057865854098699052037703/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0860 BracketBatch0053.bracket0861 (3648008103934728057865854098699052037703/10000000000000000000000000000000000000000) (2235398573605384650926380471711483723/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0860 BracketBatch0053.bracket0861
  (3648008103934728057865854098699052037703/10000000000000000000000000000000000000000) (2235398573605384650926380471711483723/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0860
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0861
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1827028788424632302385323495683727458867/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1827028788424632302385323495683727458867/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (183308558016127213318943384852287786717/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (183308558016127213318943384852287786717/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (3660114368585904435574757344206605326037/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3660114368585904435574757344206605326037/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0861 BracketBatch0053.bracket0862 (3660114368585904435574757344206605326037/10000000000000000000000000000000000000000) (11311908615265315183300037111657060351/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0861 BracketBatch0053.bracket0862
  (3660114368585904435574757344206605326037/10000000000000000000000000000000000000000) (11311908615265315183300037111657060351/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0861
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0862
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (3666171160322544266378867697045755734337/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3666171160322544266378867697045755734337/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (459787432099297608110462558498553711097/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (459787432099297608110462558498553711097/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (7344470617116925131262568165034185423113/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7344470617116925131262568165034185423113/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0862 BracketBatch0053.bracket0863 (7344470617116925131262568165034185423113/20000000000000000000000000000000000000000) (228961498446288066980832030952330783/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0862 BracketBatch0053.bracket0863
  (7344470617116925131262568165034185423113/20000000000000000000000000000000000000000) (228961498446288066980832030952330783/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0862
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0863
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (3678299456794380864883700467988429688773/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3678299456794380864883700467988429688773/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (3690442542009286120100529970638962164913/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3690442542009286120100529970638962164913/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (3684370999401833492492115219313695926843/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3684370999401833492492115219313695926843/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0107.rows ScalarLogs0107.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0863 BracketBatch0054.bracket0864 (3684370999401833492492115219313695926843/10000000000000000000000000000000000000000) (1448187518198838889694561967004333649/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0863 BracketBatch0054.bracket0864
  (3684370999401833492492115219313695926843/10000000000000000000000000000000000000000) (1448187518198838889694561967004333649/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0863
