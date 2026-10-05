import BecknerOnofri.EntropyScalarCertificate.Bessel0306
import BecknerOnofri.EntropyScalarCertificate.Bessel0307
import BecknerOnofri.EntropyScalarCertificate.Bessel0642
import BecknerOnofri.EntropyScalarCertificate.Brackets0122
import BecknerOnofri.EntropyScalarCertificate.Brackets0123
import BecknerOnofri.EntropyScalarCertificate.Logs0245
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1960
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (21877577388683437434468193885824607628623/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21877577388683437434468193885824607628623/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (11028985431946505128297841913863026110187/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11028985431946505128297841913863026110187/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (43935548252576447691063877713550659848997/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43935548252576447691063877713550659848997/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1960 BracketBatch0122.bracket1961 (43935548252576447691063877713550659848997/10000000000000000000000000000000000000000) (423262144357278782974517812743879239591/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1960 BracketBatch0122.bracket1961
  (43935548252576447691063877713550659848997/10000000000000000000000000000000000000000) (423262144357278782974517812743879239591/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1960
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1961
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (8823188345557204102638273531090420888149/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8823188345557204102638273531090420888149/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (177931916897972568477482271820956591757/40000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (177931916897972568477482271820956591757/40000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (17719784190455832526512387122138250475999/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17719784190455832526512387122138250475999/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1961 BracketBatch0122.bracket1962 (17719784190455832526512387122138250475999/4000000000000000000000000000000000000000) (851493653452978783092605073167012533233/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1961 BracketBatch0122.bracket1962
  (17719784190455832526512387122138250475999/4000000000000000000000000000000000000000) (851493653452978783092605073167012533233/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1961
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1962
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (44482979224493142119370567955239147939247/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44482979224493142119370567955239147939247/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (44856430072258955354011997887478597496999/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44856430072258955354011997887478597496999/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (44669704648376048736691282921358872718123/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44669704648376048736691282921358872718123/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1962 BracketBatch0122.bracket1963 (44669704648376048736691282921358872718123/10000000000000000000000000000000000000000) (856509612799898843711683207096822170103/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1962 BracketBatch0122.bracket1963
  (44669704648376048736691282921358872718123/10000000000000000000000000000000000000000) (856509612799898843711683207096822170103/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1962
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1963
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (11214107518064738838502999471869649374249/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11214107518064738838502999471869649374249/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (22618231396246750296555318831688583681267/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22618231396246750296555318831688583681267/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (9009289286475245594712263555085576485953/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9009289286475245594712263555085576485953/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1963 BracketBatch0122.bracket1964 (9009289286475245594712263555085576485953/2000000000000000000000000000000000000000) (861572876755146082999392052151303500629/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1963 BracketBatch0122.bracket1964
  (9009289286475245594712263555085576485953/2000000000000000000000000000000000000000) (861572876755146082999392052151303500629/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1963
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1964
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (45236462792493500593110637663377167362531/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (45236462792493500593110637663377167362531/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (45623251876205357177487501626748268717417/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (45623251876205357177487501626748268717417/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (22714928667174714442649534822531359019987/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22714928667174714442649534822531359019987/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1964 BracketBatch0122.bracket1965 (22714928667174714442649534822531359019987/5000000000000000000000000000000000000000) (866684171182787487559087475770390619627/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1964 BracketBatch0122.bracket1965
  (22714928667174714442649534822531359019987/5000000000000000000000000000000000000000) (866684171182787487559087475770390619627/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1964
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1965
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (22811625938102678588743750813374134358707/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (22811625938102678588743750813374134358707/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (46016978050503122061099548017926353573707/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46016978050503122061099548017926353573707/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (91640229926708479238587049644674622291121/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (91640229926708479238587049644674622291121/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1965 BracketBatch0122.bracket1966 (91640229926708479238587049644674622291121/20000000000000000000000000000000000000000) (348737695284747556352832619893410314547/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1965 BracketBatch0122.bracket1966
  (91640229926708479238587049644674622291121/20000000000000000000000000000000000000000) (348737695284747556352832619893410314547/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1965
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1966
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (5752122256312890257637443502240794196713/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5752122256312890257637443502240794196713/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (46417828559493529384747736333652621016873/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46417828559493529384747736333652621016873/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (92434806609996651445847284351578974590577/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (92434806609996651445847284351578974590577/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1966 BracketBatch0122.bracket1967 (92434806609996651445847284351578974590577/20000000000000000000000000000000000000000) (438526918322111113753130765415422302929/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1966 BracketBatch0122.bracket1967
  (92434806609996651445847284351578974590577/20000000000000000000000000000000000000000) (438526918322111113753130765415422302929/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1966
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1967
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (4641782855949352938474773633365262101687/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4641782855949352938474773633365262101687/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (46825997460492750378686582580028243474571/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46825997460492750378686582580028243474571/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (93243826019986279763434318913680864491441/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (93243826019986279763434318913680864491441/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0245.rows ScalarLogs0245.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1967 BracketBatch0123.bracket1968 (93243826019986279763434318913680864491441/20000000000000000000000000000000000000000) (1764627484737912171743021254799809793847/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1967 BracketBatch0123.bracket1968
  (93243826019986279763434318913680864491441/20000000000000000000000000000000000000000) (1764627484737912171743021254799809793847/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1967
