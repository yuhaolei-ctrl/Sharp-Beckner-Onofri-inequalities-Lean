import BecknerOnofri.EntropyScalarCertificate.Bessel0331
import BecknerOnofri.EntropyScalarCertificate.Bessel0332
import BecknerOnofri.EntropyScalarCertificate.Bessel0654
import BecknerOnofri.EntropyScalarCertificate.Bessel0655
import BecknerOnofri.EntropyScalarCertificate.Brackets0132
import BecknerOnofri.EntropyScalarCertificate.Brackets0133
import BecknerOnofri.EntropyScalarCertificate.Logs0265
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2120
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (35578256707998482545620257587835172458893/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (35578256707998482545620257587835172458893/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (71351892523071618719156187654209946034969/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (71351892523071618719156187654209946034969/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (28501681187813716762079340565976058190551/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28501681187813716762079340565976058190551/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2120 BracketBatch0132.bracket2121 (28501681187813716762079340565976058190551/4000000000000000000000000000000000000000) (2318863793880236857006413399340579020993/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2120 BracketBatch0132.bracket2121
  (28501681187813716762079340565976058190551/4000000000000000000000000000000000000000) (2318863793880236857006413399340579020993/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2120
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2121
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (35675946261535809359578093827104973017483/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (35675946261535809359578093827104973017483/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (14309674141787206281034755154794898413511/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14309674141787206281034755154794898413511/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (142900263232007650124329963428184438102521/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (142900263232007650124329963428184438102521/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2121 BracketBatch0132.bracket2122 (142900263232007650124329963428184438102521/20000000000000000000000000000000000000000) (2322406324552186769838817103955756356503/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2121 BracketBatch0132.bracket2122
  (142900263232007650124329963428184438102521/20000000000000000000000000000000000000000) (2322406324552186769838817103955756356503/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2121
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2122
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (2235886584654250981411680492936702877111/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2235886584654250981411680492936702877111/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (8968244657504243730162089935235030318343/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8968244657504243730162089935235030318343/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (17911790996121247655808811906981841826787/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17911790996121247655808811906981841826787/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2122 BracketBatch0132.bracket2123 (17911790996121247655808811906981841826787/2500000000000000000000000000000000000000) (1162979890493661946738792430004235406977/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2122 BracketBatch0132.bracket2123
  (17911790996121247655808811906981841826787/2500000000000000000000000000000000000000) (1162979890493661946738792430004235406977/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2122
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2123
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (71745957260033949841296719481880242546741/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (71745957260033949841296719481880242546741/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (8993082695968076750474057743798832468303/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8993082695968076750474057743798832468303/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (28738123765555712769017836286454180458633/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28738123765555712769017836286454180458633/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2123 BracketBatch0132.bracket2124 (28738123765555712769017836286454180458633/4000000000000000000000000000000000000000) (116476211307739142072652842225822752613/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2123 BracketBatch0132.bracket2124
  (28738123765555712769017836286454180458633/4000000000000000000000000000000000000000) (116476211307739142072652842225822752613/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2123
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2124
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (71944661567744614003792461950390659746421/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (71944661567744614003792461950390659746421/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (72144493129869074910365486336516869718153/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (72144493129869074910365486336516869718153/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (72044577348806844457078974143453764732287/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (72044577348806844457078974143453764732287/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2124 BracketBatch0132.bracket2125 (72044577348806844457078974143453764732287/10000000000000000000000000000000000000000) (2333099723565501566636605711982966131781/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2124 BracketBatch0132.bracket2125
  (72044577348806844457078974143453764732287/10000000000000000000000000000000000000000) (2333099723565501566636605711982966131781/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2124
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2125
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1442889862597381498207309726730337394363/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1442889862597381498207309726730337394363/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (72345461552141847531122493156980937267567/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (72345461552141847531122493156980937267567/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (144489954682010922441487979493497806985717/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (144489954682010922441487979493497806985717/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2125 BracketBatch0132.bracket2126 (144489954682010922441487979493497806985717/20000000000000000000000000000000000000000) (467337267455661866598150288051290693123/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2125 BracketBatch0132.bracket2126
  (144489954682010922441487979493497806985717/20000000000000000000000000000000000000000) (467337267455661866598150288051290693123/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2125
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2126
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (18086365388035461882780623289245234316891/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18086365388035461882780623289245234316891/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2267111767180262628462271032273536052711/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2267111767180262628462271032273536052711/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (36223259525477562910478791547433522738579/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36223259525477562910478791547433522738579/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2126 BracketBatch0132.bracket2127 (36223259525477562910478791547433522738579/5000000000000000000000000000000000000000) (468056826381219781007716620877665532871/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2126 BracketBatch0132.bracket2127
  (36223259525477562910478791547433522738579/5000000000000000000000000000000000000000) (468056826381219781007716620877665532871/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2126
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2127
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (72547576549768404110792673032753153686749/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (72547576549768404110792673032753153686749/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (4546927996811814044275344379959979915009/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4546927996811814044275344379959979915009/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (145298424498757428819198183112112832326893/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (145298424498757428819198183112112832326893/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0265.rows ScalarLogs0265.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2127 BracketBatch0133.bracket2128 (145298424498757428819198183112112832326893/20000000000000000000000000000000000000000) (468778634524416867005494837231828151251/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2127 BracketBatch0133.bracket2128
  (145298424498757428819198183112112832326893/20000000000000000000000000000000000000000) (468778634524416867005494837231828151251/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2127
