import BecknerOnofri.EntropyScalarCertificate.Bessel0432
import BecknerOnofri.EntropyScalarCertificate.Bessel0433
import BecknerOnofri.EntropyScalarCertificate.Bessel0705
import BecknerOnofri.EntropyScalarCertificate.Brackets0173
import BecknerOnofri.EntropyScalarCertificate.Logs0346
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2768
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (447056214996611354688645109363919364006017/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (447056214996611354688645109363919364006017/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (111963707556793578452230152995461623993899/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (111963707556793578452230152995461623993899/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (894911045223785668497565721345765859981613/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (894911045223785668497565721345765859981613/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2768 BracketBatch0173.bracket2769 (894911045223785668497565721345765859981613/10000000000000000000000000000000000000000) (5941363954957061279394363768022058246669/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2768 BracketBatch0173.bracket2769
  (894911045223785668497565721345765859981613/10000000000000000000000000000000000000000) (5941363954957061279394363768022058246669/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2768
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2769
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (895709660454348627617841223963692991951189/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (895709660454348627617841223963692991951189/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (897312615790158452325521933984210178898667/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (897312615790158452325521933984210178898667/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (28015973066320423124115049342935987044529/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28015973066320423124115049342935987044529/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2769 BracketBatch0173.bracket2770 (28015973066320423124115049342935987044529/312500000000000000000000000000000000000) (5944106128405032989825716833579361511133/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2769 BracketBatch0173.bracket2770
  (28015973066320423124115049342935987044529/312500000000000000000000000000000000000) (5944106128405032989825716833579361511133/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2769
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2770
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (112164076973769806540690241748026272362333/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (112164076973769806540690241748026272362333/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (179784265366961071708670796880446996252537/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (179784265366961071708670796880446996252537/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (1796233942624963810868875918386445160161349/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1796233942624963810868875918386445160161349/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2770 BracketBatch0173.bracket2771 (1796233942624963810868875918386445160161349/20000000000000000000000000000000000000000) (743356664756921339250601156734730174843/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2770 BracketBatch0173.bracket2771
  (1796233942624963810868875918386445160161349/20000000000000000000000000000000000000000) (743356664756921339250601156734730174843/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2770
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2771
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (449460663417402679271676992201117490631341/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (449460663417402679271676992201117490631341/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (900535824644270961522947572169800161458029/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (900535824644270961522947572169800161458029/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1799457151479076320066301556572035142720711/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1799457151479076320066301556572035142720711/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2771 BracketBatch0173.bracket2772 (1799457151479076320066301556572035142720711/20000000000000000000000000000000000000000) (5949605541441173103173348785389848997041/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2771 BracketBatch0173.bracket2772
  (1799457151479076320066301556572035142720711/20000000000000000000000000000000000000000) (5949605541441173103173348785389848997041/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2771
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2772
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (450267912322135480761473786084900080729013/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (450267912322135480761473786084900080729013/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (225539035124590942785195554557511160811623/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (225539035124590942785195554557511160811623/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (901345982571317366331864895199922402352259/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (901345982571317366331864895199922402352259/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2772 BracketBatch0173.bracket2773 (901345982571317366331864895199922402352259/10000000000000000000000000000000000000000) (1488090704046348279476591629659216261909/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2772 BracketBatch0173.bracket2773
  (901345982571317366331864895199922402352259/10000000000000000000000000000000000000000) (1488090704046348279476591629659216261909/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2772
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2773
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (902156140498363771140782218230044643246489/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (902156140498363771140782218230044643246489/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (45189115295136964511256658632204469514871/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (45189115295136964511256658632204469514871/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (1805938446401103061365915390874134033543909/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1805938446401103061365915390874134033543909/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2773 BracketBatch0173.bracket2774 (1805938446401103061365915390874134033543909/20000000000000000000000000000000000000000) (5955125160001434404306176308102631360011/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2773 BracketBatch0173.bracket2774
  (1805938446401103061365915390874134033543909/20000000000000000000000000000000000000000) (5955125160001434404306176308102631360011/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2773
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2774
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (903782305902739290225133172644089390297417/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (903782305902739290225133172644089390297417/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (181082870518188406153439187735850101250509/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (181082870518188406153439187735850101250509/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (904598329246840660496164555661669948274981/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (904598329246840660496164555661669948274981/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2774 BracketBatch0173.bracket2775 (904598329246840660496164555661669948274981/10000000000000000000000000000000000000000) (595789259069375241466182999256944713347/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2774 BracketBatch0173.bracket2775
  (904598329246840660496164555661669948274981/10000000000000000000000000000000000000000) (595789259069375241466182999256944713347/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2774
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2775
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (452707176295471015383597969339625253126271/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (452707176295471015383597969339625253126271/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (28345384766452178936268518364261438061359/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28345384766452178936268518364261438061359/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (181246666511741175672778852633561652421603/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (181246666511741175672778852633561652421603/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0346.rows ScalarLogs0346.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2775 BracketBatch0173.bracket2776 (181246666511741175672778852633561652421603/2000000000000000000000000000000000000000) (5960665126158460314956697750291078605613/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2775 BracketBatch0173.bracket2776
  (181246666511741175672778852633561652421603/2000000000000000000000000000000000000000) (5960665126158460314956697750291078605613/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2775
