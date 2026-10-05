import BecknerOnofri.EntropyScalarCertificate.Bessel0367
import BecknerOnofri.EntropyScalarCertificate.Bessel0368
import BecknerOnofri.EntropyScalarCertificate.Bessel0672
import BecknerOnofri.EntropyScalarCertificate.Bessel0673
import BecknerOnofri.EntropyScalarCertificate.Brackets0147
import BecknerOnofri.EntropyScalarCertificate.Logs0294
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2352
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (199687104632925477697949088137176074987157/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (199687104632925477697949088137176074987157/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (10063710303009034856885779885356362930029/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10063710303009034856885779885356362930029/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (400961310693106174835664685844303333587737/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (400961310693106174835664685844303333587737/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2352 BracketBatch0147.bracket2353 (400961310693106174835664685844303333587737/20000000000000000000000000000000000000000) (3687235322797170533228165899042329709239/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2352 BracketBatch0147.bracket2353
  (400961310693106174835664685844303333587737/20000000000000000000000000000000000000000) (3687235322797170533228165899042329709239/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2352
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2353
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (201274206060180697137715597707127258600577/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (201274206060180697137715597707127258600577/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (202886909234538667328815636649722706896113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (202886909234538667328815636649722706896113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (40416111529471936446653123435684996549669/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40416111529471936446653123435684996549669/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2353 BracketBatch0147.bracket2354 (40416111529471936446653123435684996549669/2000000000000000000000000000000000000000) (1848841403896176193069667540382277451673/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2353 BracketBatch0147.bracket2354
  (40416111529471936446653123435684996549669/2000000000000000000000000000000000000000) (1848841403896176193069667540382277451673/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2353
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2354
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (20288690923453866732881563664972270689611/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20288690923453866732881563664972270689611/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (204525838586071285459007486661506902748603/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (204525838586071285459007486661506902748603/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (407412747820609952787823123311229609644713/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (407412747820609952787823123311229609644713/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2354 BracketBatch0147.bracket2355 (407412747820609952787823123311229609644713/20000000000000000000000000000000000000000) (463528073984870120725595649217322933581/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2354 BracketBatch0147.bracket2355
  (407412747820609952787823123311229609644713/20000000000000000000000000000000000000000) (463528073984870120725595649217322933581/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2354
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2355
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1022629192930356427295037433307534513743/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1022629192930356427295037433307534513743/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (824766556071889256659097213966863329267/40000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (824766556071889256659097213966863329267/40000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (8214349552080871992475635803064454701307/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8214349552080871992475635803064454701307/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2355 BracketBatch0147.bracket2356 (8214349552080871992475635803064454701307/400000000000000000000000000000000000000) (743789838584588288834787693552964741399/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2355 BracketBatch0147.bracket2356
  (8214349552080871992475635803064454701307/400000000000000000000000000000000000000) (743789838584588288834787693552964741399/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2355
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2356
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (206191639017972314164774303491715832316747/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (206191639017972314164774303491715832316747/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (207884976752554138883995284605787875176093/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (207884976752554138883995284605787875176093/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (10351915394263161326219239702437592687321/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10351915394263161326219239702437592687321/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2356 BracketBatch0147.bracket2357 (10351915394263161326219239702437592687321/500000000000000000000000000000000000000) (932438797605576424709540979924676928549/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2356 BracketBatch0147.bracket2357
  (10351915394263161326219239702437592687321/500000000000000000000000000000000000000) (932438797605576424709540979924676928549/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2356
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2357
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (20788497675255413888399528460578787517609/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20788497675255413888399528460578787517609/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (209606540219544363138721519782766282047407/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (209606540219544363138721519782766282047407/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (417491516972098502022716804388554157223497/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (417491516972098502022716804388554157223497/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2357 BracketBatch0147.bracket2358 (417491516972098502022716804388554157223497/20000000000000000000000000000000000000000) (3740643551554378149770543780632280572891/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2357 BracketBatch0147.bracket2358
  (417491516972098502022716804388554157223497/20000000000000000000000000000000000000000) (3740643551554378149770543780632280572891/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2357
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2358
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (52401635054886090784680379945691570511851/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (52401635054886090784680379945691570511851/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (42271408197834093501650897035692023542347/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (42271408197834093501650897035692023542347/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (420963581208714830646976004961226399759139/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (420963581208714830646976004961226399759139/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2358 BracketBatch0147.bracket2359 (420963581208714830646976004961226399759139/20000000000000000000000000000000000000000) (937903812892880497213597323150847660063/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2358 BracketBatch0147.bracket2359
  (420963581208714830646976004961226399759139/20000000000000000000000000000000000000000) (937903812892880497213597323150847660063/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2358
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2359
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (52839260247292616877063621294615029427933/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (52839260247292616877063621294615029427933/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (21313721475268945132460636437347624089301/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21313721475268945132460636437347624089301/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (212247127870929959416430424775968179302371/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (212247127870929959416430424775968179302371/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0294.rows ScalarLogs0294.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2359 BracketBatch0147.bracket2360 (212247127870929959416430424775968179302371/10000000000000000000000000000000000000000) (3762671273278992130950849894630543578983/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2359 BracketBatch0147.bracket2360
  (212247127870929959416430424775968179302371/10000000000000000000000000000000000000000) (3762671273278992130950849894630543578983/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2359
