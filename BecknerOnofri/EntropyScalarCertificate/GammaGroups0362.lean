import BecknerOnofri.EntropyScalarCertificate.Bessel0452
import BecknerOnofri.EntropyScalarCertificate.Bessel0453
import BecknerOnofri.EntropyScalarCertificate.Bessel0715
import BecknerOnofri.EntropyScalarCertificate.Brackets0181
import BecknerOnofri.EntropyScalarCertificate.Logs0362
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2896
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1158661479454079540895280836732930187686347/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1158661479454079540895280836732930187686347/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (145168358749238105055830586889176812650247/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (145168358749238105055830586889176812650247/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (2320008349447984381341925531846344688888323/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2320008349447984381341925531846344688888323/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2896 BracketBatch0181.bracket2897 (2320008349447984381341925531846344688888323/20000000000000000000000000000000000000000) (6340265256853853279109518427695501108781/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2896 BracketBatch0181.bracket2897
  (2320008349447984381341925531846344688888323/20000000000000000000000000000000000000000) (6340265256853853279109518427695501108781/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2896
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2897
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1161346869993904840446644695113414501201973/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1161346869993904840446644695113414501201973/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (582022375383304160123574303311055876980269/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (582022375383304160123574303311055876980269/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (2325391620760513160693793301735526255162511/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2325391620760513160693793301735526255162511/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2897 BracketBatch0181.bracket2898 (2325391620760513160693793301735526255162511/20000000000000000000000000000000000000000) (6343830526959516447291956114131979094757/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2897 BracketBatch0181.bracket2898
  (2325391620760513160693793301735526255162511/20000000000000000000000000000000000000000) (6343830526959516447291956114131979094757/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2897
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2898
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (232808950153321664049429721324422350792107/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (232808950153321664049429721324422350792107/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (583377604558237074537328711832767484985117/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (583377604558237074537328711832767484985117/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (2330799959883082469321806030287646723930769/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2330799959883082469321806030287646723930769/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2898 BracketBatch0181.bracket2899 (2330799959883082469321806030287646723930769/20000000000000000000000000000000000000000) (6347404054955790455677604933791278785637/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2898 BracketBatch0181.bracket2899
  (2330799959883082469321806030287646723930769/20000000000000000000000000000000000000000) (6347404054955790455677604933791278785637/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2898
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2899
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1166755209116474149074657423665534969970231/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1166755209116474149074657423665534969970231/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (292369583301022054259711223477231215747241/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (292369583301022054259711223477231215747241/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (467246708464112473222700463514891966591839/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (467246708464112473222700463514891966591839/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2899 BracketBatch0181.bracket2900 (467246708464112473222700463514891966591839/4000000000000000000000000000000000000000) (3175492938451594574525349544264397224017/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2899 BracketBatch0181.bracket2900
  (467246708464112473222700463514891966591839/4000000000000000000000000000000000000000) (3175492938451594574525349544264397224017/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2899
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2900
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1169478333204088217038844893908924862988961/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1169478333204088217038844893908924862988961/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1172214212015896703746655242360283395191663/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1172214212015896703746655242360283395191663/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (146355784076249057549093758516825516136289/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (146355784076249057549093758516825516136289/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2900 BracketBatch0181.bracket2901 (146355784076249057549093758516825516136289/1250000000000000000000000000000000000000) (1588644007271505320111584961764576034157/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2900 BracketBatch0181.bracket2901
  (146355784076249057549093758516825516136289/1250000000000000000000000000000000000000) (1588644007271505320111584961764576034157/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2900
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2901
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (58610710600794835187332762118014169759583/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (58610710600794835187332762118014169759583/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1174962935373899274188405060503763451010003/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1174962935373899274188405060503763451010003/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (2347177147389795977935060302864046846201663/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2347177147389795977935060302864046846201663/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2901 BracketBatch0181.bracket2902 (2347177147389795977935060302864046846201663/20000000000000000000000000000000000000000) (1589543637003521430445250102794645916199/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2901 BracketBatch0181.bracket2902
  (2347177147389795977935060302864046846201663/20000000000000000000000000000000000000000) (1589543637003521430445250102794645916199/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2901
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2902
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (117496293537389927418840506050376345101/1000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (117496293537389927418840506050376345101/1000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (294431148486369779935569306296488367897259/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (294431148486369779935569306296488367897259/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (588171882329844598482670571422429230649759/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (588171882329844598482670571422429230649759/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2902 BracketBatch0181.bracket2903 (588171882329844598482670571422429230649759/5000000000000000000000000000000000000000) (6361781470424380077907910953880980591283/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2902 BracketBatch0181.bracket2903
  (588171882329844598482670571422429230649759/5000000000000000000000000000000000000000) (6361781470424380077907910953880980591283/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2902
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2903
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1177724593945479119742277225185953471589033/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1177724593945479119742277225185953471589033/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1180499279253372103532651998688851620955893/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1180499279253372103532651998688851620955893/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1179111936599425611637464611937402546272463/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1179111936599425611637464611937402546272463/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0362.rows ScalarLogs0362.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2903 BracketBatch0181.bracket2904 (1179111936599425611637464611937402546272463/10000000000000000000000000000000000000000) (6365396833282822772645386874366663417419/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2903 BracketBatch0181.bracket2904
  (1179111936599425611637464611937402546272463/10000000000000000000000000000000000000000) (6365396833282822772645386874366663417419/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2903
