module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0451
public import BecknerOnofri.EntropyScalarCertificate.Bessel0452
public import BecknerOnofri.EntropyScalarCertificate.Bessel0714
public import BecknerOnofri.EntropyScalarCertificate.Bessel0715
public import BecknerOnofri.EntropyScalarCertificate.Brackets0180
public import BecknerOnofri.EntropyScalarCertificate.Brackets0181
public import BecknerOnofri.EntropyScalarCertificate.Logs0361
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2888
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (56880889211892196381639907640712495728297/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (56880889211892196381639907640712495728297/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (285051575601009151485061223004910673279793/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (285051575601009151485061223004910673279793/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (284728010830235066696630380604236575960639/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (284728010830235066696630380604236575960639/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2888 BracketBatch0180.bracket2889 (284728010830235066696630380604236575960639/2500000000000000000000000000000000000000) (1262407225068269323950656581297539445203/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2888 BracketBatch0180.bracket2889
  (284728010830235066696630380604236575960639/2500000000000000000000000000000000000000) (1262407225068269323950656581297539445203/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2888
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2889
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1140206302404036605940244892019642693119169/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1140206302404036605940244892019642693119169/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (571403320165703869660743988825706292259497/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (571403320165703869660743988825706292259497/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (2283012942735444345261732869671055277638163/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2283012942735444345261732869671055277638163/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2889 BracketBatch0180.bracket2890 (2283012942735444345261732869671055277638163/20000000000000000000000000000000000000000) (6315536604194158412790929994314063563223/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2889 BracketBatch0180.bracket2890
  (2283012942735444345261732869671055277638163/20000000000000000000000000000000000000000) (6315536604194158412790929994314063563223/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2889
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2890
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1142806640331407739321487977651412584518991/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1142806640331407739321487977651412584518991/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1145418879162480917686609079611718826765883/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1145418879162480917686609079611718826765883/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (1144112759746944328504048528631565705642437/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1144112759746944328504048528631565705642437/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2890 BracketBatch0180.bracket2891 (1144112759746944328504048528631565705642437/10000000000000000000000000000000000000000) (1263809012062205683069407688467632047519/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2890 BracketBatch0180.bracket2891
  (1144112759746944328504048528631565705642437/10000000000000000000000000000000000000000) (1263809012062205683069407688467632047519/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2890
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2891
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (28635471979062022942165226990292970669147/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28635471979062022942165226990292970669147/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (143505387598025819124690222314732078001731/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (143505387598025819124690222314732078001731/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (143341373746667966917758178633098465673733/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (143341373746667966917758178633098465673733/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2891 BracketBatch0180.bracket2892 (143341373746667966917758178633098465673733/1250000000000000000000000000000000000000) (395160095501347123358489917109799545437/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2891 BracketBatch0180.bracket2892
  (143341373746667966917758178633098465673733/1250000000000000000000000000000000000000) (395160095501347123358489917109799545437/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2891
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2892
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (229608620156841310599504355703571324802769/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (229608620156841310599504355703571324802769/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (57533969391825925470324118530019166440133/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (57533969391825925470324118530019166440133/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (459744497724145012480800829823647990563301/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (459744497724145012480800829823647990563301/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2892 BracketBatch0180.bracket2893 (459744497724145012480800829823647990563301/4000000000000000000000000000000000000000) (6326086041866039554514381103229400605107/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2892 BracketBatch0180.bracket2893
  (459744497724145012480800829823647990563301/4000000000000000000000000000000000000000) (6326086041866039554514381103229400605107/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2892
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2893
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1150679387836518509406482370600383328802657/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1150679387836518509406482370600383328802657/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (72082988982563064238779919074249209479861/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (72082988982563064238779919074249209479861/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (2304007211557527537226961075788370680480433/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2304007211557527537226961075788370680480433/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2893 BracketBatch0180.bracket2894 (2304007211557527537226961075788370680480433/20000000000000000000000000000000000000000) (6329618636597087337979396094285979686181/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2893 BracketBatch0180.bracket2894
  (2304007211557527537226961075788370680480433/20000000000000000000000000000000000000000) (6329618636597087337979396094285979686181/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2893
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2894
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1153327823721009027820478705187987351677773/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1153327823721009027820478705187987351677773/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (115598849260972385727251586823814085702079/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (115598849260972385727251586823814085702079/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (2309316316330732885092994573426128208698563/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2309316316330732885092994573426128208698563/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2894 BracketBatch0180.bracket2895 (2309316316330732885092994573426128208698563/20000000000000000000000000000000000000000) (1583289836795300156367400644402627828801/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2894 BracketBatch0180.bracket2895
  (2309316316330732885092994573426128208698563/20000000000000000000000000000000000000000) (1583289836795300156367400644402627828801/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2894
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2895
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1155988492609723857272515868238140857020787/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1155988492609723857272515868238140857020787/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (23173229589081590817905616734658603753727/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (23173229589081590817905616734658603753727/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (2314649972063803398167796704971071044707137/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2314649972063803398167796704971071044707137/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0361.rows ScalarLogs0361.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2895 BracketBatch0181.bracket2896 (2314649972063803398167796704971071044707137/20000000000000000000000000000000000000000) (6336708208800400137522314431177683004063/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2895 BracketBatch0181.bracket2896
  (2314649972063803398167796704971071044707137/20000000000000000000000000000000000000000) (6336708208800400137522314431177683004063/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2895
