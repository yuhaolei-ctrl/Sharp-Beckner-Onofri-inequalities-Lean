module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0308
public import BecknerOnofri.EntropyScalarCertificate.Bessel0309
public import BecknerOnofri.EntropyScalarCertificate.Bessel0310
public import BecknerOnofri.EntropyScalarCertificate.Bessel0643
public import BecknerOnofri.EntropyScalarCertificate.Brackets0123
public import BecknerOnofri.EntropyScalarCertificate.Brackets0124
public import BecknerOnofri.EntropyScalarCertificate.Logs0247
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1976
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (10076122100585253186335381131397624121667/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10076122100585253186335381131397624121667/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (50864671247710569267956803686518345483283/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (50864671247710569267956803686518345483283/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (50622640875318417599816854671753233045809/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (50622640875318417599816854671753233045809/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1976 BracketBatch0123.bracket1977 (50622640875318417599816854671753233045809/10000000000000000000000000000000000000000) (372821500692875377144848312415313156773/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1976 BracketBatch0123.bracket1977
  (50622640875318417599816854671753233045809/10000000000000000000000000000000000000000) (372821500692875377144848312415313156773/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1976
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1977
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (635808390596382115849460046081479318541/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (635808390596382115849460046081479318541/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (12839611002760485325543761713210861852367/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12839611002760485325543761713210861852367/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (25555778814688127642532962634840448223187/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25555778814688127642532962634840448223187/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1977 BracketBatch0123.bracket1978 (25555778814688127642532962634840448223187/5000000000000000000000000000000000000000) (1875726940264323224008395750302252600729/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1977 BracketBatch0123.bracket1978
  (25555778814688127642532962634840448223187/5000000000000000000000000000000000000000) (1875726940264323224008395750302252600729/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1977
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1978
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (10271688802208388260435009370568689481893/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10271688802208388260435009370568689481893/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (51458389677759312039909866081921741332389/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (51458389677759312039909866081921741332389/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (51408416844400626671042456467382594370927/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51408416844400626671042456467382594370927/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1978 BracketBatch0123.bracket1979 (51408416844400626671042456467382594370927/10000000000000000000000000000000000000000) (1903211700852456680464230612226625798551/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1978 BracketBatch0123.bracket1979
  (51408416844400626671042456467382594370927/10000000000000000000000000000000000000000) (1903211700852456680464230612226625798551/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1978
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1979
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (25729194838879656019954933040960870666193/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25729194838879656019954933040960870666193/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (6444842244911975830376630972696461245841/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6444842244911975830376630972696461245841/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (51508563818527559341461456931746715649557/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51508563818527559341461456931746715649557/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1979 BracketBatch0123.bracket1980 (51508563818527559341461456931746715649557/10000000000000000000000000000000000000000) (29775865985128240154673035485898888227/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1979 BracketBatch0123.bracket1980
  (51508563818527559341461456931746715649557/10000000000000000000000000000000000000000) (29775865985128240154673035485898888227/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1979
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1980
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (2062349518371832265720521911262867598669/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2062349518371832265720521911262867598669/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (51659491284194115240204003402363722879223/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (51659491284194115240204003402363722879223/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (25804557310872480470804262795983853211487/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25804557310872480470804262795983853211487/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1980 BracketBatch0123.bracket1981 (25804557310872480470804262795983853211487/5000000000000000000000000000000000000000) (954052336364482554708916767466246658947/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1980 BracketBatch0123.bracket1981
  (25804557310872480470804262795983853211487/5000000000000000000000000000000000000000) (954052336364482554708916767466246658947/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1980
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1981
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (2582974564209705762010200170118186143961/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2582974564209705762010200170118186143961/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (10352130420117671037541700216994353332801/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10352130420117671037541700216994353332801/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (4136805735391298817116500179493419581729/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4136805735391298817116500179493419581729/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1981 BracketBatch0123.bracket1982 (4136805735391298817116500179493419581729/800000000000000000000000000000000000000) (1910559472359473027144231262707512207017/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1981 BracketBatch0123.bracket1982
  (4136805735391298817116500179493419581729/800000000000000000000000000000000000000) (1910559472359473027144231262707512207017/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1981
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1982
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (25880326050294177593854250542485883332001/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25880326050294177593854250542485883332001/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (51862222876401934366872652053045296161531/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (51862222876401934366872652053045296161531/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (103622874976990289554581153138017062825533/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (103622874976990289554581153138017062825533/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1982 BracketBatch0123.bracket1983 (103622874976990289554581153138017062825533/20000000000000000000000000000000000000000) (478254961136367744102924268365828279079/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1982 BracketBatch0123.bracket1983
  (103622874976990289554581153138017062825533/20000000000000000000000000000000000000000) (478254961136367744102924268365828279079/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1982
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1983
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (6482777859550241795859081506630662020191/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6482777859550241795859081506630662020191/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1299105152488695438490660426950788558429/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1299105152488695438490660426950788558429/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (811143976374607436769523977586537800771/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (811143976374607436769523977586537800771/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0247.rows ScalarLogs0247.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1983 BracketBatch0124.bracket1984 (811143976374607436769523977586537800771/156250000000000000000000000000000000000) (1915485812034858742992953051878688946469/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1983 BracketBatch0124.bracket1984
  (811143976374607436769523977586537800771/156250000000000000000000000000000000000) (1915485812034858742992953051878688946469/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1983
