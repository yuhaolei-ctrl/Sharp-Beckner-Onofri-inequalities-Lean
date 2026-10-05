module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0102
public import BecknerOnofri.EntropyScalarCertificate.Bessel0103
public import BecknerOnofri.EntropyScalarCertificate.Bessel0540
public import BecknerOnofri.EntropyScalarCertificate.Brackets0041
public import BecknerOnofri.EntropyScalarCertificate.Logs0082
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0656
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (191106900471973839156123317361259517751/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (191106900471973839156123317361259517751/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (956590124412840051507613283985579814459/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (956590124412840051507613283985579814459/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (956062313386354623644114935395938701607/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (956062313386354623644114935395938701607/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0656 BracketBatch0041.bracket0657 (956062313386354623644114935395938701607/5000000000000000000000000000000000000000) (490251478461122384159933755153592959/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0656 BracketBatch0041.bracket0657
  (956062313386354623644114935395938701607/5000000000000000000000000000000000000000) (490251478461122384159933755153592959/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0656
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0657
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (382636049765136020603045313594231925783/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (382636049765136020603045313594231925783/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (957645871091486513971558978175293892821/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (957645871091486513971558978175293892821/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (3828471991008653130958344524321747414557/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3828471991008653130958344524321747414557/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0657 BracketBatch0041.bracket0658 (3828471991008653130958344524321747414557/20000000000000000000000000000000000000000) (196944175926527557634766624913279043/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0657 BracketBatch0041.bracket0658
  (3828471991008653130958344524321747414557/20000000000000000000000000000000000000000) (196944175926527557634766624913279043/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0657
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0658
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1915291742182973027943117956350587785639/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1915291742182973027943117956350587785639/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (958701742555686779544082491052594949261/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (958701742555686779544082491052594949261/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (3832695227294346587031282938455777684161/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3832695227294346587031282938455777684161/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0658 BracketBatch0041.bracket0659 (3832695227294346587031282938455777684161/20000000000000000000000000000000000000000) (988952490078445784578853064492851627/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0658 BracketBatch0041.bracket0659
  (3832695227294346587031282938455777684161/20000000000000000000000000000000000000000) (988952490078445784578853064492851627/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0658
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0659
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1917403485111373559088164982105189898519/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1917403485111373559088164982105189898519/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (959757738965414485289865947665560441743/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (959757738965414485289865947665560441743/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (767383792608440505933579375487262156401/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (767383792608440505933579375487262156401/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0659 BracketBatch0041.bracket0660 (767383792608440505933579375487262156401/4000000000000000000000000000000000000000) (99319781848927668629429791809957673/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0659 BracketBatch0041.bracket0660
  (767383792608440505933579375487262156401/4000000000000000000000000000000000000000) (99319781848927668629429791809957673/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0659
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0660
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1919515477930828970579731895331120883483/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1919515477930828970579731895331120883483/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (480406930240369429673707178160655827889/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (480406930240369429673707178160655827889/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (3841143198892306689274560607973744195039/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3841143198892306689274560607973744195039/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0660 BracketBatch0041.bracket0661 (3841143198892306689274560607973744195039/20000000000000000000000000000000000000000) (498728447565830676086089228908485863/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0660 BracketBatch0041.bracket0661
  (3841143198892306689274560607973744195039/20000000000000000000000000000000000000000) (498728447565830676086089228908485863/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0660
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0661
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1921627720961477718694828712642623311553/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1921627720961477718694828712642623311553/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (76949608580945989719461774382081744419/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (76949608580945989719461774382081744419/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (961341983871281865420343268048666730507/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (961341983871281865420343268048666730507/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0661 BracketBatch0041.bracket0662 (961341983871281865420343268048666730507/5000000000000000000000000000000000000000) (200345950061814000456655891780691583/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0661 BracketBatch0041.bracket0662
  (961341983871281865420343268048666730507/5000000000000000000000000000000000000000) (200345950061814000456655891780691583/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0661
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0662
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (240467526815456217873318044944005451309/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (240467526815456217873318044944005451309/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (481463239734466691945022739606785859463/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (481463239734466691945022739606785859463/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (962398293365379127691658829494796762081/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (962398293365379127691658829494796762081/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0662 BracketBatch0041.bracket0663 (962398293365379127691658829494796762081/5000000000000000000000000000000000000000) (503008207180964336790173441516479349/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0662 BracketBatch0041.bracket0663
  (962398293365379127691658829494796762081/5000000000000000000000000000000000000000) (503008207180964336790173441516479349/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0662
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0663
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1925852958937866767780090958427143437849/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1925852958937866767780090958427143437849/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1927965954524842604037177752349711000493/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1927965954524842604037177752349711000493/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1926909456731354685908634355388427219171/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1926909456731354685908634355388427219171/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0082.rows ScalarLogs0082.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0663 BracketBatch0041.bracket0664 (1926909456731354685908634355388427219171/10000000000000000000000000000000000000000) (1010316917667635700124936904742311059/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0663 BracketBatch0041.bracket0664
  (1926909456731354685908634355388427219171/10000000000000000000000000000000000000000) (1010316917667635700124936904742311059/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0663
