module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0217
public import BecknerOnofri.EntropyScalarCertificate.Bessel0218
public import BecknerOnofri.EntropyScalarCertificate.Bessel0597
public import BecknerOnofri.EntropyScalarCertificate.Bessel0598
public import BecknerOnofri.EntropyScalarCertificate.Brackets0087
public import BecknerOnofri.EntropyScalarCertificate.Logs0174
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1392
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (16623956581864321034101036699421285433021/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16623956581864321034101036699421285433021/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (3326495500600509489346320913890720572751/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3326495500600509489346320913890720572751/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (4157054260608358560104080158609361037097/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4157054260608358560104080158609361037097/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1392 BracketBatch0087.bracket1393 (4157054260608358560104080158609361037097/2500000000000000000000000000000000000000) (24848755081516041213777844629320541711/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1392 BracketBatch0087.bracket1393
  (4157054260608358560104080158609361037097/2500000000000000000000000000000000000000) (24848755081516041213777844629320541711/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1392
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1393
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (2079059687875318430841450571181700357969/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2079059687875318430841450571181700357969/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (16641008343460141067136219166597952907043/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16641008343460141067136219166597952907043/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (6654697169292537702773564747210311154159/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6654697169292537702773564747210311154159/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1393 BracketBatch0087.bracket1394 (6654697169292537702773564747210311154159/4000000000000000000000000000000000000000) (124338383453075536718753965616303975053/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1393 BracketBatch0087.bracket1394
  (6654697169292537702773564747210311154159/4000000000000000000000000000000000000000) (124338383453075536718753965616303975053/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1393
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1394
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (104006302146625881669601369791237205669/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (104006302146625881669601369791237205669/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (16649549122193564319241715725575626246571/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16649549122193564319241715725575626246571/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (33290557465653705386377934892173579153611/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33290557465653705386377934892173579153611/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1394 BracketBatch0087.bracket1395 (33290557465653705386377934892173579153611/20000000000000000000000000000000000000000) (622165423222749689846599677883095618901/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1394 BracketBatch0087.bracket1395
  (33290557465653705386377934892173579153611/20000000000000000000000000000000000000000) (622165423222749689846599677883095618901/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1394
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1395
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (2081193640274195539905214465696953280821/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2081193640274195539905214465696953280821/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (8329049929103007201468800678161323967267/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8329049929103007201468800678161323967267/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (16653824490199789361089658540949137090551/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16653824490199789361089658540949137090551/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1395 BracketBatch0087.bracket1396 (16653824490199789361089658540949137090551/10000000000000000000000000000000000000000) (31131969779331982139377592107282546601/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1395 BracketBatch0087.bracket1396
  (16653824490199789361089658540949137090551/10000000000000000000000000000000000000000) (31131969779331982139377592107282546601/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1395
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1396
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (16658099858206014402937601356322647934531/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16658099858206014402937601356322647934531/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1041666285659222556252483765682912035183/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1041666285659222556252483765682912035183/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (33324760428753575302977341607249240497459/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33324760428753575302977341607249240497459/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1396 BracketBatch0087.bracket1397 (33324760428753575302977341607249240497459/20000000000000000000000000000000000000000) (311556917517462551333818983912444853669/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1396 BracketBatch0087.bracket1397
  (33324760428753575302977341607249240497459/20000000000000000000000000000000000000000) (311556917517462551333818983912444853669/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1396
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1397
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (666666422821902436001589610037063702517/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (666666422821902436001589610037063702517/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (4168807819578820962179101911720822604093/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4168807819578820962179101911720822604093/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (33341891848862844748756147897809882979297/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33341891848862844748756147897809882979297/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1397 BracketBatch0087.bracket1398 (33341891848862844748756147897809882979297/20000000000000000000000000000000000000000) (2435893524401332334352809238990614867/39062500000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1397 BracketBatch0087.bracket1398
  (33341891848862844748756147897809882979297/20000000000000000000000000000000000000000) (2435893524401332334352809238990614867/39062500000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1397
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1398
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (16675231278315283848716407646883290416369/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16675231278315283848716407646883290416369/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (3336762400130682457643476779225864638411/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3336762400130682457643476779225864638411/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (4169880409871087017116723942876576701053/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4169880409871087017116723942876576701053/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1398 BracketBatch0087.bracket1399 (4169880409871087017116723942876576701053/2500000000000000000000000000000000000000) (312032058951241254775514482196382057023/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1398 BracketBatch0087.bracket1399
  (4169880409871087017116723942876576701053/2500000000000000000000000000000000000000) (312032058951241254775514482196382057023/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1398
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1399
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (4170953000163353072054345974032330798013/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4170953000163353072054345974032330798013/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (16692402756753463275755265667452611339669/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16692402756753463275755265667452611339669/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (33376214757406875563972649563581934531721/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33376214757406875563972649563581934531721/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0174.rows ScalarLogs0174.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1399 BracketBatch0087.bracket1400 (33376214757406875563972649563581934531721/20000000000000000000000000000000000000000) (124907992536761353031242391905911364521/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1399 BracketBatch0087.bracket1400
  (33376214757406875563972649563581934531721/20000000000000000000000000000000000000000) (124907992536761353031242391905911364521/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1399
