module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0047
public import BecknerOnofri.EntropyScalarCertificate.Bessel0048
public import BecknerOnofri.EntropyScalarCertificate.Bessel0512
public import BecknerOnofri.EntropyScalarCertificate.Bessel0513
public import BecknerOnofri.EntropyScalarCertificate.Brackets0019
public import BecknerOnofri.EntropyScalarCertificate.Logs0038
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0304
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (590581789603543786252559968133868091457/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (590581789603543786252559968133868091457/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1183205733788889960949608232465200402173/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1183205733788889960949608232465200402173/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (2364369312995977533454728168732936585087/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2364369312995977533454728168732936585087/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0304 BracketBatch0019.bracket0305 (2364369312995977533454728168732936585087/20000000000000000000000000000000000000000) (73946783773277202921027587162785333/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0304 BracketBatch0019.bracket0305
  (2364369312995977533454728168732936585087/20000000000000000000000000000000000000000) (73946783773277202921027587162785333/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0304
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0305
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (118320573378888996094960823246520040217/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (118320573378888996094960823246520040217/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (237049606986140942028033797569517713639/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (237049606986140942028033797569517713639/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (473690753743918934217955444062557794073/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (473690753743918934217955444062557794073/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0305 BracketBatch0019.bracket0306 (473690753743918934217955444062557794073/4000000000000000000000000000000000000000) (5956417948646695032410698391091203/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0305 BracketBatch0019.bracket0306
  (473690753743918934217955444062557794073/4000000000000000000000000000000000000000) (5956417948646695032410698391091203/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0305
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0306
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (9259750272896130547970070217559285689/78125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9259750272896130547970070217559285689/78125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1187290482901506841039979025591605598821/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1187290482901506841039979025591605598821/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (2372538517832211551180148013439194167013/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2372538517832211551180148013439194167013/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0306 BracketBatch0019.bracket0307 (2372538517832211551180148013439194167013/20000000000000000000000000000000000000000) (29986513053241782554854599437950927/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0306 BracketBatch0019.bracket0307
  (2372538517832211551180148013439194167013/20000000000000000000000000000000000000000) (29986513053241782554854599437950927/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0306
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0307
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (593645241450753420519989512795802799409/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (593645241450753420519989512795802799409/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1189333077970374659962752074200526773447/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1189333077970374659962752074200526773447/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (475324712174376300200546219958426474453/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (475324712174376300200546219958426474453/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0307 BracketBatch0019.bracket0308 (475324712174376300200546219958426474453/4000000000000000000000000000000000000000) (75479967643163046061099287046296073/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0307 BracketBatch0019.bracket0308
  (475324712174376300200546219958426474453/4000000000000000000000000000000000000000) (75479967643163046061099287046296073/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0307
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0308
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (297333269492593664990688018550131693361/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (297333269492593664990688018550131693361/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (119137582040648996677092098366637063113/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (119137582040648996677092098366637063113/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (1190354449188432313366836528933448702287/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1190354449188432313366836528933448702287/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0308 BracketBatch0019.bracket0309 (1190354449188432313366836528933448702287/10000000000000000000000000000000000000000) (7599628844933372377055953804987483/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0308 BracketBatch0019.bracket0309
  (1190354449188432313366836528933448702287/10000000000000000000000000000000000000000) (7599628844933372377055953804987483/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0308
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0309
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1191375820406489966770920983666370631127/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1191375820406489966770920983666370631127/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1193418710479138263251650699415709197767/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1193418710479138263251650699415709197767/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (1192397265442814115011285841541039914447/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1192397265442814115011285841541039914447/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0309 BracketBatch0019.bracket0310 (1192397265442814115011285841541039914447/10000000000000000000000000000000000000000) (612122033031568362884120262931293/40000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0309 BracketBatch0019.bracket0310
  (1192397265442814115011285841541039914447/10000000000000000000000000000000000000000) (612122033031568362884120262931293/40000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0309
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0310
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (298354677619784565812912674853927299441/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (298354677619784565812912674853927299441/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1195461748457708961671084060515445433841/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1195461748457708961671084060515445433841/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (477776091787369444984546951986230926321/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (477776091787369444984546951986230926321/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0310 BracketBatch0019.bracket0311 (477776091787369444984546951986230926321/4000000000000000000000000000000000000000) (154073747551178848906349229247524619/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0310 BracketBatch0019.bracket0311
  (477776091787369444984546951986230926321/4000000000000000000000000000000000000000) (154073747551178848906349229247524619/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0310
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0311
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (597730874228854480835542030257722716919/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (597730874228854480835542030257722716919/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1197504934611695593507223053370542837343/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1197504934611695593507223053370542837343/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (2392966683069404555178307113885988271181/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2392966683069404555178307113885988271181/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0038.rows ScalarLogs0038.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0311 BracketBatch0019.bracket0312 (2392966683069404555178307113885988271181/20000000000000000000000000000000000000000) (155122312998235420307799685186212191/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0311 BracketBatch0019.bracket0312
  (2392966683069404555178307113885988271181/20000000000000000000000000000000000000000) (155122312998235420307799685186212191/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0311
