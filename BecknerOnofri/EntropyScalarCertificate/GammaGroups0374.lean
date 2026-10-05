module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0467
public import BecknerOnofri.EntropyScalarCertificate.Bessel0468
public import BecknerOnofri.EntropyScalarCertificate.Bessel0722
public import BecknerOnofri.EntropyScalarCertificate.Bessel0723
public import BecknerOnofri.EntropyScalarCertificate.Brackets0187
public import BecknerOnofri.EntropyScalarCertificate.Logs0374
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2992
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (372337100352041076472351580630768064057191/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (372337100352041076472351580630768064057191/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1493790467291388955873609806317117244612603/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1493790467291388955873609806317117244612603/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (2983138868699553261763016128840189500841367/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2983138868699553261763016128840189500841367/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket2992 BracketBatch0187.bracket2993 (2983138868699553261763016128840189500841367/20000000000000000000000000000000000000000) (6726199442561410095341825321425015030643/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket2992 BracketBatch0187.bracket2993
  (2983138868699553261763016128840189500841367/20000000000000000000000000000000000000000) (6726199442561410095341825321425015030643/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2992
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2993
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (7468952336456944779368049031585586223063/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7468952336456944779368049031585586223063/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (59930365297134838439322060736586684376709/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (59930365297134838439322060736586684376709/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (119681983988790396674266452989271374161213/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (119681983988790396674266452989271374161213/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket2993 BracketBatch0187.bracket2994 (119681983988790396674266452989271374161213/800000000000000000000000000000000000000) (269230414468369968506212321257637887021/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket2993 BracketBatch0187.bracket2994
  (119681983988790396674266452989271374161213/800000000000000000000000000000000000000) (269230414468369968506212321257637887021/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2993
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2994
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (749129566214185480491525759207333554708861/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (749129566214185480491525759207333554708861/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1502754636452024889294293371296848587871779/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1502754636452024889294293371296848587871779/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (3001013768880395850277344889711515697289501/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3001013768880395850277344889711515697289501/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket2994 BracketBatch0187.bracket2995 (3001013768880395850277344889711515697289501/20000000000000000000000000000000000000000) (6735334308981578906243196115696181722407/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket2994 BracketBatch0187.bracket2995
  (3001013768880395850277344889711515697289501/20000000000000000000000000000000000000000) (6735334308981578906243196115696181722407/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2994
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2995
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (46961082389125777790446667853026518370993/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (46961082389125777790446667853026518370993/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (753638610941204429030123075541285341152931/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (753638610941204429030123075541285341152931/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1505015929167216873677269761189709635088819/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1505015929167216873677269761189709635088819/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket2995 BracketBatch0187.bracket2996 (1505015929167216873677269761189709635088819/10000000000000000000000000000000000000000) (673992135156520847296781530515142730753/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket2995 BracketBatch0187.bracket2996
  (1505015929167216873677269761189709635088819/10000000000000000000000000000000000000000) (673992135156520847296781530515142730753/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2995
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2996
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1507277221882408858060246151082570682305859/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1507277221882408858060246151082570682305859/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1511827134170336974030033323302587092264291/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1511827134170336974030033323302587092264291/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (60382087121054916641805589487703155491403/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (60382087121054916641805589487703155491403/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket2996 BracketBatch0187.bracket2997 (60382087121054916641805589487703155491403/400000000000000000000000000000000000000) (6744521557088918430063668299322459102341/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket2996 BracketBatch0187.bracket2997
  (60382087121054916641805589487703155491403/400000000000000000000000000000000000000) (6744521557088918430063668299322459102341/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2996
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2997
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (47244597942823030438438541353205846633259/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (47244597942823030438438541353205846633259/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (303280924348356945445843200530414407464821/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (303280924348356945445843200530414407464821/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (3028231755912121701259249325954659129588393/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3028231755912121701259249325954659129588393/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket2997 BracketBatch0187.bracket2998 (3028231755912121701259249325954659129588393/20000000000000000000000000000000000000000) (421820937101615965805598335926208524623/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket2997 BracketBatch0187.bracket2998
  (3028231755912121701259249325954659129588393/20000000000000000000000000000000000000000) (421820937101615965805598335926208524623/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2997
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2998
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (758202310870892363614608001326036018662051/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (758202310870892363614608001326036018662051/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (30420198720862084191011990740362402552889/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30420198720862084191011990740362402552889/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (379676819723111117097476942458774020621069/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (379676819723111117097476942458774020621069/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket2998 BracketBatch0187.bracket2999 (379676819723111117097476942458774020621069/2500000000000000000000000000000000000000) (6753761729695901918651462029690424865437/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket2998 BracketBatch0187.bracket2999
  (379676819723111117097476942458774020621069/2500000000000000000000000000000000000000) (6753761729695901918651462029690424865437/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2998
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2999
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1521009936043104209550599537018120127644447/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1521009936043104209550599537018120127644447/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1525643331587066441002188996329713248462843/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1525643331587066441002188996329713248462843/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (304665326763017065055278853334783337610729/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (304665326763017065055278853334783337610729/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0374.rows ScalarLogs0374.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket2999 BracketBatch0187.bracket3000 (304665326763017065055278853334783337610729/2000000000000000000000000000000000000000) (3379200917134009053982288744187846349331/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket2999 BracketBatch0187.bracket3000
  (304665326763017065055278853334783337610729/2000000000000000000000000000000000000000) (3379200917134009053982288744187846349331/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2999
