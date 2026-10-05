module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0405
public import BecknerOnofri.EntropyScalarCertificate.Bessel0406
public import BecknerOnofri.EntropyScalarCertificate.Bessel0691
public import BecknerOnofri.EntropyScalarCertificate.Bessel0692
public import BecknerOnofri.EntropyScalarCertificate.Brackets0162
public import BecknerOnofri.EntropyScalarCertificate.Logs0324
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2592
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (438323818771217606612384293781280275050847/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (438323818771217606612384293781280275050847/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (219928667165232287090251634939263645928347/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (219928667165232287090251634939263645928347/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (878181153101682180792887563659807566907541/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (878181153101682180792887563659807566907541/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2592 BracketBatch0162.bracket2593 (878181153101682180792887563659807566907541/20000000000000000000000000000000000000000) (4851356051036524961126871772233992332053/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2592 BracketBatch0162.bracket2593
  (878181153101682180792887563659807566907541/20000000000000000000000000000000000000000) (4851356051036524961126871772233992332053/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2592
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2593
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (439857334330464574180503269878527291856691/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (439857334330464574180503269878527291856691/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (220700824785466108406098500920722676262947/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (220700824785466108406098500920722676262947/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (176251796780279358198540054343994528876517/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (176251796780279358198540054343994528876517/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2593 BracketBatch0162.bracket2594 (176251796780279358198540054343994528876517/4000000000000000000000000000000000000000) (485649175251991435763526644425749528739/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2593 BracketBatch0162.bracket2594
  (176251796780279358198540054343994528876517/4000000000000000000000000000000000000000) (485649175251991435763526644425749528739/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2593
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2594
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (441401649570932216812197001841445352525891/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (441401649570932216812197001841445352525891/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (442956878976830404457378463952504791525179/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (442956878976830404457378463952504791525179/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (88435852854776262126957546579395014405107/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (88435852854776262126957546579395014405107/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2594 BracketBatch0162.bracket2595 (88435852854776262126957546579395014405107/2000000000000000000000000000000000000000) (972329191454206858688581618774789880741/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2594 BracketBatch0162.bracket2595
  (88435852854776262126957546579395014405107/2000000000000000000000000000000000000000) (972329191454206858688581618774789880741/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2594
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2595
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (55369609872103800557172307994063098940647/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (55369609872103800557172307994063098940647/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (222261569328129261210035109011565872696293/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (222261569328129261210035109011565872696293/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (443740008816544463438724340987818268458881/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (443740008816544463438724340987818268458881/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2595 BracketBatch0162.bracket2596 (443740008816544463438724340987818268458881/10000000000000000000000000000000000000000) (2433409393662291079707983866157422434201/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2595 BracketBatch0162.bracket2596
  (443740008816544463438724340987818268458881/10000000000000000000000000000000000000000) (2433409393662291079707983866157422434201/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2595
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2596
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (444523138656258522420070218023131745392583/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (444523138656258522420070218023131745392583/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (111525136592525075646301855240433405683847/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (111525136592525075646301855240433405683847/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (890623685026358825005277638984865368127971/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (890623685026358825005277638984865368127971/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2596 BracketBatch0162.bracket2597 (890623685026358825005277638984865368127971/20000000000000000000000000000000000000000) (4872010365851970209569030976394721196917/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2596 BracketBatch0162.bracket2597
  (890623685026358825005277638984865368127971/20000000000000000000000000000000000000000) (4872010365851970209569030976394721196917/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2596
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2597
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (89220109274020060517041484192346724547077/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (89220109274020060517041484192346724547077/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (44768922156153782960030668522635686212461/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44768922156153782960030668522635686212461/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (178757953586327626437102821237618096971999/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (178757953586327626437102821237618096971999/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2597 BracketBatch0162.bracket2598 (178757953586327626437102821237618096971999/4000000000000000000000000000000000000000) (4877220817174124720914097219243142729037/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2597 BracketBatch0162.bracket2598
  (178757953586327626437102821237618096971999/4000000000000000000000000000000000000000) (4877220817174124720914097219243142729037/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2597
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2598
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (447689221561537829600306685226356862124607/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (447689221561537829600306685226356862124607/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (224644642693100128433749606075673633772547/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (224644642693100128433749606075673633772547/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (896978506947738086467805897377704129669701/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (896978506947738086467805897377704129669701/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2598 BracketBatch0162.bracket2599 (896978506947738086467805897377704129669701/20000000000000000000000000000000000000000) (4882450266774430957013347666849391830247/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2598 BracketBatch0162.bracket2599
  (896978506947738086467805897377704129669701/20000000000000000000000000000000000000000) (4882450266774430957013347666849391830247/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2598
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2599
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (449289285386200256867499212151347267545091/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (449289285386200256867499212151347267545091/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (22545043037148160712381400576390998816303/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22545043037148160712381400576390998816303/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (900190146129163471115127223679167243871151/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (900190146129163471115127223679167243871151/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0324.rows ScalarLogs0324.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2599 BracketBatch0162.bracket2600 (900190146129163471115127223679167243871151/20000000000000000000000000000000000000000) (4887698841311824741823277691048203261343/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2599 BracketBatch0162.bracket2600
  (900190146129163471115127223679167243871151/20000000000000000000000000000000000000000) (4887698841311824741823277691048203261343/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2599
