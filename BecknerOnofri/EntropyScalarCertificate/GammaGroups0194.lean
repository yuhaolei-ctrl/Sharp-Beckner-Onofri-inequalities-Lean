module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0242
public import BecknerOnofri.EntropyScalarCertificate.Bessel0243
public import BecknerOnofri.EntropyScalarCertificate.Bessel0610
public import BecknerOnofri.EntropyScalarCertificate.Brackets0097
public import BecknerOnofri.EntropyScalarCertificate.Logs0194
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1552
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (4531882410134533024099741604223622068789/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4531882410134533024099741604223622068789/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (181379141335636514490183331221662662133/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (181379141335636514490183331221662662133/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (4533180471762722943177162442382594311057/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4533180471762722943177162442382594311057/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1552 BracketBatch0097.bracket1553 (4533180471762722943177162442382594311057/2500000000000000000000000000000000000000) (351658910182183032961120703834967118601/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1552 BracketBatch0097.bracket1553
  (4533180471762722943177162442382594311057/2500000000000000000000000000000000000000) (351658910182183032961120703834967118601/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1552
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1553
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (18137914133563651449018333122166266213297/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18137914133563651449018333122166266213297/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (9074156139813537895379821828415080324367/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9074156139813537895379821828415080324367/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (36286226413190727239777976778996426862031/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36286226413190727239777976778996426862031/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1553 BracketBatch0097.bracket1554 (36286226413190727239777976778996426862031/20000000000000000000000000000000000000000) (175968723527448366572574989317883715859/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1553 BracketBatch0097.bracket1554
  (36286226413190727239777976778996426862031/20000000000000000000000000000000000000000) (175968723527448366572574989317883715859/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1553
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1554
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (18148312279627075790759643656830160648731/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18148312279627075790759643656830160648731/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (9079362053641574110890936539650351851573/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9079362053641574110890936539650351851573/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (36307036386910224012541516736130864351877/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36307036386910224012541516736130864351877/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1554 BracketBatch0097.bracket1555 (36307036386910224012541516736130864351877/20000000000000000000000000000000000000000) (704432559604241153483754069094918058709/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1554 BracketBatch0097.bracket1555
  (36307036386910224012541516736130864351877/20000000000000000000000000000000000000000) (704432559604241153483754069094918058709/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1554
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1555
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (18158724107283148221781873079300703703143/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18158724107283148221781873079300703703143/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (2271143705645353165020214969669457187521/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2271143705645353165020214969669457187521/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (36327873752445973541943592836656361203311/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36327873752445973541943592836656361203311/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1555 BracketBatch0097.bracket1556 (36327873752445973541943592836656361203311/20000000000000000000000000000000000000000) (704990817760180354140711899520255711191/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1555 BracketBatch0097.bracket1556
  (36327873752445973541943592836656361203311/20000000000000000000000000000000000000000) (704990817760180354140711899520255711191/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1555
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1556
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (3633829929032565064032343951471131500033/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3633829929032565064032343951471131500033/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (18179588921973520352749318207446660658207/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18179588921973520352749318207446660658207/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (9087184641784086418227759491200579539593/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9087184641784086418227759491200579539593/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1556 BracketBatch0097.bracket1557 (9087184641784086418227759491200579539593/5000000000000000000000000000000000000000) (705549669491803184252008226781333885399/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1556 BracketBatch0097.bracket1557
  (9087184641784086418227759491200579539593/5000000000000000000000000000000000000000) (705549669491803184252008226781333885399/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1556
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1557
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (4544897230493380088187329551861665164551/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4544897230493380088187329551861665164551/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (18190041966499347398852379699890260503499/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18190041966499347398852379699890260503499/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (36369630888472867751601697907336921161703/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36369630888472867751601697907336921161703/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1557 BracketBatch0097.bracket1558 (36369630888472867751601697907336921161703/20000000000000000000000000000000000000000) (1129774585144041714586324089839933003/16000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1557 BracketBatch0097.bracket1558
  (36369630888472867751601697907336921161703/20000000000000000000000000000000000000000) (1129774585144041714586324089839933003/16000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1557
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1558
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (2273755245812418424856547462486282562937/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2273755245812418424856547462486282562937/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (18200508807601366390825679298707715239597/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18200508807601366390825679298707715239597/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (36390550774100713789678058998597975743093/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36390550774100713789678058998597975743093/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1558 BracketBatch0097.bracket1559 (36390550774100713789678058998597975743093/20000000000000000000000000000000000000000) (141333831469498637176736330493725891501/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1558 BracketBatch0097.bracket1559
  (36390550774100713789678058998597975743093/20000000000000000000000000000000000000000) (141333831469498637176736330493725891501/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1558
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1559
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (9100254403800683195412839649353857619797/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9100254403800683195412839649353857619797/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (18210989474217829075664725232798028134067/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18210989474217829075664725232798028134067/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (36411498281819195466490404531505743373661/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36411498281819195466490404531505743373661/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0194.rows ScalarLogs0194.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1559 BracketBatch0097.bracket1560 (36411498281819195466490404531505743373661/20000000000000000000000000000000000000000) (707229795308579876215461045769039100547/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1559 BracketBatch0097.bracket1560
  (36411498281819195466490404531505743373661/20000000000000000000000000000000000000000) (707229795308579876215461045769039100547/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1559
