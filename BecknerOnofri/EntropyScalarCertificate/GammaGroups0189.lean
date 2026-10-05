module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0236
public import BecknerOnofri.EntropyScalarCertificate.Bessel0237
public import BecknerOnofri.EntropyScalarCertificate.Bessel0607
public import BecknerOnofri.EntropyScalarCertificate.Brackets0094
public import BecknerOnofri.EntropyScalarCertificate.Brackets0095
public import BecknerOnofri.EntropyScalarCertificate.Logs0189
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1512
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (8861513375374263799643313385346560551591/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8861513375374263799643313385346560551591/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (4433221922817962864844592071656169604861/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4433221922817962864844592071656169604861/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (17727957221010189529332497528658899761313/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17727957221010189529332497528658899761313/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1512 BracketBatch0094.bracket1513 (17727957221010189529332497528658899761313/10000000000000000000000000000000000000000) (340754919146294895842524034580673639099/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1512 BracketBatch0094.bracket1513
  (17727957221010189529332497528658899761313/10000000000000000000000000000000000000000) (340754919146294895842524034580673639099/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1512
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1513
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (17732887691271851459378368286624678419441/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17732887691271851459378368286624678419441/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (277230643788355367862489350558141840149/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (277230643788355367862489350558141840149/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (35475648893726595002577686722345756188977/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35475648893726595002577686722345756188977/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1513 BracketBatch0094.bracket1514 (35475648893726595002577686722345756188977/20000000000000000000000000000000000000000) (170510992740541348363343705628491759839/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1513 BracketBatch0094.bracket1514
  (35475648893726595002577686722345756188977/20000000000000000000000000000000000000000) (170510992740541348363343705628491759839/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1513
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1514
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (17742761202454743543199318435721077769533/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17742761202454743543199318435721077769533/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (17752647309992841876399619484504632978619/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17752647309992841876399619484504632978619/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (4436926064055948177449867240028213843519/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4436926064055948177449867240028213843519/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1514 BracketBatch0094.bracket1515 (4436926064055948177449867240028213843519/2500000000000000000000000000000000000000) (170644665063664124896106142933376667797/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1514 BracketBatch0094.bracket1515
  (4436926064055948177449867240028213843519/2500000000000000000000000000000000000000) (170644665063664124896106142933376667797/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1514
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1515
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (2219080913749105234549952435563079122327/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2219080913749105234549952435563079122327/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (17762546039648973806235700994865377251057/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17762546039648973806235700994865377251057/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (35515193349641815682635320479370010229673/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35515193349641815682635320479370010229673/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1515 BracketBatch0094.bracket1516 (35515193349641815682635320479370010229673/20000000000000000000000000000000000000000) (683113907016421623885190545045917186533/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1515 BracketBatch0094.bracket1516
  (35515193349641815682635320479370010229673/20000000000000000000000000000000000000000) (683113907016421623885190545045917186533/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1515
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1516
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (8881273019824486903117850497432688625527/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8881273019824486903117850497432688625527/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (8886228708626682903439332492701338772971/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8886228708626682903439332492701338772971/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (8883750864225584903278591495067013699249/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8883750864225584903278591495067013699249/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1516 BracketBatch0094.bracket1517 (8883750864225584903278591495067013699249/5000000000000000000000000000000000000000) (170912428023852291866771145539782207523/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1516 BracketBatch0094.bracket1517
  (8883750864225584903278591495067013699249/5000000000000000000000000000000000000000) (170912428023852291866771145539782207523/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1516
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1517
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (17772457417253365806878664985402677545939/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17772457417253365806878664985402677545939/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (17782381468703854050966103576527904315197/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17782381468703854050966103576527904315197/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (2222177430372326241115298035120661366321/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2222177430372326241115298035120661366321/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1517 BracketBatch0094.bracket1518 (2222177430372326241115298035120661366321/1250000000000000000000000000000000000000) (684186076341160560388630390772867781717/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1517 BracketBatch0094.bracket1518
  (2222177430372326241115298035120661366321/1250000000000000000000000000000000000000) (684186076341160560388630390772867781717/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1517
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1518
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (8891190734351927025483051788263952157597/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8891190734351927025483051788263952157597/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (222403977749576196883762656701096973159/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (222403977749576196883762656701096973159/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (17787349844334974900833558056307831083957/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17787349844334974900833558056307831083957/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1518 BracketBatch0094.bracket1519 (17787349844334974900833558056307831083957/10000000000000000000000000000000000000000) (684723000604813409832739423297346410573/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1518 BracketBatch0094.bracket1519
  (17787349844334974900833558056307831083957/10000000000000000000000000000000000000000) (684723000604813409832739423297346410573/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1518
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1519
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (17792318219966095750701012536087757852717/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17792318219966095750701012536087757852717/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (4450566924268445317954638689891766864589/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4450566924268445317954638689891766864589/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (35594585917039877022519567295654825311073/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35594585917039877022519567295654825311073/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0189.rows ScalarLogs0189.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1519 BracketBatch0095.bracket1520 (35594585917039877022519567295654825311073/20000000000000000000000000000000000000000) (685260485739104654841072544836700319143/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1519 BracketBatch0095.bracket1520
  (35594585917039877022519567295654825311073/20000000000000000000000000000000000000000) (685260485739104654841072544836700319143/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1519
