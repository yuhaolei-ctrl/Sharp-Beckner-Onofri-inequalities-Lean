module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0362
public import BecknerOnofri.EntropyScalarCertificate.Bessel0363
public import BecknerOnofri.EntropyScalarCertificate.Bessel0670
public import BecknerOnofri.EntropyScalarCertificate.Brackets0145
public import BecknerOnofri.EntropyScalarCertificate.Logs0290
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2320
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (79754358805202290053742306727881760649259/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (79754358805202290053742306727881760649259/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (160516334590286975019726753585053259314077/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (160516334590286975019726753585053259314077/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (64005010440138311025442273408163356122519/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64005010440138311025442273408163356122519/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2320 BracketBatch0145.bracket2321 (64005010440138311025442273408163356122519/4000000000000000000000000000000000000000) (3387691049454400751771130054382625832301/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2320 BracketBatch0145.bracket2321
  (64005010440138311025442273408163356122519/4000000000000000000000000000000000000000) (3387691049454400751771130054382625832301/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2320
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2321
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (80258167295143487509863376792526629657037/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (80258167295143487509863376792526629657037/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (161536872461333599329815627710029329938031/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (161536872461333599329815627710029329938031/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (64410641410324114869908476259016517850421/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64410641410324114869908476259016517850421/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2321 BracketBatch0145.bracket2322 (64410641410324114869908476259016517850421/4000000000000000000000000000000000000000) (3396134573813170987634052174217490485763/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2321 BracketBatch0145.bracket2322
  (64410641410324114869908476259016517850421/4000000000000000000000000000000000000000) (3396134573813170987634052174217490485763/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2321
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2322
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (40384218115333399832453906927507332484507/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (40384218115333399832453906927507332484507/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (162570581302973674905272326671154485841257/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (162570581302973674905272326671154485841257/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (64821490752861454847017590876236763155857/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64821490752861454847017590876236763155857/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2322 BracketBatch0145.bracket2323 (64821490752861454847017590876236763155857/4000000000000000000000000000000000000000) (1702315653708146567668273580389006975089/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2322 BracketBatch0145.bracket2323
  (64821490752861454847017590876236763155857/4000000000000000000000000000000000000000) (1702315653708146567668273580389006975089/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2322
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2323
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (81285290651486837452636163335577242920627/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (81285290651486837452636163335577242920627/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (163617717690210158347373159523049406825069/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (163617717690210158347373159523049406825069/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (326188298993183833252645486194203892666323/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (326188298993183833252645486194203892666323/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2323 BracketBatch0145.bracket2324 (326188298993183833252645486194203892666323/20000000000000000000000000000000000000000) (3413181808608719767025646598250669469037/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2323 BracketBatch0145.bracket2324
  (326188298993183833252645486194203892666323/20000000000000000000000000000000000000000) (3413181808608719767025646598250669469037/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2323
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2324
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (81808858845105079173686579761524703412533/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (81808858845105079173686579761524703412533/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (32935708981178675935019545359609459441363/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (32935708981178675935019545359609459441363/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (328296262596103538022470886321096704031881/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (328296262596103538022470886321096704031881/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2324 BracketBatch0145.bracket2325 (328296262596103538022470886321096704031881/20000000000000000000000000000000000000000) (3421786641711749724972350430164749766269/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2324 BracketBatch0145.bracket2325
  (328296262596103538022470886321096704031881/20000000000000000000000000000000000000000) (3421786641711749724972350430164749766269/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2324
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2325
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (41169636226473344918774431699511824301703/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (41169636226473344918774431699511824301703/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (165753333161373903649548854233898781882037/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (165753333161373903649548854233898781882037/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (330431878067267283324646581031946079088849/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (330431878067267283324646581031946079088849/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2325 BracketBatch0145.bracket2326 (330431878067267283324646581031946079088849/20000000000000000000000000000000000000000) (3430446376974419026035209421542558416201/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2325 BracketBatch0145.bracket2326
  (330431878067267283324646581031946079088849/20000000000000000000000000000000000000000) (3430446376974419026035209421542558416201/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2325
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2326
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (82876666580686951824774427116949390941017/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (82876666580686951824774427116949390941017/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (41710589956480763630771555751817888308861/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41710589956480763630771555751817888308861/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (166297846493648479086317538620585167558739/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (166297846493648479086317538620585167558739/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2326 BracketBatch0145.bracket2327 (166297846493648479086317538620585167558739/10000000000000000000000000000000000000000) (3439161590513448052007185255932719677507/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2326 BracketBatch0145.bracket2327
  (166297846493648479086317538620585167558739/10000000000000000000000000000000000000000) (3439161590513448052007185255932719677507/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2326
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2327
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (166842359825923054523086223007271553235441/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (166842359825923054523086223007271553235441/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (167945909665330261839245658126054242526379/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (167945909665330261839245658126054242526379/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (16739413474562665818116594056666289788091/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16739413474562665818116594056666289788091/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0290.rows ScalarLogs0290.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2327 BracketBatch0145.bracket2328 (16739413474562665818116594056666289788091/1000000000000000000000000000000000000000) (3447932864240748273455475505100504182429/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2327 BracketBatch0145.bracket2328
  (16739413474562665818116594056666289788091/1000000000000000000000000000000000000000) (3447932864240748273455475505100504182429/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2327
