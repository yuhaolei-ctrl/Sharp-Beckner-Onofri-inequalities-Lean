module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0385
public import BecknerOnofri.EntropyScalarCertificate.Bessel0386
public import BecknerOnofri.EntropyScalarCertificate.Bessel0681
public import BecknerOnofri.EntropyScalarCertificate.Bessel0682
public import BecknerOnofri.EntropyScalarCertificate.Brackets0154
public import BecknerOnofri.EntropyScalarCertificate.Logs0308
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2464
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (151599111893186794956959109636149624705723/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (151599111893186794956959109636149624705723/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (303929255767343396243404126323604026151269/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (303929255767343396243404126323604026151269/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (121425495910743397231464469119180655112543/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (121425495910743397231464469119180655112543/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2464 BracketBatch0154.bracket2465 (121425495910743397231464469119180655112543/4000000000000000000000000000000000000000) (862638732384370510828986489143639159237/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2464 BracketBatch0154.bracket2465
  (121425495910743397231464469119180655112543/4000000000000000000000000000000000000000) (862638732384370510828986489143639159237/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2464
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2465
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (151964627883671698121702063161802013075633/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (151964627883671698121702063161802013075633/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (487462138626089716911275574506802478209/16000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (487462138626089716911275574506802478209/16000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (608593092408649469312951360390355575031891/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (608593092408649469312951360390355575031891/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2465 BracketBatch0154.bracket2466 (608593092408649469312951360390355575031891/20000000000000000000000000000000000000000) (1079169863361187558472583604740905622709/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2465 BracketBatch0154.bracket2466
  (608593092408649469312951360390355575031891/20000000000000000000000000000000000000000) (1079169863361187558472583604740905622709/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2465
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2466
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (152331918320653036534773617033375774440311/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (152331918320653036534773617033375774440311/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (305401992312558942873265695303816644457909/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (305401992312558942873265695303816644457909/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (610065828953865015942812929370568193338531/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (610065828953865015942812929370568193338531/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2466 BracketBatch0154.bracket2467 (610065828953865015942812929370568193338531/20000000000000000000000000000000000000000) (17280696688488401334753749212473390259/40000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2466 BracketBatch0154.bracket2467
  (610065828953865015942812929370568193338531/20000000000000000000000000000000000000000) (17280696688488401334753749212473390259/40000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2466
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2467
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (152700996156279471436632847651908322228953/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (152700996156279471436632847651908322228953/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (306143748938124190123324969264735558262509/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (306143748938124190123324969264735558262509/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (122309148250136626599318132913710440544083/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (122309148250136626599318132913710440544083/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2467 BracketBatch0154.bracket2468 (122309148250136626599318132913710440544083/4000000000000000000000000000000000000000) (135114933159557657734818560528005641769/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2467 BracketBatch0154.bracket2468
  (122309148250136626599318132913710440544083/4000000000000000000000000000000000000000) (135114933159557657734818560528005641769/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2467
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2468
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (153071874469062095061662484632367779131253/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (153071874469062095061662484632367779131253/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (153444566465419203630439168483040418094369/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (153444566465419203630439168483040418094369/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (153258220467240649346050826557704098612811/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (153258220467240649346050826557704098612811/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2468 BracketBatch0154.bracket2469 (153258220467240649346050826557704098612811/5000000000000000000000000000000000000000) (865438112770519091162215058212819462109/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2468 BracketBatch0154.bracket2469
  (153258220467240649346050826557704098612811/5000000000000000000000000000000000000000) (865438112770519091162215058212819462109/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2468
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2469
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (61377826586167681452175667393216167237747/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (61377826586167681452175667393216167237747/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (15381908548124378759189233201966725257057/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15381908548124378759189233201966725257057/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (4916218431146607859557304008043322730639/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4916218431146607859557304008043322730639/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2469 BracketBatch0154.bracket2470 (4916218431146607859557304008043322730639/160000000000000000000000000000000000000) (4330712324126432642612422889420770741211/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2469 BracketBatch0154.bracket2470
  (4916218431146607859557304008043322730639/160000000000000000000000000000000000000) (4330712324126432642612422889420770741211/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2469
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2470
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (307638170962487575183784664039334505141137/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (307638170962487575183784664039334505141137/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (61678177993397651931889300661659675794641/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (61678177993397651931889300661659675794641/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (308014530464737917421615583673816442057171/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (308014530464737917421615583673816442057171/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2470 BracketBatch0154.bracket2471 (308014530464737917421615583673816442057171/10000000000000000000000000000000000000000) (1083560796500435018971459542176832310433/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2470 BracketBatch0154.bracket2471
  (308014530464737917421615583673816442057171/10000000000000000000000000000000000000000) (1083560796500435018971459542176832310433/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2470
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2471
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (154195444983494129829723251654149189486601/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (154195444983494129829723251654149189486601/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (154573658571807910246261165364636412677499/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (154573658571807910246261165364636412677499/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0681.rows BesselBatch0681.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (3087691035553020400759844170187856021641/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3087691035553020400759844170187856021641/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0308.rows ScalarLogs0308.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2471 BracketBatch0154.bracket2472 (3087691035553020400759844170187856021641/100000000000000000000000000000000000000) (867556638773213530538154434392276063997/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2471 BracketBatch0154.bracket2472
  (3087691035553020400759844170187856021641/100000000000000000000000000000000000000) (867556638773213530538154434392276063997/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2471
