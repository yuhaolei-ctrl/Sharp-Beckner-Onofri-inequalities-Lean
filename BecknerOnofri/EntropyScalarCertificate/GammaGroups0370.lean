module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0462
public import BecknerOnofri.EntropyScalarCertificate.Bessel0463
public import BecknerOnofri.EntropyScalarCertificate.Bessel0720
public import BecknerOnofri.EntropyScalarCertificate.Brackets0185
public import BecknerOnofri.EntropyScalarCertificate.Logs0370
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2960
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1359949118152947720145903820503486693382571/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1359949118152947720145903820503486693382571/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1363651276680500442802647724385965353405371/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1363651276680500442802647724385965353405371/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1361800197416724081474275772444726023393971/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1361800197416724081474275772444726023393971/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2960 BracketBatch0185.bracket2961 (1361800197416724081474275772444726023393971/10000000000000000000000000000000000000000) (6586749033698365978186434535859232629909/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2960 BracketBatch0185.bracket2961
  (1361800197416724081474275772444726023393971/10000000000000000000000000000000000000000) (6586749033698365978186434535859232629909/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2960
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2961
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (170456409585062555350330965548245669175671/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (170456409585062555350330965548245669175671/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (341843416408616235426195568135745061524843/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (341843416408616235426195568135745061524843/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (136551247115748269225371499846447279975237/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (136551247115748269225371499846447279975237/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2961 BracketBatch0185.bracket2962 (136551247115748269225371499846447279975237/1000000000000000000000000000000000000000) (823865751756472704987887240865154909669/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2961 BracketBatch0185.bracket2962
  (136551247115748269225371499846447279975237/1000000000000000000000000000000000000000) (823865751756472704987887240865154909669/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2961
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2962
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1367373665634464941704782272542980246099369/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1367373665634464941704782272542980246099369/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (685558225646158297047405759893787442561669/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (685558225646158297047405759893787442561669/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (2738490116926781535799593792330555131222707/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2738490116926781535799593792330555131222707/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2962 BracketBatch0185.bracket2963 (2738490116926781535799593792330555131222707/20000000000000000000000000000000000000000) (1319022818165897509193863902997762881661/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2962 BracketBatch0185.bracket2963
  (2738490116926781535799593792330555131222707/20000000000000000000000000000000000000000) (1319022818165897509193863902997762881661/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2962
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2963
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (274223290258463318818962303957514977024667/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (274223290258463318818962303957514977024667/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (343719950439688945377594674565422979440077/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (343719950439688945377594674565422979440077/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (2745996253051072375605190218049266802883643/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2745996253051072375605190218049266802883643/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2963 BracketBatch0185.bracket2964 (2745996253051072375605190218049266802883643/20000000000000000000000000000000000000000) (3299656659207228656667071532891090585347/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2963 BracketBatch0185.bracket2964
  (2745996253051072375605190218049266802883643/20000000000000000000000000000000000000000) (3299656659207228656667071532891090585347/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2963
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2964
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (274975960351751156302075739652338383552061/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (274975960351751156302075739652338383552061/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (172332985873859534784145133291786684616587/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (172332985873859534784145133291786684616587/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (2753543688749632059783539764595985394693001/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2753543688749632059783539764595985394693001/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2964 BracketBatch0185.bracket2965 (2753543688749632059783539764595985394693001/20000000000000000000000000000000000000000) (6603523751549926342280828904804162199069/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2964 BracketBatch0185.bracket2965
  (2753543688749632059783539764595985394693001/20000000000000000000000000000000000000000) (6603523751549926342280828904804162199069/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2964
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2965
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1378663886990876278273161066334293476932693/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1378663886990876278273161066334293476932693/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1382468878823750795588077935351108272208239/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1382468878823750795588077935351108272208239/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (690283191453656768465309750421350437285233/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (690283191453656768465309750421350437285233/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2965 BracketBatch0185.bracket2966 (690283191453656768465309750421350437285233/5000000000000000000000000000000000000000) (6607745445341931028687695433308417061681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2965 BracketBatch0185.bracket2966
  (690283191453656768465309750421350437285233/5000000000000000000000000000000000000000) (6607745445341931028687695433308417061681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2965
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2966
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (345617219705937698897019483837777068052059/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (345617219705937698897019483837777068052059/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (693147475498220885071381272636877065639309/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (693147475498220885071381272636877065639309/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (1384381914910096282865420240312431201743427/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1384381914910096282865420240312431201743427/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2966 BracketBatch0185.bracket2967 (1384381914910096282865420240312431201743427/10000000000000000000000000000000000000000) (3305989227630927885422880296593485338527/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2966 BracketBatch0185.bracket2967
  (1384381914910096282865420240312431201743427/10000000000000000000000000000000000000000) (3305989227630927885422880296593485338527/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2966
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2967
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (277258990199288354028552509054750826255723/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (277258990199288354028552509054750826255723/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (347535569794611416462589618789483747660131/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (347535569794611416462589618789483747660131/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (2776437230174887435993121020431689121919139/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2776437230174887435993121020431689121919139/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0370.rows ScalarLogs0370.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2967 BracketBatch0185.bracket2968 (2776437230174887435993121020431689121919139/20000000000000000000000000000000000000000) (827027854643623412817534541544530890593/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2967 BracketBatch0185.bracket2968
  (2776437230174887435993121020431689121919139/20000000000000000000000000000000000000000) (827027854643623412817534541544530890593/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2967
