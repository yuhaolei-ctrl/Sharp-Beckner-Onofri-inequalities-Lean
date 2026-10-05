module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0486
public import BecknerOnofri.EntropyScalarCertificate.Bessel0487
public import BecknerOnofri.EntropyScalarCertificate.Bessel0732
public import BecknerOnofri.EntropyScalarCertificate.Brackets0194
public import BecknerOnofri.EntropyScalarCertificate.Brackets0195
public import BecknerOnofri.EntropyScalarCertificate.Logs0389
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3112
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (36188544457879376611785200059804138287761/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (36188544457879376611785200059804138287761/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1163416708206245241724817901379366062597449/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1163416708206245241724817901379366062597449/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (2321450130858385293301944303293098487805801/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2321450130858385293301944303293098487805801/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3112 BracketBatch0194.bracket3113 (2321450130858385293301944303293098487805801/10000000000000000000000000000000000000000) (3694574487487479365750559484231197282383/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3112 BracketBatch0194.bracket3113
  (2321450130858385293301944303293098487805801/10000000000000000000000000000000000000000) (3694574487487479365750559484231197282383/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3112
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3113
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (465366683282498096689927160551746425038979/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (465366683282498096689927160551746425038979/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1168850304884459791558142822536213083645631/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1168850304884459791558142822536213083645631/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (4664534026181410066565921447831158292486157/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4664534026181410066565921447831158292486157/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3113 BracketBatch0194.bracket3114 (4664534026181410066565921447831158292486157/20000000000000000000000000000000000000000) (115560542348845301142916677525729863573/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3113 BracketBatch0194.bracket3114
  (4664534026181410066565921447831158292486157/20000000000000000000000000000000000000000) (115560542348845301142916677525729863573/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3113
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3114
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (2337700609768919583116285645072426167291259/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2337700609768919583116285645072426167291259/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1174334921294163845966422418872562915064669/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1174334921294163845966422418872562915064669/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (4686370452357247275049130482817551997420597/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4686370452357247275049130482817551997420597/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3114 BracketBatch0194.bracket3115 (4686370452357247275049130482817551997420597/20000000000000000000000000000000000000000) (7402624070535560064900550136756004755439/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3114 BracketBatch0194.bracket3115
  (4686370452357247275049130482817551997420597/20000000000000000000000000000000000000000) (7402624070535560064900550136756004755439/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3114
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3115
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (469733968517665538386568967549025166025867/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (469733968517665538386568967549025166025867/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (471948511765075247494597049719882177072807/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (471948511765075247494597049719882177072807/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (470841240141370392940583008634453671549337/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (470841240141370392940583008634453671549337/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3115 BracketBatch0194.bracket3116 (470841240141370392940583008634453671549337/2000000000000000000000000000000000000000) (370469856228720974109512003475036067521/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3115 BracketBatch0194.bracket3116
  (470841240141370392940583008634453671549337/2000000000000000000000000000000000000000) (370469856228720974109512003475036067521/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3115
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3116
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (36870977481646503710515394509365795083813/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (36870977481646503710515394509365795083813/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (2370920229808274731498623619149774549738673/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2370920229808274731498623619149774549738673/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (946132557726730193794321773549837087020541/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (946132557726730193794321773549837087020541/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3116 BracketBatch0194.bracket3117 (946132557726730193794321773549837087020541/4000000000000000000000000000000000000000) (7416193938836974209357727259800564168491/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3116 BracketBatch0194.bracket3117
  (946132557726730193794321773549837087020541/4000000000000000000000000000000000000000) (7416193938836974209357727259800564168491/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3116
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3117
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (237092022980827473149862361914977454973867/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (237092022980827473149862361914977454973867/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (476440870978106382964302933886344819355131/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (476440870978106382964302933886344819355131/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (190124983387952265852805531543259945860573/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (190124983387952265852805531543259945860573/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3117 BracketBatch0194.bracket3118 (190124983387952265852805531543259945860573/800000000000000000000000000000000000000) (3711507288495963595150956959211241969071/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3117 BracketBatch0194.bracket3118
  (190124983387952265852805531543259945860573/800000000000000000000000000000000000000) (3711507288495963595150956959211241969071/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3117
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3118
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (595551088722632978705378667357931024193913/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (595551088722632978705378667357931024193913/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2393596462121417461347473675883758313856523/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2393596462121417461347473675883758313856523/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (191032032680477975046759533812619296425287/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (191032032680477975046759533812619296425287/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3118 BracketBatch0194.bracket3119 (191032032680477975046759533812619296425287/800000000000000000000000000000000000000) (7429859099826722002636913773526258504627/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3118 BracketBatch0194.bracket3119
  (191032032680477975046759533812619296425287/800000000000000000000000000000000000000) (7429859099826722002636913773526258504627/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3118
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3119
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (59839911553035436533686841897093957846413/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (59839911553035436533686841897093957846413/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2405098108935763923583413168008437568302131/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2405098108935763923583413168008437568302131/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (4798694571057181384930886843892195882158651/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4798694571057181384930886843892195882158651/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0389.rows ScalarLogs0389.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3119 BracketBatch0195.bracket3120 (4798694571057181384930886843892195882158651/20000000000000000000000000000000000000000) (7436727565084700631333482621765145162277/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3119 BracketBatch0195.bracket3120
  (4798694571057181384930886843892195882158651/20000000000000000000000000000000000000000) (7436727565084700631333482621765145162277/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3119
