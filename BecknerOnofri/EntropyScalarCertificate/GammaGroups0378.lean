module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0472
public import BecknerOnofri.EntropyScalarCertificate.Bessel0473
public import BecknerOnofri.EntropyScalarCertificate.Bessel0725
public import BecknerOnofri.EntropyScalarCertificate.Brackets0189
public import BecknerOnofri.EntropyScalarCertificate.Logs0378
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3024
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (205748712874579000448357705934713490639397/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (205748712874579000448357705934713490639397/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1651417867946281059224675382431069389830793/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1651417867946281059224675382431069389830793/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (3297407570942913062811537029908777314945969/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3297407570942913062811537029908777314945969/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3024 BracketBatch0189.bracket3025 (3297407570942913062811537029908777314945969/20000000000000000000000000000000000000000) (3439480198325011107337017428425000253899/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3024 BracketBatch0189.bracket3025
  (3297407570942913062811537029908777314945969/20000000000000000000000000000000000000000) (3439480198325011107337017428425000253899/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3024
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3025
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (165141786794628105922467538243106938983079/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (165141786794628105922467538243106938983079/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (331376396214195800207581363161461484282003/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (331376396214195800207581363161461484282003/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (661659969803452012052516439647675362248161/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (661659969803452012052516439647675362248161/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3025 BracketBatch0189.bracket3026 (661659969803452012052516439647675362248161/4000000000000000000000000000000000000000) (6883973811544870047990635325829258032449/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3025 BracketBatch0189.bracket3026
  (661659969803452012052516439647675362248161/4000000000000000000000000000000000000000) (6883973811544870047990635325829258032449/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3025
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3026
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (414220495267744750259476703951826855352503/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (414220495267744750259476703951826855352503/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1662382400658182398777378082059549045178313/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1662382400658182398777378082059549045178313/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (132770575269166455992611395914674258663533/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (132770575269166455992611395914674258663533/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3026 BracketBatch0189.bracket3027 (132770575269166455992611395914674258663533/800000000000000000000000000000000000000) (6889002634246473735025749851577638552543/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3026 BracketBatch0189.bracket3027
  (132770575269166455992611395914674258663533/800000000000000000000000000000000000000) (6889002634246473735025749851577638552543/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3026
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3027
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (166238240065818239877737808205954904517831/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (166238240065818239877737808205954904517831/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (10424496811078211937316677187270821582267/62500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10424496811078211937316677187270821582267/62500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (333030189043069630874804643202288049834103/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (333030189043069630874804643202288049834103/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3027 BracketBatch0189.bracket3028 (333030189043069630874804643202288049834103/2000000000000000000000000000000000000000) (6894046947056644498480306694303863598793/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3027 BracketBatch0189.bracket3028
  (333030189043069630874804643202288049834103/2000000000000000000000000000000000000000) (6894046947056644498480306694303863598793/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3027
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3028
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1667919489772513909970668349963331453162717/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1667919489772513909970668349963331453162717/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1673493616335648000453475030829819303244251/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1673493616335648000453475030829819303244251/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (417676638263520238803017922599143844550871/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (417676638263520238803017922599143844550871/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3028 BracketBatch0189.bracket3029 (417676638263520238803017922599143844550871/2500000000000000000000000000000000000000) (1379821366553960616187267908286453398313/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3028 BracketBatch0189.bracket3029
  (417676638263520238803017922599143844550871/2500000000000000000000000000000000000000) (1379821366553960616187267908286453398313/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3028
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3029
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (209186702041956000056684378853727412905531/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (209186702041956000056684378853727412905531/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (335821030641561020445421956080062215056059/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (335821030641561020445421956080062215056059/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (3352598769543453102680584811230130378524543/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3352598769543453102680584811230130378524543/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3029 BracketBatch0189.bracket3030 (3352598769543453102680584811230130378524543/20000000000000000000000000000000000000000) (690418237467304022963510692513677693701/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3029 BracketBatch0189.bracket3030
  (3352598769543453102680584811230130378524543/20000000000000000000000000000000000000000) (690418237467304022963510692513677693701/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3029
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3030
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (419776288301951275556777445100077768820073/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (419776288301951275556777445100077768820073/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1684754478270892117939378262622176238945161/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1684754478270892117939378262622176238945161/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (3363859631478697220166488043022487314225453/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3363859631478697220166488043022487314225453/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3030 BracketBatch0189.bracket3031 (3363859631478697220166488043022487314225453/20000000000000000000000000000000000000000) (1381854731309205323452094939621590971309/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3030 BracketBatch0189.bracket3031
  (3363859631478697220166488043022487314225453/20000000000000000000000000000000000000000) (1381854731309205323452094939621590971309/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3030
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3031
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (842377239135446058969689131311088119472579/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (842377239135446058969689131311088119472579/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (422610493628332051465423491742808514465009/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (422610493628332051465423491742808514465009/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1687598226392110161900536114796705148402597/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1687598226392110161900536114796705148402597/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0378.rows ScalarLogs0378.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3031 BracketBatch0189.bracket3032 (1687598226392110161900536114796705148402597/10000000000000000000000000000000000000000) (864297595332595638639487834277596670523/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3031 BracketBatch0189.bracket3032
  (1687598226392110161900536114796705148402597/10000000000000000000000000000000000000000) (864297595332595638639487834277596670523/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3031
