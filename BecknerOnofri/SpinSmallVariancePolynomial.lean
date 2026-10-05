import BecknerOnofri.SpinSmallGradientFactor

/-! Exact polynomial certificate for the variance. The coefficient data is
checked against the defining probability law and gradient by the ring tactic;
its numerical origin supplies no trusted premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def smallVarianceCoefficientQ (n : Fin 23) : ℚ := ![
    (33:ℚ)/128,
    (14156527:ℚ)/34012224,
    (1018995373:ℚ)/1289945088,
    (108390678763308073:ℚ)/88573500000000000,
    (310085410635700007:ℚ)/212576400000000000,
    (247902789858215198242180667:ℚ)/217950444781826400000000000,
    (32967081517373389442846009:ℚ)/1195613868517447680000000000,
    (-299409619282738476419663279064343:ℚ)/178705752159032131642560000000000,
    (-2116031756358023079294816886860577:ℚ)/661873156144563450528000000000000,
    (-73011497335737281068001824730703906591391489:ℚ)/20772414950339872368497776303586880000000000,
    (-610453231683141244671308294644693168382128757:ℚ)/271929795713540147369425435246955520000000000,
    (-66042160097492733641183:ℚ)/268631151142024925100000,
    (46348022331255451969087890121427:ℚ)/39982388958101134789571250000000,
    (60200026106045248289684346395429:ℚ)/39150109290969330192000000000000,
    (4776617145036055297267537:ℚ)/3666183073978289356800000,
    (2106998951083931715703643:ℚ)/2477467853569152926212500,
    (119250539790265044725224667:ℚ)/267566528185468516030950000,
    (394718116549864326974521:ℚ)/2097806782137845625000000,
    (54587831433260715450203:ℚ)/866589682971375000000000,
    (2538976362706390120832:ℚ)/157010776911250779515625,
    (35726590802904256:ℚ)/11916220242862546875,
    (112353116:ℚ)/313826716467,
    (11:ℚ)/531441] n

theorem small_variance_polynomial (t : ℝ) :
    (∑ j : Count,productProbability t j*(smallGradientFactor t j)^2)=
      ∑ n : Fin 23,(smallVarianceCoefficientQ n:ℝ)*t^(2*n.val) := by
  norm_num [productProbability,reference,referenceQ,smallGradientFactor,weight,weightQ,
    moment,momentQ,meanCoordinate,meanCoordinateQ,smallVarianceCoefficientQ,
    Fin.sum_univ_succ,Finset.sum_range_succ,Nat.choose]
  ring

theorem small_variance_coefficient_bound :
    (∑ n : Fin 23,max (smallVarianceCoefficientQ n) 0*(1/16:ℚ)^(2*n.val))≤13/50 := by
  decide +kernel

#print axioms small_variance_polynomial
end BecknerOnofri.HighDim.Spin
