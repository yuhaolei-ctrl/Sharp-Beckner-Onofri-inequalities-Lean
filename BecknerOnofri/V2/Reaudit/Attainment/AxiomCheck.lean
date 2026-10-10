module

public import BecknerOnofri.V2.Reaudit.Attainment.Main
public import BecknerOnofri.V2.Reaudit.Attainment.AdamsInput
public import BecknerOnofri.V2.Reaudit.Attainment.Fourier
public import BecknerOnofri.V2.Reaudit.Attainment.Rellich
public import BecknerOnofri.V2.Reaudit.Attainment.Vitali
public import BecknerOnofri.V2.Reaudit.Attainment.SobolevSmooth
public import BecknerOnofri.V2.Reaudit.Attainment.Pairing
public import BecknerOnofri.V2.Reaudit.Attainment.PotentialFourier
public import BecknerOnofri.V2.Reaudit.Attainment.GapIdentities

/-! `#print axioms` for every public theorem of package `Attainment`. -/

open BecknerOnofri.V2.Reaudit.Attainment

#print axioms criticalAdamsAboveThreshold_unconditional
#print axioms criticalAdamsAboveThreshold_of_input
#print axioms exists_L2_ae_limit
#print axioms unifIntegrable_of_sq_bound
#print axioms tendsto_integral_of_ae_of_sq_bound
#print axioms coercivity
#print axioms exists_coefficient_maximizer
#print axioms ae_eq_zero_of_potentialEnergy_eq_zero
#print axioms smooth_of_inSobolev_multiples
#print axioms coefficientValue_gap
#print axioms densityValue_gap
#print axioms coefficientMaximizer_iff
#print axioms densityMinimizer_iff
#print axioms euler_lagrange_of_maximizer
#print axioms maximizer_regularity
#print axioms densityMinimizer_regularity
#print axioms kirkwoodMonroe_of_maximizer
#print axioms subcritical_attainment_of_adams
#print axioms subcritical_attainment_of_criticalAdamsInput
#print axioms subcritical_attainment
#print axioms attained_extremizers_regular
#print axioms exists_smooth_positive_minimizer
#print axioms integrable_exp_mul_abs
#print axioms tail_bound
#print axioms tendsto_integral_exp_tail
#print axioms abs_integral_sub_headPart_le
#print axioms abs_integral_sub_le_of_bdd
#print axioms tendsto_integral_heat
#print axioms summable_norm_pairing
#print axioms pairing_identification_of_measurable
#print axioms pairing_identification
#print axioms pairing_identification_nonzero
#print axioms fourierCoeff_densityPotential
#print axioms weighted_sub_sq
#print axioms fourierCoeff_densityPotential_eq
#print axioms square_completion
#print axioms gibbs_entropy_formula
#print axioms relativeEntropy_gibbs_formula
#print axioms coefficientValue_gap_written
#print axioms densityValue_gap_written
