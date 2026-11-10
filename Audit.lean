import Erdos345

-- The audit deliberately inspects generated helpers at this exact pinned revision.
-- No mathematical proof depends on these unstable names.
set_option linter.auxLemma false

#print Erdos345.IntendedStatement
#check @Erdos345.intended_of_late_powerThreshold_inversions
#check @Erdos345.primePhaseBin_dvd_alternative
#check @Erdos345.two_distance_le_abs_sine
#check @Erdos345.sum_prime_logs_of_phaseBin
#check @Erdos345.sum_prime_weights_of_phaseBin
#check @Erdos345.sum_abs_prime_sine_harmonic
#check @Erdos345.sum_abs_prime_sine_bound
#check @Erdos345.belovSineTotal_pos_upto_eight
#check @Erdos345.belovSinePrefix_lower
#check @Erdos345.prime_theta_half_large
#check @Erdos345.odd_prime_mass_lower
#check @Erdos345.exists_belov_balanced_level
#check @Erdos345.belovSineTotal_nonneg_512
#check @Erdos345.belov_konyagin_input_proved
#check @Erdos345.good_degrees_threshold_upper_unconditional
#check @Erdos345.intended_of_fan_pollack
#check @Erdos345.intended_of_many_shifted_primes
#check @Erdos345.shifted_prime_spike_of_pair_count
#check @Erdos345.gcd_class_card_lower
#check @Erdos345.shifted_prime_spike_of_progression_counts
#check @Erdos345.prime_subset_products_card
#check @Erdos345.prime_subset_products_valid
#check @Erdos345.prime_progression_card_lower
#check @Erdos345.eventually_prime_progression_lower
#check @Erdos345.shifted_prime_spike_of_many_progressions
#check @Erdos345.prime_subset_products_twenty_four_lower
#check @Erdos345.shifted_prime_abundance_of_bombieri_vinogradov
#check @Erdos345.intended_of_bombieri_vinogradov
#check @Erdos345.shifted_prime_abundance_proved
#check @Erdos345.erdos_345
#check @OAI.LargePrimeGaps.siegelWalfisz
#check @OAI.LargePrimeGaps.bombieriVinogradov
#check @Erdos345.exists_least_powerThreshold
#check @Erdos345.leastPowerThreshold_spec
#check @Erdos345.hasGlobalIntegerPolynomialReduction_iff_dvd
#check @Erdos345.exists_good_reduction_degree
#check @Erdos345.centerEnergy_gt_of_cubic_bound
#check @Erdos345.log_modulus_le_of_contraction
#check @Erdos345.normalizedMoment_dvd_factorial
#check @Erdos345.rootSlots_mul_le_mass
#check @Erdos345.flatPolynomial_top_moment
#check @Erdos345.exists_flat_power_recurrence
#check @Erdos345.power_annihilator_characteristic_dvd
#check @Erdos345.remove_nonprimary_cyclotomic_factors
#check @Erdos345.rootOneWindow_real_le
#check @Erdos345.cyclotomic_dilation_preserves_recurrence
#check @Erdos345.cyclotomic_recurrence_expansion
#check @Erdos345.power_annihilator_dilation_product_dvd
#check @Erdos345.exists_odd_dilation_generator
#check @Erdos345.local_scaling_multiplicity_bound
#check @Erdos345.exists_integral_minimalAnnihilator
#check @Erdos345.minimalAnnihilator_map
#check @Erdos345.exists_minimal_flat_slot_bound
#check @Erdos345.minimal_cyclotomic_expansion_top_ne_zero
#check @Erdos345.filtered_top_isIntegral
#check @Erdos345.filtered_top_ne_zero
#check @Erdos345.cofactorWitness_eq_top
#check @Erdos345.minimal_cyclotomic_witness_norm_lower
#check @Erdos345.primePower_general_power_norm_product
#check @Erdos345.nonvanishingPrimeWeight_le_mass
#check @Erdos345.regularizedCyclotomicNorm_mono
#check @Erdos345.exists_large_primePower_top_coefficient
#check @Erdos345.exists_large_rootOne_top_coefficient
#check @Erdos345.exists_large_scaled_rootOne_top_coefficient
#check @Erdos345.discrete_energy_half_lower_of_gram
#check @Erdos345.cyclotomic_root_separation
#check @Erdos345.cyclotomic_modulated_offDiagonal_le
#check @Erdos345.exists_shiftedChebyshev_expansion
#check @Erdos345.shiftedChebyshevSeries_continuous_energy_lower
#check @Erdos345.uniform_sampling_error_le
#check @Erdos345.shiftedChebyshevSeries_sampled_half_energy_lower
#check @Erdos345.cyclotomicChebyshev_energy_lower
#check @Erdos345.exists_scaled_chebyshev_expansion
#check @Erdos345.ordinary_cyclotomic_expansion_energy_lower
#check @Erdos345.minimal_integer_primePower_energy_lower
#check @Erdos345.minimalAnnihilator_translate
#check @Erdos345.minimal_integer_primePower_multiplicity_bound
#check @Erdos345.minimal_integer_rootOne_multiplicity_bound
#check @Erdos345.rational_polynomial_perturbation_components
#check @Erdos345.rational_error_primePower_multiplicity_bound
#check @Erdos345.rational_error_rootOne_multiplicity_bound
#check @Erdos345.exists_flat_error_window_multiplicity_bounds
#check @Erdos345.exists_rational_phase_height_bounds
#check @Erdos345.rational_error_annihilator_mod_power
#check @Erdos345.primary_local_scaling_bound
#check @Erdos345.large_prime_power_reduction
#check @Erdos345.primary_exponent_bound
#check @Erdos345.power_dvd_factorial_of_mul_le
#check @Erdos345.conductor_divisibility_of_heights
#check @Erdos345.rational_phase_window_reduction
#check @Erdos345.exists_rational_reduction_phase
#check @Erdos345.rational_phase_sineEnergy_eq_center
#check @Erdos345.exists_reduced_phase_recurrence
#check @Erdos345.windowHeightBudget_le_linear_degree
#check @Erdos345.exists_reduced_phase_long_window
#check @Erdos345.exists_exact_reduction_step
#check @Erdos345.power_modulus_one_of_small_heights
#check @Erdos345.centerEnergy_gt_of_flat_family
#check @Erdos345.exists_good_conductor_degree
#check @Erdos345.exists_good_degree_explicit_center_bound
#check @Erdos345.goodConductorEnvelope_le_logScale
#check @Erdos345.centerWindowExponent_le_logScale
#check @Erdos345.log_sufficientCenterWindow_le
#check @Erdos345.log_sufficientCenterPrefix_square_le
#check @Erdos345.exists_good_quasipolynomial_center_bound
#check @Erdos345.unit_circle_radial_ratio
#check @Erdos345.radialFlatProduct_log_hasSum
#check @Erdos345.flatPolynomial_sup_norm_mass_bound
#check @Erdos345.coefficientL1_le_unit_bound
#check @Erdos345.flat_coefficient_norm_from_cosine
#check @Erdos345.exists_good_center_bound_from_cosine_existence
#check @Erdos345.eventually_quasipolynomialCenterPrefix_le_seventh_scale
#check @Erdos345.polynomial_of_vanishing_difference
#check @Erdos345.exists_flat_quotient_polynomial
#check @Erdos345.polynomialShiftAction_top
#check @Erdos345.polynomial_sample_energy_lower
#check @Erdos345.exists_inverse_error_polynomial
#check @Erdos345.flat_inverse_of_energy_le
#check @Erdos345.power_sineEnergy_perturbation
#check @Erdos345.rational_center_energy_gt
#check @Erdos345.flat_inverse_integer_center
#check @Erdos345.card_gridNear_le
#check @Erdos345.card_lowEnergyGrid_le
#check @Erdos345.finiteCosineMean_pow_le
#check @Erdos345.prefixEnergy_le_population_add_missing
#check @Erdos345.powerCollisionSum_le_flat_grid
#check @Erdos345.near_integer_implies_small_numerator
#check @Erdos345.card_nonzero_integerArcs_le
#check @Erdos345.powerCollisionSum_le_integer_inverse
#check @Erdos345.powerCollisionSum_lt_one_of_log_budgets
#check @Erdos345.stacked_naturalWindow_energy_lower
#check @Erdos345.powerWindow_length_lower
#check @Erdos345.powerWindow_phase
#check @Erdos345.powerWindows_energy_lower
#check @Erdos345.finiteSineEnergy_min_numerator
#check @Erdos345.middle_scale_energy_lower
#check @Erdos345.large_scale_energy_lower
#check @Erdos345.quarter_root_le_one_sub_inv
#check @Erdos345.unreserved_small_numerator_energy_lower
#check @Erdos345.unreserved_lowEnergyGrid_empty
#check @Erdos345.coarse_unreserved_frequency_bound
#check @Erdos345.unreserved_collision_le_exp_margin
#check @Erdos345.tendsto_logScale_pow_div
#check @Erdos345.eventually_monomial_exp_dominated
#check @Erdos345.flat_radius_perturbation_le_eight
#check @Erdos345.eventually_fourier_inverse_size
#check @Erdos345.eventually_fourier_parameter_conditions
#check @Erdos345.fourier_collision_margin
#check @Erdos345.collision_decay_of_parameters
#check @Erdos345.good_degrees_fourier_decay
#check @Erdos345.good_degrees_collision_small
#check @Erdos345.good_degrees_uniform_energy
#check @Erdos345.uniformMean_pi_prod
#check @Erdos345.labelGroup_disjoint
#check @Erdos345.mean_sampled_cosineSum_le
#check @Erdos345.cyclic_parseval
#check @Erdos345.residueSupport_large_of_collision_le_three
#check @Erdos345.bitSum_fourier_product
#check @Erdos345.powerBit_collision_eq
#check @Erdos345.representedResidues_large_of_cosineSum
#check @Erdos345.uniformMean_event_le
#check @Erdos345.finite_bad_event_selection
#check @Erdos345.good_degrees_label_support_small
#check @Erdos345.uniformMean_pi_two
#check @Erdos345.labelWeight_variance
#check @Erdos345.unreserved_power_sum_bound
#check @Erdos345.unreserved_span_variance_le
#check @Erdos345.mean_bad_row_le
#check @Erdos345.mean_large_span_le
#check @Erdos345.select_groups_with_support_and_span
#check @Erdos345.good_degrees_reserved_groups
#check @Erdos345.exists_disjoint_subsets_of_uniform_card
#check @Erdos345.reserved_good_allocation
#check @Erdos345.residue_endpoint_card_growth
#check @Erdos345.finitePowerSums_union_growth
#check @Erdos345.reserved_augmentation_card_lower
#check @Erdos345.reserved_augmentation_span_upper
#check @Erdos345.auxiliaryPair_no_proper_progression
#check @Erdos345.good_degrees_gcd_one_groups
#check @Erdos345.lev_parameters_large
#check @Erdos345.representedUpTo_of_group_sums
#check @Erdos345.lev_interval_covers_next_power
#check @Erdos345.good_degrees_interval_ready_groups
#check @Erdos345.dense_int_sumset_interval
#check @Erdos345.dense_nat_sumset_interval
#check @Erdos345.indexed_sumset_card_lower
#check @Erdos345.indexed_sumset_span
#check @Erdos345.naturalResidueImage_card_closed_interval
#check @Finset.add_kneser
#check @Finset.add_strict_kneser
#check @Erdos345.multiple_kneser
#check @Erdos345.sumset_residue_growth
#check @Erdos345.quotient_fiber_defect_bound
#check @Erdos345.quotient_sumset_fiber_bound_of_mem
#check @Erdos345.stabilizer_quotient_mem_image
#check @Erdos345.quotient_old_region_growth
#check @Erdos345.quotient_new_class_of_generating
#check @Erdos345.stabilized_sumset_fiber_bound
#check @Erdos345.periodic_sumset_lifting
#check @Erdos345.integer_sumset_growth_of_generating
#check @Erdos345.natural_residue_generates_of_no_progression
#check @Erdos345.lev_integer_growth
#check @Erdos345.lev_uniform_growth
#check @Erdos345.sorted_prefix_card_lower
#check @Erdos345.paired_span_min_bound
#check @Erdos345.sorted_prefix_density
#check @Erdos345.alternating_span_balance
#check @Erdos345.interval_of_dense_balanced_sumsets
#check @Erdos345.sorted_128_sumset_interval
#check @Erdos345.interval_for_128_sets
#check @Erdos345.sharp_interval_ratio
#check @Erdos345.good_degrees_represented_interval
#check @Erdos345.good_degrees_threshold_upper
#check @Erdos345.two_pow_prime_count_lt_threshold
#check @Erdos345.shifted_prime_log_threshold_lower
#check @Erdos345.log_threshold_envelope_le
#check @Erdos345.upper_envelope_lt_threshold_of_many_primes
#check @Erdos345.intended_of_cosine_and_shifted_prime_abundance
#check @Erdos345.eventually_power_lt_exp_div_log
#check @Erdos345.eventually_shifted_prime_requirement
#check @Erdos345.shifted_prime_abundance_of_fan_input
#check @Erdos345.BelovKonyaginInput
#check @Erdos345.FanPollackInput
#check @Erdos345.intended_of_published_analytic_inputs
#check @Erdos345.interpolate_cosine_mass
#check @Erdos345.exact_cosine_mass_of_interlacing
#check @Erdos345.countingProfileWeight_interlace
#check @Erdos345.exact_mass_from_counting_profile
#check @Erdos345.belov_input_of_profile_data
#check @Erdos345.oddSineSum_identity
#check @Erdos345.oddSineSum_abs_le_inv_sin
#check @Erdos345.oddSineSum_nonneg
#check @Erdos345.oddSineSum_small_angle_lower
#check @Erdos345.scaledSineBlock_small_lower
#check @Erdos345.scaledSineBlock_abs_linear
#check @Erdos345.summable_succ_pow_div_two
#check @Erdos345.dyadicSineLevel_abs_bound
#check @Erdos345.summable_dyadicSineLevels
#check @Erdos345.tsum_ge_initial_sum_of_nonnegative_tail
#check @Erdos345.dyadicSineTotal_pos_small
#check @Erdos345.summable_belovSineLevels
#check @Erdos345.belovSineTotal_pos_small
#check @Erdos345.belovSineLevels_nonnegative_tail
#check @Erdos345.belovSineTotal_ge_prefix
#check @Erdos345.summable_dyadicFrequency
#check @Erdos345.summable_abs_sine_dyadicFrequency
#check @Erdos345.tsum_sine_dyadicFrequency
#check @Erdos345.one_le_belovDenominator
#check @Erdos345.summable_inv_belovDenominator
#check @Erdos345.tsum_belovSineFamily
#check @Erdos345.finite_reciprocal_sublevel
#check @Erdos345.belovCountingProfile_monotone
#check @Erdos345.belovCountingProfile_le_majorant
#check @Erdos345.belovProfileMajorant_double
#check @Erdos345.sine_le_truncatedCosine
#check @Erdos345.tsum_belovFloorCosine
#check @Erdos345.profile_cosine_nonneg_of_sine_nonneg
#check @Erdos345.cosine_nonneg_of_half_period
#check @Erdos345.belov_profile_cosine_of_global_sine
#check @Erdos345.belov_input_of_concrete_sine_profile
#check @Erdos345.intended_of_concrete_sine_profile_and_fan
#check @Erdos345.primeCounting_le_five_mul_div_log
#check @Erdos345.belov_level_count_bound
#check @Erdos345.belov_level_reciprocal_numerator_bound
#check @Erdos345.hasSum_shift_three_fifth_div_two
#check @Erdos345.dyadic_fifth_shift_bound
#check @Erdos345.belovProfileMajorant_eq_levels
#check @Erdos345.belovProfile_split_bound
#check @Erdos345.belovProfileMajorant_log_bound
#check @Erdos345.belovProfile_budget_512
#check @Erdos345.belov_input_of_global_sine_512
#check @Erdos345.intended_of_global_sine_512_and_fan

#print axioms Erdos345.image_indexed_sumset
#print axioms Erdos345.indexed_sumset_card_add
#print axioms Erdos345.sum_of_input_fibers_subset
#print axioms Erdos345.sumset_fiber_card_bound
#print axioms Erdos345.sum_range_even_odd
#print axioms Erdos345.alternating_span_balance
#print axioms Erdos345.intended_of_cosine_and_shifted_prime_abundance
#print axioms Erdos345.reserved_augmentation_card_lower
#print axioms Erdos345.reserveGroupSize_lower
#print axioms Erdos345.selected_span_le_reserve_third
#print axioms Erdos345.reserved_augmentation_span_upper
#print axioms Erdos345.good_degrees_augmented_groups
#print axioms Erdos345.auxiliaryPair_subset
#print axioms Erdos345.auxiliaryPair_disjoint
#print axioms Erdos345.auxiliaryPair_powers_coprime
#print axioms Erdos345.self_power_mem_finitePowerSums
#print axioms Erdos345.auxiliaryPair_no_proper_progression
#print axioms Erdos345.reservedBases_auxiliary_disjoint
#print axioms Erdos345.auxiliaryPair_span_le
#print axioms Erdos345.belov_konyagin_input_proved
#print axioms Erdos345.good_degrees_threshold_upper_unconditional
#print axioms Erdos345.intended_of_fan_pollack
#print axioms Erdos345.intended_of_many_shifted_primes
#print axioms Erdos345.belovLevelPrimes_prime
#print axioms Erdos345.belovLevelPrimes_three_le
#print axioms Erdos345.belovSineLevel_nonneg_of_phase_le_six
#print axioms Erdos345.belovSineLevel_zero_ge_neg_three
#print axioms Erdos345.belovSineLevel_six_gt_argument
#print axioms Erdos345.belovSineTotal_pos_upto_eight
#print axioms Erdos345.belovLevelPrimes_subset
#print axioms Erdos345.belovLevelPrimes_zero_nonempty
#print axioms Erdos345.belovMultiplicity_zero
#print axioms Erdos345.belovMultiplicity_le
#print axioms Erdos345.summable_belovSineLevels
#print axioms Erdos345.belovSineTotal_pos_small
#print axioms Erdos345.belovSineLevels_nonnegative_tail
#print axioms Erdos345.belovSineTotal_ge_prefix
#print axioms Erdos345.belovSineLevel_small_lower
#print axioms Erdos345.belov_scale_512_le_multiplicity
#print axioms Erdos345.belovSineLevel_balanced_lower
#print axioms Erdos345.belovSineTotal_pos_large
#print axioms Erdos345.belovSineTotal_nonneg_512
#print axioms Erdos345.belovSineLevel_lower_log
#print axioms Erdos345.dyadic_log_envelope
#print axioms Erdos345.weighted_square_prefix
#print axioms Erdos345.weighted_square_triangle
#print axioms Erdos345.belovSinePrefix_lower
#print axioms Erdos345.belovSineTotal_lower_with_level
#print axioms Erdos345.belovMultiplicity_real_le
#print axioms Erdos345.belov_scale_log_lower
#print axioms Erdos345.belovMultiplicity_twice_le_log_scale
#print axioms Erdos345.belovMultiplicity_square_le_log_scale
#print axioms Erdos345.sum_belov_primes_mul_log
#print axioms Erdos345.belov_level_count_bound
#print axioms Erdos345.belov_level_reciprocal_numerator_bound
#print axioms Erdos345.belovProfileCut_ge_three
#print axioms Erdos345.belovProfileCut_power_bound
#print axioms Erdos345.belovProfileCut_log_bound
#print axioms Erdos345.belovProfile_cut_bound
#print axioms Erdos345.belovProfileMajorant_log_bound
#print axioms Erdos345.belovProfile_budget_512
#print axioms Erdos345.belov_input_of_global_sine_512
#print axioms Erdos345.intended_of_global_sine_512_and_fan
#print axioms Erdos345.summable_belovProfileAtoms
#print axioms Erdos345.belovProfileLevel_nonneg
#print axioms Erdos345.summable_belovProfileLevels
#print axioms Erdos345.belovProfileMajorant_eq_levels
#print axioms Erdos345.belovProfileLevel_le_count
#print axioms Erdos345.belovProfileLevel_le_reciprocal
#print axioms Erdos345.belov_input_of_profile_data
#print axioms Erdos345.belovProfileHead_bound
#print axioms Erdos345.belovProfileTail_bound
#print axioms Erdos345.belovProfile_split_bound
#print axioms Erdos345.belovProfile_linear_bound
#print axioms Erdos345.dyadicAtomFrequency_lt_multiplicity
#print axioms Erdos345.belovMultiplicity_le_two_pow
#print axioms Erdos345.belovFrequency_pos
#print axioms Erdos345.belovFrequency_le_one
#print axioms Erdos345.belovDenominator_pos
#print axioms Erdos345.one_le_belovDenominator
#print axioms Erdos345.belovDenominator_base
#print axioms Erdos345.inv_belovDenominator
#print axioms Erdos345.summable_belovFrequency
#print axioms Erdos345.summable_inv_belovDenominator
#print axioms Erdos345.summable_belovSineFamily
#print axioms Erdos345.tsum_belovSineFamily
#print axioms Erdos345.belovSineFamily_pos_small
#print axioms Erdos345.belovMultiplicity_pos
#print axioms Erdos345.belovMultiplicity_mono
#print axioms Erdos345.exists_belov_safe_level
#print axioms Erdos345.belovMultiplicity_four_ge_two
#print axioms Erdos345.exists_belov_balanced_level
#print axioms Erdos345.addChar_sum_product
#print axioms Erdos345.character_bitSum
#print axioms Erdos345.bitSum_fourier_product
#print axioms Erdos345.half_character_norm
#print axioms Erdos345.half_stdAddChar_norm
#print axioms Erdos345.sin_pi_mul_half_lower
#print axioms Erdos345.sin_pi_mul_lower
#print axioms Erdos345.sin_nat_fraction_sq_lower
#print axioms Erdos345.sin_nat_fraction_sq_mod
#print axioms Erdos345.centerTerm_nonneg
#print axioms Erdos345.centerTerm_residue_one
#print axioms Erdos345.centerEnergy_lower
#print axioms Erdos345.centerEnergy_gt_of_cubic_bound
#print axioms Erdos345.low_centerEnergy_forces_cubic_bound
#print axioms Erdos345.characteristic_eq_zero_of_unit_coordinate
#print axioms Erdos345.characteristic_dvd_of_congruence
#print axioms Erdos345.shiftedChebyshev_natDegree
#print axioms Erdos345.shiftedChebyshev_leadingCoeff
#print axioms Erdos345.shiftedChebyshev_ne_zero
#print axioms Erdos345.shiftedChebyshev_degree
#print axioms Erdos345.exists_shiftedChebyshev_expansion
#print axioms Erdos345.shiftedChebyshev_eval
#print axioms Erdos345.shiftedChebyshev_real_abs_le
#print axioms Erdos345.shiftedChebyshev_real_derivative_abs_le
#print axioms Erdos345.shiftedChebyshev_real_difference_le
#print axioms Erdos345.shiftedChebyshev_complex_eval
#print axioms Erdos345.shiftedChebyshev_complex_norm_le
#print axioms Erdos345.unitGrid_mem
#print axioms Erdos345.unitGrid_step_abs
#print axioms Erdos345.chebyshevPhase_norm
#print axioms Erdos345.chebyshev_sample_step_le
#print axioms Erdos345.chebyshevPhase_cross_bound
#print axioms Erdos345.chebyshev_sample_energy_mass_lower
#print axioms Erdos345.integral_sq_finite_sum
#print axioms Erdos345.integral_chebyshev_pair
#print axioms Erdos345.integral_chebyshev_realSeries_sq
#print axioms Erdos345.chebyshevSeries_norm_sq
#print axioms Erdos345.integral_chebyshevSeries_norm_sq
#print axioms Erdos345.cosineSeries_energy_lower
#print axioms Erdos345.chebyshevSeries_pointwise_sq_le
#print axioms Erdos345.chebyshevCoefficientMass_nonneg
#print axioms Erdos345.chebyshevCoefficientMass_sq_le
#print axioms Erdos345.shiftedChebyshevSeries_norm_le
#print axioms Erdos345.shiftedChebyshevSeries_difference_le
#print axioms Erdos345.norm_sq_difference_le
#print axioms Erdos345.shiftedChebyshevSeries_norm_sq_difference_le
#print axioms Erdos345.shiftedChebyshevSeries_sampling_error
#print axioms Erdos345.shiftedChebyshevSeries_sampled_energy_lower
#print axioms Erdos345.shiftedChebyshevSeries_sampled_half_energy_lower
#print axioms Erdos345.log_sixteen_ge_two
#print axioms Erdos345.coarseWindowScale_conditions
#print axioms Erdos345.coarseWindowFloor_gt
#print axioms Erdos345.coarseWindowRadius_budget
#print axioms Erdos345.cofactorWitness_eval
#print axioms Erdos345.componentFilter_mul_linear
#print axioms Erdos345.componentFilter_eq_div
#print axioms Erdos345.cofactorWitness_eq_top
#print axioms Erdos345.nat_mul_exp_le_exp
#print axioms Erdos345.powerCollisionSum_le_two_exp
#print axioms Erdos345.two_exp_neg_lt_one
#print axioms Erdos345.powerCollisionSum_lt_one_of_log_budgets
#print axioms Erdos345.sum_cosineMean_pow_split
#print axioms Erdos345.mem_nonzeroFrequencies
#print axioms Erdos345.card_nonzeroFrequencies_le
#print axioms Erdos345.powerCollisionSum_nonneg
#print axioms Erdos345.iteratedDifference_power_self
#print axioms Erdos345.exponentialPower_top_filter
#print axioms Erdos345.shiftAction_exponential
#print axioms Erdos345.shiftAction_annihilates_multiple
#print axioms Erdos345.complementFactor_monic
#print axioms Erdos345.componentFilter_monic
#print axioms Erdos345.componentFilter_dvd
#print axioms Erdos345.componentFilter_top
#print axioms Erdos345.componentFilter_other
#print axioms Erdos345.shifted_prime_abundance_proved
#print axioms Erdos345.erdos_345
#print axioms Erdos345.belov_profile_cosine_of_global_sine
#print axioms Erdos345.belov_input_of_concrete_sine_profile
#print axioms Erdos345.intended_of_concrete_sine_profile_and_fan
#print axioms Erdos345.conductor_divisibility_of_heights
#print axioms Erdos345.conductor_minimal_degree_bound
#print axioms Erdos345.rational_error_conductor_divisibility
#print axioms Erdos345.weighted_sum_square_le
#print axioms Erdos345.shifted_nonnegative_sum_le
#print axioms Erdos345.convolution_energy_le
#print axioms Erdos345.integer_nonzero_count_le_energy
#print axioms Erdos345.coefficientL1_nonneg
#print axioms Erdos345.shiftAction_error
#print axioms Erdos345.recurrence_residual_count_bound
#print axioms Erdos345.shiftAction_window_energy_le
#print axioms Erdos345.inverse_energy_from_flat_recurrence
#print axioms Erdos345.finiteSineEnergy_nonneg
#print axioms Erdos345.finiteSineEnergy_le_card
#print axioms Erdos345.finiteCosineMean_nonneg
#print axioms Erdos345.finiteCosineMean_eq_one_sub
#print axioms Erdos345.finiteCosineMean_le_one
#print axioms Erdos345.finiteCosineMean_pow_le
#print axioms Erdos345.finiteCosineMean_pow_le_of_energy
#print axioms Erdos345.sum_cosineMean_pow_le_of_energy
#print axioms Erdos345.weightMass_extend_of_support
#print axioms Erdos345.weightedSum_extend_of_support
#print axioms Erdos345.interlaced_weightMass_step
#print axioms Erdos345.weightMass_ge_length
#print axioms Erdos345.exact_cosine_mass_of_interlacing
#print axioms Erdos345.flatNormConstant_nonneg
#print axioms Erdos345.flat_coefficient_norm_from_cosine
#print axioms Erdos345.flat_coefficient_norm_below_degree
#print axioms Erdos345.radialFlatProduct_ne_zero
#print axioms Erdos345.radial_log_upper_of_cosine
#print axioms Erdos345.flatPolynomial_sup_norm_from_cosine
#print axioms Erdos345.flatPolynomial_sup_norm_mass_bound
#print axioms Erdos345.cosine_nonneg_of_half_period
#print axioms Erdos345.augmentFirstWeight_antitone
#print axioms Erdos345.augmentFirstWeight_mass
#print axioms Erdos345.augmentFirstWeight_evaluation
#print axioms Erdos345.augmentFirstWeight_cosine_nonneg
#print axioms Erdos345.interpolate_cosine_mass
#print axioms Erdos345.flatCosineNonnegative_of_real
#print axioms Erdos345.flat_family_from_cosine_existence
#print axioms Erdos345.exists_good_center_bound_from_cosine_existence
#print axioms Erdos345.countingProfileWeight_antitone
#print axioms Erdos345.countingProfileWeight_support
#print axioms Erdos345.countingProfileWeight_pos
#print axioms Erdos345.countingProfileWeight_interlace
#print axioms Erdos345.exact_mass_from_counting_profile
#print axioms Erdos345.nonzero_zmod_sum_eq_nat
#print axioms Erdos345.cyclic_character_sum
#print axioms Erdos345.cyclicFourier_zero
#print axioms Erdos345.cyclic_character_pair
#print axioms Erdos345.cyclic_parseval_complex
#print axioms Erdos345.cyclic_parseval
#print axioms Erdos345.residueCollision_nonneg
#print axioms Erdos345.residueCollision_identity
#print axioms Erdos345.residueSupport_collision_bound
#print axioms Erdos345.residueSupport_large_of_collision_le_three
#print axioms Erdos345.cyclotomicRootIndex_card_le
#print axioms Erdos345.chebyshevMixingCost_polynomial_bound
#print axioms Erdos345.cyclotomicChebyshev_energy_lower
#print axioms Erdos345.cyclotomic_dvd_expand
#print axioms Erdos345.cyclotomicProduct_dvd_expand
#print axioms Erdos345.shiftAction_dilate
#print axioms Erdos345.dilation_preserves_recurrence
#print axioms Erdos345.cyclotomic_dilation_preserves_recurrence
#print axioms Erdos345.dilationMatrix_matches_sequence
#print axioms Erdos345.cyclotomicRootValue_injective
#print axioms Erdos345.cyclotomicRootValue_ne_zero
#print axioms Erdos345.cyclotomicProduct_split
#print axioms Erdos345.cyclotomic_recurrence_expansion
#print axioms Erdos345.monic_divisor_of_prime_product
#print axioms Erdos345.monic_divisor_of_cyclotomicProduct
#print axioms Erdos345.exists_minimal_cyclotomic_annihilator
#print axioms Erdos345.cyclotomic_resultant_eq_product
#print axioms Erdos345.one_le_norm_intCast
#print axioms Erdos345.primitive_value_norm_product_ge_one
#print axioms Erdos345.cyclotomic_eval_one_isUnit_primePower
#print axioms Erdos345.cyclotomicProduct_eval_one_isUnit
#print axioms Erdos345.remove_nonprimary_cyclotomic_factors
#print axioms Erdos345.finiteSineEnergy_range
#print axioms Erdos345.finiteSineEnergy_mono
#print axioms Erdos345.finiteSineEnergy_le_add_missing
#print axioms Erdos345.prefixEnergy_le_population_add_missing
#print axioms Erdos345.populationEnergy_ge_prefix_sub_missing
#print axioms Erdos345.interval_of_dense_balanced_sumsets
#print axioms Erdos345.dense_int_sumset_interval
#print axioms Erdos345.dense_nat_sumset_interval
#print axioms Erdos345.polynomial_of_vanishing_difference
#print axioms Erdos345.flat_quotient_vanishing_difference
#print axioms Erdos345.exists_flat_quotient_polynomial
#print axioms Erdos345.sequenceDilation_pow
#print axioms Erdos345.dilationAction_sum
#print axioms Erdos345.dilationAction_mul
#print axioms Erdos345.dilationAction_map
#print axioms Erdos345.dilationAction_factor_exponential
#print axioms Erdos345.dilationAction_multiple_kills_exponential
#print axioms Erdos345.split_dilation_annihilator
#print axioms Erdos345.dilationAction_power_at_one
#print axioms Erdos345.dilationAction_congruence
#print axioms Erdos345.dilation_annihilator_divides_value
#print axioms Erdos345.cyclotomicProduct_monic
#print axioms Erdos345.dilationBoundPolynomial_eval
#print axioms Erdos345.dilationBoundPolynomial_factor
#print axioms Erdos345.dilationBoundPolynomial_annihilates_complex
#print axioms Erdos345.dilationBoundPolynomial_annihilates_integer
#print axioms Erdos345.power_annihilator_dilation_product_dvd
#print axioms Erdos345.recurrenceSolver_apply
#print axioms Erdos345.dilationMatrix_mulVec
#print axioms Erdos345.dilation_power_congruence
#print axioms Erdos345.dilation_characteristic_dvd
#print axioms Erdos345.power_annihilator_degree_ge_two
#print axioms Erdos345.power_annihilator_characteristic_dvd
#print axioms Erdos345.dilationDifference_pos
#print axioms Erdos345.dilationDifference_cast
#print axioms Erdos345.dilationDifference_factor
#print axioms Erdos345.primePower_le_dilation_valuation_sum
#print axioms Erdos345.dilationDifference_five_factorization
#print axioms Erdos345.complex_sq_norm_re
#print axioms Erdos345.discrete_energy_gram_identity
#print axioms Erdos345.gram_error_identity
#print axioms Erdos345.gram_error_le
#print axioms Erdos345.discrete_energy_lower_of_gram
#print axioms Erdos345.discrete_energy_half_lower_of_gram
#print axioms Erdos345.unit_geometric_sum_norm_le
#print axioms Erdos345.oscillatory_sum_norm_le_variation
#print axioms Erdos345.oscillatory_sum_norm_le_of_step_bound
#print axioms Erdos345.product_step_norm_le
#print axioms Erdos345.exists_disjoint_subsets_of_uniform_card
#print axioms Erdos345.sum_divisorCount
#print axioms Erdos345.harmonic_eq_sum_Ioc
#print axioms Erdos345.sum_divisorCount_le_harmonic
#print axioms Erdos345.divisorWeight_nonneg
#print axioms Erdos345.divisorWeight_zero
#print axioms Erdos345.divisorWeight_nat
#print axioms Erdos345.sum_divisorWeight
#print axioms Erdos345.sum_divisorWeight_le
#print axioms Erdos345.hasSum_nat_pow_div_two
#print axioms Erdos345.hasSum_shift_three_fifth_div_two
#print axioms Erdos345.hasSum_nat_fifth_div_two
#print axioms Erdos345.tsum_succ_fifth_div_two
#print axioms Erdos345.summable_shift_fifth_div_two
#print axioms Erdos345.dyadic_fifth_shift_bound
#print axioms Erdos345.dyadicAtomFrequency_nonneg
#print axioms Erdos345.dyadicAtomFrequency_pos
#print axioms Erdos345.sum_dyadicAtomFrequency
#print axioms Erdos345.sum_dyadicFrequency_level
#print axioms Erdos345.dyadicFrequency_level_bound
#print axioms Erdos345.summable_dyadicFrequency
#print axioms Erdos345.summable_nat_pow_div_two
#print axioms Erdos345.summable_succ_pow_div_two
#print axioms Erdos345.dyadic_cover_below
#print axioms Erdos345.backwardPrefix_mono
#print axioms Erdos345.backwardPrefix_bound_of_dyadic
#print axioms Erdos345.sum_sine_dyadicFrequency_level
#print axioms Erdos345.summable_sine_dyadicFrequency
#print axioms Erdos345.summable_abs_sine_dyadicFrequency
#print axioms Erdos345.tsum_sine_dyadicFrequency
#print axioms Erdos345.sum_nat_le_square_of_interval
#print axioms Erdos345.dyadicSineLevel_abs_bound
#print axioms Erdos345.summable_dyadicSineLevels
#print axioms Erdos345.dyadicSineLevel_nonneg_tail
#print axioms Erdos345.unreservedPopulation_subset_prefix
#print axioms Erdos345.population_energy_le_prefix
#print axioms Erdos345.nonzero_lowEnergyGrid_empty
#print axioms Erdos345.flatInverseRadius_nonneg
#print axioms Erdos345.unreserved_lowEnergyGrid_empty
#print axioms Erdos345.powerCollisionSum_le_of_empty_exceptional
#print axioms Erdos345.unreserved_collisionSum_le
#print axioms Erdos345.endpoint_extension_card_growth
#print axioms Erdos345.sumset_residue_growth
#print axioms Erdos345.multiplicity_log_bound_of_energy
#print axioms Erdos345.multiplicity_bound_of_energy
#print axioms Erdos345.minimal_integer_primePower_multiplicity_bound
#print axioms Erdos345.minimal_integer_rootOne_multiplicity_bound
#print axioms Erdos345.energyHeightConstant_le_logScale
#print axioms Erdos345.centerExponentConstant_nonneg
#print axioms Erdos345.centerWindowExponent_le_logScale
#print axioms Erdos345.pad_exponential_expansion
#print axioms Erdos345.polynomial_exponential_expansion
#print axioms Erdos345.nonunit_expansion_sum_zero
#print axioms Erdos345.multiplicity_le_of_padded_sum_zero
#print axioms Erdos345.multiplicities_eq_of_padded_sum_zero
#print axioms Erdos345.sufficientCenterWindow_ge_sixteen
#print axioms Erdos345.sufficientCenterWindow_large
#print axioms Erdos345.sufficientCenterWindow_contracts
#print axioms Erdos345.centerEnergy_gt_sufficientPrefix
#print axioms Erdos345.exists_good_degree_explicit_center_bound
#print axioms Erdos345.degree_le_exp_logScale
#print axioms Erdos345.monomial_exp_logScale_bound
#print axioms Erdos345.eventually_monomial_exp_dominated
#print axioms Erdos345.exponentialPower_mem_genEigenspace
#print axioms Erdos345.independent_submodules_linearIndependent_sigma
#print axioms Erdos345.exponentialPower_family_linearIndependent
#print axioms Erdos345.shiftAction_sub
#print axioms Erdos345.shiftAction_X
#print axioms Erdos345.exponential_difference
#print axioms Erdos345.exponential_difference_power
#print axioms Erdos345.exponentialPower_annihilate
#print axioms Erdos345.exponentialPower_top_difference
#print axioms Erdos345.exponentialPower_dilate
#print axioms Erdos345.exponentialPower_linearIndependent
#print axioms Erdos345.power_dvd_factorial_of_mul_le
#print axioms Erdos345.prime_scaled_exponent_bound
#print axioms Erdos345.conductorCoefficient_ge_one
#print axioms Erdos345.primary_uniform_exponent_bound
#print axioms Erdos345.centerEnergy_gt_of_flat_family
#print axioms Erdos345.uniformMean_sub
#print axioms Erdos345.uniformMean_comm
#print axioms Erdos345.uniformMean_pi_eval
#print axioms Erdos345.uniformMean_pi_two
#print axioms Erdos345.map_iteratedDifference
#print axioms Erdos345.dvd_iteratedDifference
#print axioms Erdos345.iteratedDifference_sub
#print axioms Erdos345.iteratedDifference_zero_of_prefix
#print axioms Erdos345.newtonEval_zero
#print axioms Erdos345.newtonEval_succ
#print axioms Erdos345.difference_newtonEval
#print axioms Erdos345.iteratedDifference_newtonEval
#print axioms Erdos345.iteratedDifference_newtonEval_zero
#print axioms Erdos345.iteratedDifference_power_zero
#print axioms Erdos345.iteratedDifference_difference
#print axioms Erdos345.newton_forward_formula
#print axioms Erdos345.eventIndicator_nonneg
#print axioms Erdos345.exists_lt_of_uniformMean_lt
#print axioms Erdos345.uniformMean_event_le
#print axioms Erdos345.finite_bad_event_selection
#print axioms Erdos345.uniformMean_const
#print axioms Erdos345.uniformMean_add
#print axioms Erdos345.uniformMean_sum
#print axioms Erdos345.uniformMean_finset_sum
#print axioms Erdos345.uniformMean_mul_const
#print axioms Erdos345.uniformMean_nonneg
#print axioms Erdos345.uniformMean_mono
#print axioms Erdos345.uniformMean_pi_prod
#print axioms Erdos345.uniformMean_ite_eq
#print axioms Erdos345.interval_for_128_sets
#print axioms Erdos345.fiber_card_defect_bound
#print axioms Erdos345.image_filter_preimage
#print axioms Erdos345.fiber_card_le_preimage_card
#print axioms Erdos345.image_filter_mem
#print axioms Erdos345.image_filter_mem_preimage
#print axioms Erdos345.fiber_partition_card
#print axioms Erdos345.fiber_region_card_eq_sum
#print axioms Erdos345.baseSum_twice
#print axioms Erdos345.baseSum_sqrt_gap
#print axioms Erdos345.sqrt_succ_pow_ge
#print axioms Erdos345.exists_exception_from_shifted_primes
#print axioms Erdos345.threshold_lower_bound_from_shifted_primes
#print axioms Erdos345.not_represented_of_residue
#print axioms Erdos345.shifted_power_mod_prime
#print axioms Erdos345.shifted_power_mod_prime_product
#print axioms Erdos345.residue_in_top_interval
#print axioms Erdos345.exists_exception_from_residue
#print axioms Erdos345.padFin_castLE
#print axioms Erdos345.padFin_eq_zero
#print axioms Erdos345.sum_padFin_smul
#print axioms Erdos345.flat_radius_perturbation_le_eight
#print axioms Erdos345.perturbation_budget_of_separation
#print axioms Erdos345.zero_mem_finitePowerSums
#print axioms Erdos345.finitePowerSums_mono
#print axioms Erdos345.naturalResidueImage_finitePowerSums
#print axioms Erdos345.finitePowerSums_insert
#print axioms Erdos345.finitePowerSums_insert_growth
#print axioms Erdos345.representedResidues_mono
#print axioms Erdos345.finitePowerSums_union_growth
#print axioms Erdos345.uniformMean_complex_cast
#print axioms Erdos345.residueMass_nonneg
#print axioms Erdos345.residueMass_sum
#print axioms Erdos345.residueMass_zero_outside
#print axioms Erdos345.residueMass_sum_support
#print axioms Erdos345.residueMass_fourier
#print axioms Erdos345.mean_finiteRowMean
#print axioms Erdos345.finiteRowMean_nonneg
#print axioms Erdos345.mean_finiteRowMean_le
#print axioms Erdos345.eventIndicator_sum_card
#print axioms Erdos345.complement_filter_half
#print axioms Erdos345.mean_bad_row_le
#print axioms Erdos345.le_natSetSpan
#print axioms Erdos345.natSetSpan_mem
#print axioms Erdos345.natSetSpan_upper
#print axioms Erdos345.natSetSpan_le_of_bound
#print axioms Erdos345.indexed_sumset_span
#print axioms Erdos345.indexed_sumset_zero
#print axioms Erdos345.card_le_natSetSpan_add_one
#print axioms Erdos345.many_shifted_primes_half_lower
#print axioms Erdos345.upper_envelope_lt_threshold_of_many_primes
#print axioms Erdos345.rpow_increment_lower_small
#print axioms Erdos345.firstPowerWindow_length_lower
#print axioms Erdos345.firstPowerWindow_lower_ge
#print axioms Erdos345.firstPowerWindow_energy_lower
#print axioms Erdos345.large_scale_energy_lower
#print axioms Erdos345.dvd_fixedDifferenceDivisor_iff
#print axioms Erdos345.fixedDifferenceDivisor_pos
#print axioms Erdos345.reduction_quotient_dvd_fixedDifference
#print axioms Erdos345.reduction_quotient_dvd_fixedDivisor
#print axioms Erdos345.reductionModulus_pos
#print axioms Erdos345.reductionModulus_dvd_fixedProduct
#print axioms Erdos345.prime_sub_one_dvd_of_fixedDifferenceDivisor
#print axioms Erdos345.prime_dvd_fixedDifferenceDivisor_of_sub_one_dvd
#print axioms Erdos345.prime_dvd_fixedDifferenceDivisor_iff
#print axioms Erdos345.fixedDifference_eq_nat_sub
#print axioms Erdos345.nat_power_difference_factor
#print axioms Erdos345.prime_not_dvd_self_add_one
#print axioms Erdos345.fixedDifferenceDivisor_dvd_factored_value
#print axioms Erdos345.fixedDifferenceDivisor_odd_multiplicity
#print axioms Erdos345.five_power_sub_one_multiplicity
#print axioms Erdos345.fixedDifferenceDivisor_two_multiplicity
#print axioms Erdos345.factorization_cast_eq_emultiplicity
#print axioms Erdos345.fixedDifferenceDivisor_factorization_le
#print axioms Erdos345.divisors_eq_filter_Icc
#print axioms Erdos345.X_power_sub_one_power_cyclotomic
#print axioms Erdos345.flatPolynomial_cyclotomic_factorization
#print axioms Erdos345.flatCyclotomic_annihilates
#print axioms Erdos345.exists_minimal_flat_cyclotomic_annihilator
#print axioms Erdos345.exists_minimal_flat_slot_bound
#print axioms Erdos345.flat_regularizedValue_eq
#print axioms Erdos345.vanishingPowerProduct_nonneg
#print axioms Erdos345.vanishingPowerProduct_le
#print axioms Erdos345.flat_regularizedNorm_formula
#print axioms Erdos345.flat_regularizedNorm_le
#print axioms Erdos345.rational_cast_flat_recurrence
#print axioms Erdos345.flat_error_annihilation
#print axioms Erdos345.exists_flat_error_minimal_pair
#print axioms Erdos345.exists_flat_error_multiplicity_bounds
#print axioms Erdos345.inverse_energy_mono_length
#print axioms Erdos345.flat_inverse_energy
#print axioms Erdos345.abs_le_flatInverseRadius
#print axioms Erdos345.flat_inverse_of_energy_le
#print axioms Erdos345.shiftAction_C
#print axioms Erdos345.shiftAction_constant
#print axioms Erdos345.shiftAction_one_sub_X_power
#print axioms Erdos345.polynomial_top_difference_all
#print axioms Erdos345.flatPolynomial_top_moment
#print axioms Erdos345.coefficientL1_flatQuotient
#print axioms Erdos345.coefficientL1_flatPolynomial_ge_one
#print axioms Erdos345.geometricNat_map
#print axioms Erdos345.flatQuotient_eq_product
#print axioms Erdos345.flatQuotient_coeff_nonneg
#print axioms Erdos345.flatQuotient_eval_one
#print axioms Erdos345.flatQuotient_eval_one_pos
#print axioms Erdos345.flatQuotient_eval_one_dvd
#print axioms Erdos345.flatPolynomial_factor
#print axioms Erdos345.flatPolynomial_coeff_zero
#print axioms Erdos345.flatPolynomial_ne_zero
#print axioms Erdos345.one_sub_X_pow_natDegree
#print axioms Erdos345.one_sub_X_pow_leadingCoeff
#print axioms Erdos345.flatPolynomial_leadingCoeff
#print axioms Erdos345.flatPolynomial_natDegree
#print axioms Erdos345.flatPolynomial_natDegree_le
#print axioms Erdos345.one_sub_X_power_dvd_flatPolynomial
#print axioms Erdos345.flatPolynomial_rootMultiplicity_one
#print axioms Erdos345.initialCosineSum_floor_eq
#print axioms Erdos345.belovFloorCosine_zero_outside
#print axioms Erdos345.summable_belovFloorCosine
#print axioms Erdos345.belovFloorCosine_eq_sum
#print axioms Erdos345.tsum_belovFloorCosine
#print axioms Erdos345.collision_decay_of_parameters
#print axioms Erdos345.good_degrees_fourier_decay
#print axioms Erdos345.tendsto_fourier_decay_zero
#print axioms Erdos345.eventually_fourier_decay_small
#print axioms Erdos345.good_degrees_collision_small
#print axioms Erdos345.eventually_fourier_parameter_conditions
#print axioms Erdos345.eventually_fourier_energy_margin
#print axioms Erdos345.eventually_fourier_root_budget
#print axioms Erdos345.exp_quarter_le_exp_half
#print axioms Erdos345.eventually_fourier_coarse_window
#print axioms Erdos345.eventually_fourier_chebyshev_length
#print axioms Erdos345.eventually_fourier_center_separation
#print axioms Erdos345.fourierN_pos
#print axioms Erdos345.fourierW_pos
#print axioms Erdos345.fourierW_le_N
#print axioms Erdos345.fourierH_nonneg
#print axioms Erdos345.fourierH_add_one_le
#print axioms Erdos345.fourierN_bounds
#print axioms Erdos345.fourierW_bounds
#print axioms Erdos345.log_fourierN_add_one_le
#print axioms Erdos345.eventually_inverse_factor_bound
#print axioms Erdos345.eventually_fourier_degree_bound
#print axioms Erdos345.eventually_exp_quarter_ge_eight
#print axioms Erdos345.eventually_fourier_inverse_size
#print axioms Erdos345.eventually_fourier_center_prefix
#print axioms Erdos345.good_degrees_gcd_one_groups
#print axioms Erdos345.factorial_conductor_log_bound
#print axioms Erdos345.goodConductorEnvelope_nonneg
#print axioms Erdos345.exists_good_conductor_degree
#print axioms Erdos345.degreeInterval_card
#print axioms Erdos345.degreeInterval_nonempty
#print axioms Erdos345.dyadicShifts_card
#print axioms Erdos345.dyadicShifts_nonempty
#print axioms Erdos345.sum_dyadicShifts
#print axioms Erdos345.harmonic_nonneg
#print axioms Erdos345.exists_good_dyadic_degree
#print axioms Erdos345.exists_good_prefix_degree
#print axioms Erdos345.exists_good_degree
#print axioms Erdos345.good_degrees_threshold_upper
#print axioms Erdos345.exists_good_reduction_degree
#print axioms Erdos345.mem_gridNear
#print axioms Erdos345.card_gridNear_le
#print axioms Erdos345.card_centerNumerators
#print axioms Erdos345.card_commonRationalArcs_le
#print axioms Erdos345.mem_commonRationalArcs_of_near
#print axioms Erdos345.powerCollisionSum_le_exceptional_count
#print axioms Erdos345.powerCollisionSum_le_grid_count
#print axioms Erdos345.powerCollisionSum_le_flat_grid
#print axioms Erdos345.finitePowerSums_le_span
#print axioms Erdos345.finitePowerSums_subset_interval
#print axioms Erdos345.representedUpTo_of_group_sums
#print axioms Erdos345.mem_indexed_sumset
#print axioms Erdos345.indexed_sumset_nonempty
#print axioms Erdos345.indexed_sumset_bound
#print axioms Erdos345.indexed_sumset_card_lower
#print axioms Erdos345.lowEnergyGrid_subset_integerArcs
#print axioms Erdos345.card_lowEnergyGrid_integer_le
#print axioms Erdos345.powerCollisionSum_le_integer_localized
#print axioms Erdos345.powerCollisionSum_le_integer_inverse
#print axioms Erdos345.flat_multiplicity_le_dimension
#print axioms Erdos345.integer_recurrence_primePower_energy_lower
#print axioms Erdos345.integer_recurrence_rootOne_energy_lower
#print axioms Erdos345.minimal_integer_primePower_energy_lower
#print axioms Erdos345.minimal_integer_rootOne_energy_lower
#print axioms Erdos345.integer_sumset_growth_of_generating
#print axioms Erdos345.binomialPolynomial_eval_nat
#print axioms Erdos345.binomialPolynomial_eval_int
#print axioms Erdos345.binomialPolynomial_natDegree_le
#print axioms Erdos345.binomialPolynomial_coeff_self
#print axioms Erdos345.newtonPolynomial_integerValued
#print axioms Erdos345.newtonPolynomial_eval_nat
#print axioms Erdos345.newtonPolynomial_natDegree_le
#print axioms Erdos345.newtonPolynomial_coeff_top
#print axioms Erdos345.newtonPolynomial_eval_initial
#print axioms Erdos345.polynomial_eq_of_eval_range
#print axioms Erdos345.polynomial_eq_newtonPolynomial
#print axioms Erdos345.polynomial_top_difference
#print axioms Erdos345.newtonEval_truncate_eq_sum
#print axioms Erdos345.newtonPolynomial_eval_truncate
#print axioms Erdos345.polynomial_difference_coefficient_zero
#print axioms Erdos345.polynomial_iteratedDifference_zero
#print axioms Erdos345.componentFilter_expansion_at_zero
#print axioms Erdos345.isIntegral_shiftAction
#print axioms Erdos345.filtered_top_isIntegral
#print axioms Erdos345.complementFactor_eval_ne_zero
#print axioms Erdos345.filtered_top_ne_zero
#print axioms Erdos345.good_degrees_interval_ready_groups
#print axioms Erdos345.exists_inverse_error_polynomial
#print axioms Erdos345.flatQuotient_natDegree_le
#print axioms Erdos345.flatInverseRadius_le_power
#print axioms Erdos345.flatInverseRadius_eighth_scale
#print axioms Erdos345.flatInverseRadius_le_one
#print axioms Erdos345.groupLabel_injective
#print axioms Erdos345.select_groups_with_support_and_span
#print axioms Erdos345.good_degrees_selected_groups
#print axioms Erdos345.mean_labelHit
#print axioms Erdos345.mean_centeredLabelHit
#print axioms Erdos345.mean_centeredLabelHit_square
#print axioms Erdos345.mean_centeredLabelHit_pair
#print axioms Erdos345.mem_labelGroup
#print axioms Erdos345.labelGroup_disjoint
#print axioms Erdos345.label_product_mean
#print axioms Erdos345.label_product_exp_bound
#print axioms Erdos345.label_cosine_product_bound
#print axioms Erdos345.sampledBases_subset
#print axioms Erdos345.sampledBases_disjoint
#print axioms Erdos345.prod_sampledBases
#print axioms Erdos345.uniformMean_const_mul
#print axioms Erdos345.labelWeightSum_eq
#print axioms Erdos345.mean_labelWeightSum
#print axioms Erdos345.centered_labelWeightSum
#print axioms Erdos345.labelWeight_variance
#print axioms Erdos345.labelWeight_variance_le
#print axioms Erdos345.iteratedDifference_add
#print axioms Erdos345.difference_annihilator_reduction
#print axioms Erdos345.zeroth_difference_modulus_one
#print axioms Erdos345.primaryProduct_eq_rootOne
#print axioms Erdos345.primary_multiplicity_zero_of_large_prime
#print axioms Erdos345.primary_rootOne_reduction
#print axioms Erdos345.large_prime_power_reduction
#print axioms Erdos345.lev_integer_growth
#print axioms Erdos345.lev_uniform_growth
#print axioms Erdos345.lev_parameters_large
#print axioms Erdos345.lev_interval_covers_next_power
#print axioms Erdos345.local_scaling_multiplicity_bound
#print axioms Erdos345.logScale_ge_one
#print axioms Erdos345.natLog_two_le_real_log
#print axioms Erdos345.conductorCoefficient_le_logScale
#print axioms Erdos345.goodConductorEnvelope_le_logScale
#print axioms Erdos345.log_regularizedNorm_le
#print axioms Erdos345.primePower_le_twice_totient
#print axioms Erdos345.scaled_log_regularizedNorm_le
#print axioms Erdos345.scaled_log_regularizedNorm_le_three
#print axioms Erdos345.tendsto_logScale_atTop
#print axioms Erdos345.exp_logScale
#print axioms Erdos345.logScale_pow_div_identity
#print axioms Erdos345.tendsto_logScale_pow_div
#print axioms Erdos345.eventually_logScale_pow_small
#print axioms Erdos345.eventually_sixth_power_below_eighth
#print axioms Erdos345.mem_lowEnergyGrid
#print axioms Erdos345.lowEnergyGrid_subset_commonRationalArcs
#print axioms Erdos345.card_lowEnergyGrid_le
#print axioms Erdos345.stackWindowCount_size
#print axioms Erdos345.stackWindowCount_le
#print axioms Erdos345.stackWindowCount_log
#print axioms Erdos345.middle_scale_energy_lower
#print axioms Erdos345.minimalAnnihilator_dvd_iff
#print axioms Erdos345.minimalAnnihilator_annihilates
#print axioms Erdos345.minimalAnnihilator_ne_zero
#print axioms Erdos345.minimalAnnihilator_monic
#print axioms Erdos345.minimalAnnihilator_natDegree_le
#print axioms Erdos345.minimalAnnihilator_unique
#print axioms Erdos345.exists_integral_minimalAnnihilator
#print axioms Erdos345.shiftAction_monomial
#print axioms Erdos345.shiftAction_ofFn
#print axioms Erdos345.initialShiftFamily_linearIndependent
#print axioms Erdos345.no_small_annihilator_of_initial_independent
#print axioms Erdos345.shiftAction_map_annihilates
#print axioms Erdos345.minimalAnnihilator_map
#print axioms Erdos345.minimal_nonunit_component_comparison
#print axioms Erdos345.rational_minimal_cyclotomic_complex
#print axioms Erdos345.unitCyclotomicIndex_value
#print axioms Erdos345.cyclotomic_index_ne_unit
#print axioms Erdos345.dvd_reductionModulus_self
#print axioms Erdos345.exists_reduction_degree
#print axioms Erdos345.minimalReductionDegree_spec
#print axioms Erdos345.minimalReductionDegree_le
#print axioms Erdos345.minimalReductionDegree_le_self
#print axioms Erdos345.minimalReductionDegree_le_iff
#print axioms Erdos345.minimalReductionDegree_pos
#print axioms Erdos345.minimalReductionDegree_polynomial
#print axioms Erdos345.minimalReductionDegree_le_of_contraction
#print axioms Erdos345.log_modulus_le_of_contraction
#print axioms Erdos345.cyclotomicProduct_degree_pos
#print axioms Erdos345.integer_minimal_cyclotomic_complex
#print axioms Erdos345.minimal_cyclotomic_witness_norm_lower
#print axioms Erdos345.totalChebyshevMass_nonneg
#print axioms Erdos345.chebyshevMass_le_total
#print axioms Erdos345.totalChebyshevMass_sq_le
#print axioms Erdos345.mixedChebyshev_energy_mass_lower
#print axioms Erdos345.mixedChebyshev_energy_lower
#print axioms Erdos345.mixedChebyshev_half_energy_lower
#print axioms Erdos345.matrix_sum_re_ge_diagonal
#print axioms Erdos345.discreteGram_self_re
#print axioms Erdos345.discrete_sum_energy_ge_diagonal
#print axioms Erdos345.integer_annihilator_of_rational_map
#print axioms Erdos345.minimal_integer_cyclotomic_annihilates
#print axioms Erdos345.annihilator_transfer_to_power
#print axioms Erdos345.integer_error_power_congruence
#print axioms Erdos345.rational_error_annihilator_mod_power
#print axioms Erdos345.modulated_discreteGram
#print axioms Erdos345.modulated_discreteGram_offDiagonal_le
#print axioms Erdos345.cyclotomic_modulated_offDiagonal_le
#print axioms Erdos345.weight_le_mass
#print axioms Erdos345.initial_finset_eq_range_card
#print axioms Erdos345.weightLayer_eq_range
#print axioms Erdos345.layerHeight_le
#print axioms Erdos345.layer_index_count
#print axioms Erdos345.layer_weighted_sum
#print axioms Erdos345.sum_layerHeight
#print axioms Erdos345.layer_weighted_product
#print axioms Erdos345.normalizedMoment_eq_layer_factorials
#print axioms Erdos345.normalizedMoment_dvd_factorial
#print axioms Erdos345.normalizedMoment_pos
#print axioms Erdos345.rootSlots_eq_layer_quotients
#print axioms Erdos345.rootSlots_mul_le_mass
#print axioms Erdos345.group_sumset_nonempty
#print axioms Erdos345.sumset_add_idempotent
#print axioms Erdos345.stabilizer_subset_group_sumset
#print axioms Erdos345.multiple_kneser_fixed_stabilizer
#print axioms Erdos345.multiple_kneser
#print axioms Erdos345.natural_gcd_mem_addSubgroup
#print axioms Erdos345.natural_finset_gcd_mem_addSubgroup
#print axioms Erdos345.natural_residue_generates_of_gcd_one
#print axioms Erdos345.natural_residue_generates_of_no_progression
#print axioms Erdos345.mem_naturalWindow
#print axioms Erdos345.naturalWindow_card_half_length
#print axioms Erdos345.powerCoefficient_eq_zero
#print axioms Erdos345.pow_newton_expansion
#print axioms Erdos345.newtonEval_injective
#print axioms Erdos345.newtonEval_powerCoefficient
#print axioms Erdos345.hasNewtonReduction_iff
#print axioms Erdos345.low_energy_center_numerator_divisible
#print axioms Erdos345.integer_near_of_numerator_divisible
#print axioms Erdos345.low_energy_near_factorial_center_is_near_integer
#print axioms Erdos345.flat_inverse_integer_center
#print axioms Erdos345.tsum_ge_initial_sum_of_nonnegative_tail
#print axioms Erdos345.dyadicSineTotal_pos_small
#print axioms Erdos345.natCast_power_eq_one_iff_dvd_sub
#print axioms Erdos345.odd_prime_lift_dvd
#print axioms Erdos345.exists_odd_dilation_generator
#print axioms Erdos345.prime_not_dvd_pred
#print axioms Erdos345.generator_power_sub_one_factorization
#print axioms Erdos345.dilationDifference_odd_factorization
#print axioms Erdos345.generator_coprime
#print axioms Erdos345.odd_generator_prime_power_period
#print axioms Erdos345.generator_prime_power_period_factorization
#print axioms Erdos345.oddPrimeDilationPeriod_one
#print axioms Erdos345.oddPrimeDilationPeriod_pow_succ
#print axioms Erdos345.oddPrimeDilationPeriod_pos
#print axioms Erdos345.oddPrimeDilationPeriod_period
#print axioms Erdos345.odd_dilation_root_one_sum
#print axioms Erdos345.odd_dilation_primary_sum
#print axioms Erdos345.oddPrime_cyclotomic_multiplicity_bound
#print axioms Erdos345.oddPrime_cyclotomic_multiplicity_log_bound
#print axioms Erdos345.oddSineSum_identity
#print axioms Erdos345.oddSineSum_abs_le
#print axioms Erdos345.oddSineSum_zero
#print axioms Erdos345.oddSineSum_pi
#print axioms Erdos345.oddSineSum_abs_le_inv_sin
#print axioms Erdos345.oddSineSum_nonneg
#print axioms Erdos345.oddSineSum_small_angle_lower
#print axioms Erdos345.exact_reduction_step
#print axioms Erdos345.exists_exact_reduction_step
#print axioms Erdos345.ordinaryComponentPolynomial_degree
#print axioms Erdos345.ordinaryComponentPolynomial_coeff
#print axioms Erdos345.ordinaryComponentPolynomial_eval
#print axioms Erdos345.ordinary_expansion_as_frequency_sum
#print axioms Erdos345.ordinary_cyclotomic_expansion_energy_lower
#print axioms Erdos345.periodic_lifting_arithmetic
#print axioms Erdos345.periodic_sumset_lifting
#print axioms Erdos345.sin_square_sub_integer
#print axioms Erdos345.sine_square_lower_on_phase_window
#print axioms Erdos345.finiteSineEnergy_phase_window_lower
#print axioms Erdos345.naturalWindow_energy_lower
#print axioms Erdos345.complex_coefficient_norm_le_unit_bound
#print axioms Erdos345.coefficientL1_le_unit_bound
#print axioms Erdos345.coefficientL1_flat_from_cosine
#print axioms Erdos345.scaled_chebyshev_samples
#print axioms Erdos345.polynomialFrequency_energy_lower
#print axioms Erdos345.rootSlots_one
#print axioms Erdos345.rational_polynomial_perturbation_components
#print axioms Erdos345.complex_polynomial_sum_of_rational
#print axioms Erdos345.polynomialReduction_tail_divisibility
#print axioms Erdos345.polynomialReduction_of_tail_divisibility
#print axioms Erdos345.hasIntegerPolynomialReduction_iff_dvd
#print axioms Erdos345.X_pow_eq_newtonPolynomial
#print axioms Erdos345.integer_power_newton_expansion
#print axioms Erdos345.globalPolynomialReduction_to_nat
#print axioms Erdos345.globalPolynomialReduction_of_tail_divisibility
#print axioms Erdos345.hasGlobalIntegerPolynomialReduction_iff_dvd
#print axioms Erdos345.polynomial_sample_energy_lower
#print axioms Erdos345.real_polynomial_sample_energy_lower
#print axioms Erdos345.polynomialShiftAction_eval
#print axioms Erdos345.polynomialShiftAction_degree
#print axioms Erdos345.taylor_coeff_of_natDegree_le
#print axioms Erdos345.polynomialShiftAction_top
#print axioms Erdos345.positivePhaseScale_pos
#print axioms Erdos345.positivePhaseScale_pow
#print axioms Erdos345.power_phase_eq_scaled
#print axioms Erdos345.finiteSineEnergy_eq_scaled
#print axioms Erdos345.sine_square_complement_numerator
#print axioms Erdos345.finiteSineEnergy_complement_numerator
#print axioms Erdos345.finiteSineEnergy_min_numerator
#print axioms Erdos345.positivePhaseScale_ge
#print axioms Erdos345.positivePhaseScale_le
#print axioms Erdos345.positivePhaseScale_le_base
#print axioms Erdos345.powerBit_fourier_norm
#print axioms Erdos345.powerBit_collision_eq
#print axioms Erdos345.powerBit_support_subset_represented
#print axioms Erdos345.representedResidues_large_of_cosineSum
#print axioms Erdos345.positive_power_sum_bound
#print axioms Erdos345.unreservedEndpoint_add_one_le
#print axioms Erdos345.unreserved_power_sum_bound
#print axioms Erdos345.unreserved_power_square_sum_bound
#print axioms Erdos345.rpow_increment_lower
#print axioms Erdos345.powerWindowLower_nonneg
#print axioms Erdos345.powerWindow_length_lower
#print axioms Erdos345.powerWindow_phase
#print axioms Erdos345.reciprocal_window_sum
#print axioms Erdos345.reciprocal_window_sum_log_lower
#print axioms Erdos345.powerWindows_log_energy_lower
#print axioms Erdos345.powerWindowLower_ge_scale
#print axioms Erdos345.powerWindowUpper_le_bound
#print axioms Erdos345.powerWindow_subset_population
#print axioms Erdos345.powerWindow_length_ge_two
#print axioms Erdos345.powerWindows_energy_lower
#print axioms Erdos345.sufficientCenterPrefix_pos
#print axioms Erdos345.log_sufficientCenterPrefix_le
#print axioms Erdos345.centerPrefixLogConstant_nonneg
#print axioms Erdos345.log_sufficientCenterPrefix_square_le
#print axioms Erdos345.mem_primaryOrders
#print axioms Erdos345.mem_nonprimaryOrders
#print axioms Erdos345.cyclotomicProduct_primary_split
#print axioms Erdos345.nonprimaryOrders_exclude_primePowers
#print axioms Erdos345.primary_power_annihilator
#print axioms Erdos345.primary_local_scaling_bound
#print axioms Erdos345.rational_error_local_scaling_bound
#print axioms Erdos345.primary_order_ge_prime
#print axioms Erdos345.primaryOrders_card_le_log
#print axioms Erdos345.primary_exponent_bound
#print axioms Erdos345.log_two_profile_bounds
#print axioms Erdos345.primeCounting_le_five_mul_div_log
#print axioms Erdos345.prime_product_ge_two_pow_card
#print axioms Erdos345.sqrt_prime_product_ge_two_pow_half
#print axioms Erdos345.power_lt_sqrt_power_sub
#print axioms Erdos345.two_pow_prime_count_lt_threshold
#print axioms Erdos345.log_threshold_lower_of_prime_count
#print axioms Erdos345.shifted_prime_log_threshold_lower
#print axioms Erdos345.intended_of_bombieri_vinogradov
#print axioms Erdos345.prime_log_ratio
#print axioms Erdos345.sum_prime_log_ratio
#print axioms Erdos345.sum_prime_weights_of_phaseBin
#print axioms Erdos345.odd_prime_mass_lower
#print axioms Erdos345.belov_prime_mass_lower
#print axioms Erdos345.primePhaseDistance_nonneg
#print axioms Erdos345.primePhaseDistance_eq
#print axioms Erdos345.primePhaseDistance_le_half
#print axioms Erdos345.primePhaseBin_le_distance
#print axioms Erdos345.primePhaseBin_dvd_alternative
#print axioms Erdos345.phase_floor_bounds
#print axioms Erdos345.sum_prime_logs_of_phaseBin
#print axioms Erdos345.primitiveTopCoefficient_norm_identity
#print axioms Erdos345.primitiveTopCoefficient_product_identity
#print axioms Erdos345.primitiveTopCoefficient_ne_zero
#print axioms Erdos345.exists_large_primePower_top_coefficient
#print axioms Erdos345.primitive_power_difference_product_eq_norm
#print axioms Erdos345.prime_primitive_sub_one_norm_product
#print axioms Erdos345.primePower_pure_power_norm_product
#print axioms Erdos345.primitive_power_norm_coprime_invariant
#print axioms Erdos345.primePower_general_power_norm_product
#print axioms Erdos345.primePowerValuation_le_divisor_sum
#print axioms Erdos345.nonvanishingPrimeWeight_le_slot_sum
#print axioms Erdos345.nonvanishingPrimeWeight_le_mass
#print axioms Erdos345.eventually_log_rpow_le_positive_rpow
#print axioms Erdos345.eventually_prime_progression_lower
#print axioms Erdos345.prime_mod_one_iff_shift_divides
#print axioms Erdos345.prime_progression_theta_eq
#print axioms Erdos345.prime_progression_theta_le_card
#print axioms Erdos345.prime_progression_card_lower
#print axioms Erdos345.endpointError_le_sum
#print axioms Erdos345.prime_progression_uniform_of_bounds
#print axioms Erdos345.sum_abs_sine_zero_bin
#print axioms Erdos345.sum_abs_sine_positive_bin
#print axioms Erdos345.sum_abs_prime_sine_harmonic
#print axioms Erdos345.sum_abs_prime_sine_bound
#print axioms Erdos345.prime_progression_scale_twice_primorial
#print axioms Erdos345.prime_progression_scale_ge
#print axioms Erdos345.log_prime_progression_scale
#print axioms Erdos345.log_prime_progression_scale_bounds
#print axioms Erdos345.prime_subset_products_twenty_four_lower
#print axioms Erdos345.prime_product_injective
#print axioms Erdos345.prime_subset_products_card
#print axioms Erdos345.prime_subset_products_valid
#print axioms Erdos345.choose_lower_half
#print axioms Erdos345.prime_count_sqrt_lower
#print axioms Erdos345.log_le_sqrt_large
#print axioms Erdos345.log_succ_le_twice_sqrt
#print axioms Erdos345.prime_theta_half_large
#print axioms Erdos345.exists_factor_ge_exp_neg
#print axioms Erdos345.belov_scaled_sine_identity
#print axioms Erdos345.profile_cosine_nonneg_of_sine_nonneg
#print axioms Erdos345.prouhetBlock_injective
#print axioms Erdos345.prouhetBlock_unique
#print axioms Erdos345.prouhetFamily_lt
#print axioms Erdos345.prouhetFamily_unique
#print axioms Erdos345.prouhetFamily_disjoint
#print axioms Erdos345.prouhetFamily_zero_mem
#print axioms Erdos345.prouhet_block_disjoint
#print axioms Erdos345.sum_prouhetFamily_succ
#print axioms Erdos345.sum_shift_power
#print axioms Erdos345.sum_sub_color
#print axioms Erdos345.prouhetFamily_moment_step
#print axioms Erdos345.prouhetFamily_moment_eq
#print axioms Erdos345.oddProuhet_positive_odd
#print axioms Erdos345.oddProuhet_disjoint
#print axioms Erdos345.oddProuhet_moment_expansion
#print axioms Erdos345.oddProuhet_moment_eq
#print axioms Erdos345.oddProuhet_one_mem
#print axioms Erdos345.exists_disjoint_odd_equal_powers
#print axioms Erdos345.intended_of_published_analytic_inputs
#print axioms Erdos345.exists_reduced_phase_long_window
#print axioms Erdos345.log_sufficientCenterPrefix_exp_bound
#print axioms Erdos345.sufficientCenterPrefix_le_quasipolynomial
#print axioms Erdos345.centerEnergy_mono
#print axioms Erdos345.exists_good_quasipolynomial_center_bound
#print axioms Erdos345.centerPrefixPowerConstant_nonneg
#print axioms Erdos345.quasipolynomialCenterPrefix_pos
#print axioms Erdos345.log_quasipolynomialCenterPrefix_le
#print axioms Erdos345.quasipolynomialCenterPrefix_le_seventh_scale
#print axioms Erdos345.eventually_logScale_ge
#print axioms Erdos345.eventually_quasipolynomialCenterPrefix_le_seventh_scale
#print axioms Erdos345.quotient_full_fiber_card
#print axioms Erdos345.quotient_fiber_card_le
#print axioms Erdos345.quotient_fiber_defect_bound
#print axioms Erdos345.quotient_new_class_of_generating
#print axioms Erdos345.quotient_region_residue_image
#print axioms Erdos345.quotient_old_region_growth
#print axioms Erdos345.quotient_sumset_fiber_bound
#print axioms Erdos345.quotient_sumset_fiber_bound_of_mem
#print axioms Erdos345.unit_radial_factor_ne_zero
#print axioms Erdos345.unit_radial_log_hasSum
#print axioms Erdos345.log_radialFlatProduct
#print axioms Erdos345.radialFlatProduct_log_hasSum
#print axioms Erdos345.unit_circle_radial_norm
#print axioms Erdos345.unit_circle_radial_ratio
#print axioms Erdos345.radialFlatProduct_norm
#print axioms Erdos345.flatPolynomial_norm_le_radial
#print axioms Erdos345.exists_oddPowerPacket
#print axioms Erdos345.OddPowerPacket.base_le_total
#print axioms Erdos345.OddPowerPacket.digit_properties
#print axioms Erdos345.oddControlledRepresentation_zero
#print axioms Erdos345.oddControlledRepresentation_scaled_add
#print axioms Erdos345.OddPowerPacket.represents_multiples
#print axioms Erdos345.correctionBase_injective
#print axioms Erdos345.correctionBase_odd_large
#print axioms Erdos345.correctionSum_eq_set
#print axioms Erdos345.correctionSum_mono
#print axioms Erdos345.correctionSum_modEq
#print axioms Erdos345.OddPowerPacket.threshold
#print axioms Erdos345.exists_least_powerThreshold
#print axioms Erdos345.leastPowerThreshold_spec
#print axioms Erdos345.intended_of_late_powerThreshold_inversions
#print axioms Erdos345.power_sineEnergy_abs
#print axioms Erdos345.rational_sineEnergy_eq_center
#print axioms Erdos345.rational_fraction_den_dvd
#print axioms Erdos345.rational_fraction_den_gt_one
#print axioms Erdos345.rational_center_energy_gt
#print axioms Erdos345.rational_error_primePower_energy_lower
#print axioms Erdos345.rational_error_primePower_multiplicity_bound
#print axioms Erdos345.top_norm_eq_of_component_sum
#print axioms Erdos345.rational_error_primePower_coefficient_height
#print axioms Erdos345.exists_rational_reduction_phase
#print axioms Erdos345.rational_phase_int_shift
#print axioms Erdos345.sin_pi_sq_int_shift
#print axioms Erdos345.rational_phase_sineEnergy_eq_center
#print axioms Erdos345.finite_reciprocal_sublevel
#print axioms Erdos345.mem_belovCutoff
#print axioms Erdos345.belovCountingProfile_monotone
#print axioms Erdos345.belovCountingProfile_zero_below_one
#print axioms Erdos345.belovCountingProfile_one_pos
#print axioms Erdos345.belovProfileTerm_nonneg
#print axioms Erdos345.belovProfileMajorant_summable
#print axioms Erdos345.belovProfileMajorant_nonneg
#print axioms Erdos345.belovProfileMajorant_monotone
#print axioms Erdos345.belovCountingProfile_le_majorant
#print axioms Erdos345.belovProfileMajorant_double
#print axioms Erdos345.zero_of_recurrence_initial
#print axioms Erdos345.eq_of_recurrence_initial
#print axioms Erdos345.recurrence_congruence
#print axioms Erdos345.generatedRecurrence_solution
#print axioms Erdos345.generatedRecurrence_initial
#print axioms Erdos345.generated_power_congruence
#print axioms Erdos345.polynomialRecurrence_sum
#print axioms Erdos345.shiftAction_last
#print axioms Erdos345.polynomialRecurrence_iff
#print axioms Erdos345.shiftAction_translate
#print axioms Erdos345.local_solution_agrees_mkSol
#print axioms Erdos345.prependRecurrence_solution
#print axioms Erdos345.exists_unshifted_recurrence
#print axioms Erdos345.exists_integral_recurrence_extension
#print axioms Erdos345.flatPolynomial_integral_extension
#print axioms Erdos345.recurrenceInitialMap_injective
#print axioms Erdos345.recurrenceKernel_finrank_le
#print axioms Erdos345.recurrence_expansion_of_card
#print axioms Erdos345.linearFactorProduct_monic
#print axioms Erdos345.linearFactorProduct_natDegree
#print axioms Erdos345.linearFactorProduct_annihilates_component
#print axioms Erdos345.split_recurrence_expansion
#print axioms Erdos345.shiftAction_translate_general
#print axioms Erdos345.recurrence_zero_of_zero_tail
#print axioms Erdos345.sequenceAnnihilator_translate
#print axioms Erdos345.minimalAnnihilator_translate
#print axioms Erdos345.minimalAnnihilator_flat_translate
#print axioms Erdos345.real_cast_flat_polynomial_annihilation
#print axioms Erdos345.exists_reduced_phase_recurrence
#print axioms Erdos345.energyHeightConstant_mono
#print axioms Erdos345.conductorCoefficient_mono
#print axioms Erdos345.log_bound_for_all_reductions
#print axioms Erdos345.shiftedPrimes_card_le_divisorCount
#print axioms Erdos345.shiftedPrimeProduct_le
#print axioms Erdos345.reductionModulus_le_divisorEnvelope
#print axioms Erdos345.log_reductionModulus_le
#print axioms Erdos345.dvd_reductionModulus_iff
#print axioms Erdos345.hasNewtonReduction_iff_dvd
#print axioms Erdos345.factorial_dvd_reductionModulus
#print axioms Erdos345.reductionModulus_mono_dvd
#print axioms Erdos345.powerCoefficient_one
#print axioms Erdos345.reductionModulus_zero
#print axioms Erdos345.reductionModulus_step
#print axioms Erdos345.cyclotomicProduct_factor
#print axioms Erdos345.eval_divByMonic_X_sub_C_eq_derivative
#print axioms Erdos345.complementFactor_of_factorization
#print axioms Erdos345.complementFactor_eval_eq_regularized
#print axioms Erdos345.cyclotomicProduct_add
#print axioms Erdos345.cyclotomicProduct_congr
#print axioms Erdos345.cyclotomic_derivative_eval_ne_zero
#print axioms Erdos345.cyclotomicComplement_eval_ne_zero
#print axioms Erdos345.regularizedCyclotomicValue_ne_zero
#print axioms Erdos345.regularizedCyclotomicNorm_ge_one
#print axioms Erdos345.regularizedCyclotomicValue_add
#print axioms Erdos345.regularizedCyclotomicNorm_add
#print axioms Erdos345.regularizedCyclotomicValue_congr
#print axioms Erdos345.regularizedCyclotomicNorm_mono
#print axioms Erdos345.rawFlatPolynomial_eq_cyclotomic
#print axioms Erdos345.regularizedPowerFactor_factor
#print axioms Erdos345.regularizedPowerProduct_factor
#print axioms Erdos345.regularizedPowerFactor_norm_of_dvd
#print axioms Erdos345.regularizedPowerFactor_primitive_norm_product
#print axioms Erdos345.represented_iff_mem_subsetSums
#print axioms Erdos345.represented_zero
#print axioms Erdos345.representation_bases_le
#print axioms Erdos345.exception_lt_threshold
#print axioms Erdos345.good_degrees_represented_interval
#print axioms Erdos345.reserved_good_allocation
#print axioms Erdos345.reserveCount_le_div
#print axioms Erdos345.reserveCount_le
#print axioms Erdos345.reserveCount_pos
#print axioms Erdos345.reservedBases_card
#print axioms Erdos345.reservedBases_nonempty
#print axioms Erdos345.reservedBases_positive
#print axioms Erdos345.reservedBases_above_unreserved
#print axioms Erdos345.reservedBases_disjoint
#print axioms Erdos345.reserveCount_lower
#print axioms Erdos345.reserved_power_lower
#print axioms Erdos345.eventually_reserve_large
#print axioms Erdos345.good_degrees_reserved_groups
#print axioms Erdos345.unit_rpow_tangent
#print axioms Erdos345.quarter_root_le_one_sub_inv
#print axioms Erdos345.exists_new_residue_endpoint
#print axioms Erdos345.residue_endpoint_card_growth
#print axioms Erdos345.natCast_eq_on_closed_interval
#print axioms Erdos345.naturalResidueImage_card_of_not_both_endpoints
#print axioms Erdos345.naturalResidueImage_card_closed_interval
#print axioms Erdos345.uniform_cell_error_le
#print axioms Erdos345.uniform_sampling_error_le
#print axioms Erdos345.flat_regularizedNorm_one
#print axioms Erdos345.log_topDenominator_one_le
#print axioms Erdos345.exists_large_rootOne_top_coefficient
#print axioms Erdos345.unit_geometric_sum_norm_le_length
#print axioms Erdos345.unit_norm_pow_sub_one_le
#print axioms Erdos345.root_of_unity_separation
#print axioms Erdos345.distinct_roots_ratio_separation
#print axioms Erdos345.cyclotomic_root_separation
#print axioms Erdos345.rounded_residual_count_bound
#print axioms Erdos345.exists_rounded_recurrence
#print axioms Erdos345.exists_flat_power_recurrence
#print axioms Erdos345.rounding_error_sine_bound
#print axioms Erdos345.sineEnergy_nonneg
#print axioms Erdos345.rounding_error_energy_le
#print axioms Erdos345.subsetCosineProduct_nonneg
#print axioms Erdos345.subsetCosineSum_nonneg
#print axioms Erdos345.mean_sampled_cosineProduct_le
#print axioms Erdos345.mean_sampled_cosineSum_le
#print axioms Erdos345.mean_label_cosine_decay_of_parameters
#print axioms Erdos345.sampledPowerSum_eq
#print axioms Erdos345.mean_sampledPowerSum
#print axioms Erdos345.sampledPowerSum_variance_le
#print axioms Erdos345.unreserved_span_mean_le
#print axioms Erdos345.unreserved_span_variance_le
#print axioms Erdos345.span_variance_ratio
#print axioms Erdos345.mean_large_span_le
#print axioms Erdos345.mean_bad_support_le_cosineMean
#print axioms Erdos345.mean_bad_support_of_parameters
#print axioms Erdos345.good_degrees_label_support_small
#print axioms Erdos345.rpow_inv_le_of_log_budget
#print axioms Erdos345.unreserved_small_numerator_energy_lower
#print axioms Erdos345.unreservedPopulation_card_le
#print axioms Erdos345.unreservedPopulation_nonempty_of_large
#print axioms Erdos345.sample_floor_lower
#print axioms Erdos345.sampling_fraction_lower
#print axioms Erdos345.log_fourierN_le
#print axioms Erdos345.fourier_collision_margin
#print axioms Erdos345.minimal_split_expansion_top_ne_zero
#print axioms Erdos345.minimal_cyclotomic_expansion_top_ne_zero
#print axioms Erdos345.sequenceAnnihilator_smul
#print axioms Erdos345.minimalAnnihilator_smul
#print axioms Erdos345.scale_finite_expansion
#print axioms Erdos345.primitiveTopCoefficient_scale
#print axioms Erdos345.norm_ge_exp_of_scaled
#print axioms Erdos345.exists_large_scaled_rootOne_top_coefficient
#print axioms Erdos345.shiftedChebyshev_expansion_top_coeff
#print axioms Erdos345.exists_supported_chebyshev_expansion
#print axioms Erdos345.exists_scaled_chebyshev_expansion
#print axioms Erdos345.shiftedChebyshev_topScale_norm_le
#print axioms Erdos345.scaled_chebyshev_top_norm_lower
#print axioms Erdos345.integer_multiple_minimal_cyclotomic
#print axioms Erdos345.complex_integer_multiple
#print axioms Erdos345.rational_error_rootOne_coefficient_height
#print axioms Erdos345.rational_error_rootOne_energy_lower
#print axioms Erdos345.rational_error_rootOne_multiplicity_bound
#print axioms Erdos345.scaledSineBlock_abs_le
#print axioms Erdos345.scaledSineBlock_nonneg
#print axioms Erdos345.scaledSineBlock_small_lower
#print axioms Erdos345.reduction_scaling_difference
#print axioms Erdos345.reductionModulus_scaling_difference
#print axioms Erdos345.sharp_interval_ratio
#print axioms Erdos345.sequenceShift_pow
#print axioms Erdos345.shiftAction_mul
#print axioms Erdos345.shiftAction_add
#print axioms Erdos345.shiftAction_sum
#print axioms Erdos345.shiftAction_sum_of_degree_lt
#print axioms Erdos345.shiftAction_zero_sequence
#print axioms Erdos345.shiftAction_X_sub_one
#print axioms Erdos345.shiftAction_difference_power
#print axioms Erdos345.shiftAction_map
#print axioms Erdos345.shiftAction_annihilates_polynomial
#print axioms Erdos345.X_sub_one_power_dvd_flatPolynomial
#print axioms Erdos345.flatPolynomial_annihilates
#print axioms Erdos345.iteratedDifference_power_vanish
#print axioms Erdos345.shiftAction_annihilates_of_difference
#print axioms Erdos345.flatPolynomial_annihilates_power
#print axioms Erdos345.translated_sum_le
#print axioms Erdos345.translated_sum_le_support
#print axioms Erdos345.sum_backward_prefix_le_support
#print axioms Erdos345.sum_backward_prefix_le
#print axioms Erdos345.exists_simultaneous_backward_averages
#print axioms Erdos345.exists_simultaneous_backward_averages_support
#print axioms Erdos345.prime_subset_products_dominate
#print axioms Erdos345.shifted_prime_requirement_below_scale
#print axioms Erdos345.shifted_prime_abundance_of_bombieri_vinogradov
#print axioms Erdos345.eventually_power_lt_exp_div_log
#print axioms Erdos345.doubled_logScale_le
#print axioms Erdos345.eventually_shifted_prime_requirement
#print axioms Erdos345.shifted_prime_abundance_of_fan_input
#print axioms Erdos345.shiftedPrimeProduct_pos
#print axioms Erdos345.prime_dvd_shiftedPrimeProduct
#print axioms Erdos345.fixedDifferenceDivisor_dvd_shiftedPrimeBound
#print axioms Erdos345.reductionModulus_dvd_shiftedPrimeBound
#print axioms Erdos345.gcd_classes_disjoint
#print axioms Erdos345.divisor_prime_pairs_disjoint
#print axioms Erdos345.selected_divisor_pairs_card_lower
#print axioms Erdos345.selected_divisor_pairs_valid
#print axioms Erdos345.shifted_prime_spike_of_progression_counts
#print axioms Erdos345.gcd_class_embedding
#print axioms Erdos345.gcd_class_card_lower
#print axioms Erdos345.shifted_product_fiber_card_le
#print axioms Erdos345.shifted_prime_spike_of_pair_count
#print axioms Erdos345.nat_quotient_half_lower
#print axioms Erdos345.shifted_prime_spike_of_many_progressions
#print axioms Erdos345.exists_simultaneous_bound
#print axioms Erdos345.exists_simultaneous_weighted_bound
#print axioms Erdos345.sum_odd_reals
#print axioms Erdos345.oddSineSum_abs_le_square_mul
#print axioms Erdos345.scaledSineBlock_abs_linear
#print axioms Erdos345.abs_sine_round_shift
#print axioms Erdos345.two_distance_le_abs_sine
#print axioms Erdos345.scaledSineBlock_abs_le_phaseDistance
#print axioms Erdos345.scaledSineBlock_abs_le_phaseBin
#print axioms Erdos345.sine_square_perturbation
#print axioms Erdos345.sineEnergy_perturbation
#print axioms Erdos345.power_phase_squared_distance_sum_le
#print axioms Erdos345.power_sineEnergy_perturbation
#print axioms Erdos345.sineEnergy_mono
#print axioms Erdos345.power_modulus_one_of_small_heights
#print axioms Erdos345.rational_phase_window_modulus_one
#print axioms Erdos345.exact_reduction_step_modulus_one
#print axioms Erdos345.uniform_scaled_energy_lower
#print axioms Erdos345.small_numerator_energy_lower
#print axioms Erdos345.mem_smallNumeratorFrequencies
#print axioms Erdos345.card_smallNumeratorFrequencies_le
#print axioms Erdos345.near_integer_implies_small_numerator
#print axioms Erdos345.nonzero_integerArcs_subset_smallNumerators
#print axioms Erdos345.card_nonzero_integerArcs_le
#print axioms Erdos345.sorted_128_sumset_interval
#print axioms Erdos345.paired_span_min_bound
#print axioms Erdos345.sorted_prefix_density
#print axioms Erdos345.sorted_prefix_growth_step
#print axioms Erdos345.sorted_prefix_card_lower
#print axioms Erdos345.degree_le_fourierN
#print axioms Erdos345.eventually_span_failure_small
#print axioms Erdos345.stabilized_sumset_fiber_bound
#print axioms Erdos345.stabilizer_natCard
#print axioms Erdos345.stabilizer_quotient_saturation_card
#print axioms Erdos345.stabilizer_quotient_self_card
#print axioms Erdos345.stabilizer_quotient_mem_image
#print axioms Erdos345.phaseWindows_pairwise_disjoint
#print axioms Erdos345.stacked_naturalWindow_energy_lower
#print axioms Erdos345.thresholds_upward
#print axioms Erdos345.threshold_le_of_isLeast
#print axioms Erdos345.least_threshold_unique
#print axioms Erdos345.isLeast_thresholds_one
#print axioms Erdos345.eventually_monotone_of_finite_drops
#print axioms Erdos345.infinite_drops_of_late_inversions
#print axioms Erdos345.infinite_positive_drops_of_late_inversions
#print axioms Erdos345.intended_of_thresholds_and_late_inversions
#print axioms Erdos345.representedUpTo_represented
#print axioms Erdos345.representedUpTo_mono
#print axioms Erdos345.representedUpTo_add_next
#print axioms Erdos345.representedInterval_add_next
#print axioms Erdos345.succ_pow_mul_sub_le
#print axioms Erdos345.next_power_le_twice
#print axioms Erdos345.tailLength_zero
#print axioms Erdos345.tailLength_succ
#print axioms Erdos345.tailInterval_invariant
#print axioms Erdos345.threshold_of_representedInterval
#print axioms Erdos345.exists_least_threshold_of_threshold
#print axioms Erdos345.exists_least_threshold_of_representedInterval
#print axioms Erdos345.log_threshold_envelope_le
#print axioms Erdos345.logScale_mono
#print axioms Erdos345.log_threshold_envelope_le_at_larger
#print axioms Erdos345.topDenominator_pos
#print axioms Erdos345.scaled_log_topDenominator_le
#print axioms Erdos345.log_topDenominator_le
#print axioms Erdos345.initialCosineSum_identity
#print axioms Erdos345.sine_le_truncatedCosine
#print axioms Erdos345.theta_le_four_sin_half
#print axioms Erdos345.five_period_two_power
#print axioms Erdos345.twoPowerDilationPeriod_pos
#print axioms Erdos345.twoPowerDilationPeriod_period
#print axioms Erdos345.twoAdic_cyclotomic_multiplicity_bound
#print axioms Erdos345.twoAdic_cyclotomic_multiplicity_log_bound
#print axioms Erdos345.shiftedChebyshevSeries_eq
#print axioms Erdos345.integral_cos_sine_substitution
#print axioms Erdos345.shiftedChebyshevSeries_integral_norm_sq
#print axioms Erdos345.shiftedChebyshevSeries_continuous_energy_lower
#print axioms Erdos345.population_energy_gt_of_empty
#print axioms Erdos345.uniform_energy_of_parameters
#print axioms Erdos345.good_degrees_uniform_energy
#print axioms Erdos345.isCoprime_linear_of_eval_unit
#print axioms Erdos345.cancel_unit_factor_on_polynomial_sequence
#print axioms Erdos345.remove_unit_factor_from_power_annihilator
#print axioms Erdos345.coarse_unreserved_frequency_bound
#print axioms Erdos345.unreserved_collision_le_exp_margin
#print axioms Erdos345.mem_unreservedPopulation
#print axioms Erdos345.unreservedEndpoint_cast
#print axioms Erdos345.unreservedEndpoint_ge_three_quarters
#print axioms Erdos345.quarter_root_endpoint_le
#print axioms Erdos345.unreservedPopulation_contains_band
#print axioms Erdos345.unreservedPopulation_nonempty
#print axioms Erdos345.unreservedPopulation_missing_le
#print axioms Erdos345.valuationWindow_eq
#print axioms Erdos345.factorial_valuation_scaled_le
#print axioms Erdos345.valuationWindow_scaled_le
#print axioms Erdos345.valuationWindow_real_le
#print axioms Erdos345.multipleWindow_card_le
#print axioms Erdos345.multipleWindow_card_scaled_le
#print axioms Erdos345.rootOneWindow_le
#print axioms Erdos345.rootOneWindow_scaled_le
#print axioms Erdos345.rootOneWindow_real_le
#print axioms Erdos345.integral_split_three
#print axioms Erdos345.sin_lower_on_trimmed_interval
#print axioms Erdos345.sine_weighted_integral_lower
#print axioms Erdos345.cosineSeries_sine_energy_lower
#print axioms Erdos345.windowHeightBudget_antitone_length
#print axioms Erdos345.windowHeightBudget_le_explicit
#print axioms Erdos345.windowHeightBudget_le_log_envelope
#print axioms Erdos345.windowHeightBudget_le_linear_degree
#print axioms Erdos345.rational_phase_window_reduction
#print axioms Erdos345.translated_phase_identity
#print axioms Erdos345.translated_flat_recurrence
#print axioms Erdos345.exists_integer_error_multiple
#print axioms Erdos345.exists_flat_error_window_multiplicity_bounds
#print axioms Erdos345.exists_rational_phase_height_bounds
#print axioms Erdos345.centerWindowLogConstant_nonneg
#print axioms Erdos345.log_succ_le_logScale
#print axioms Erdos345.log_sufficientCenterWindow_le
#print axioms Erdos345.windowHeightBudget_nonneg
#print axioms Erdos345.weighted_primePower_height_bound
#print axioms Erdos345.height_bounds_to_uniform
#print axioms Erdos345.flat_multiplicity_le_power_degree
#print axioms Erdos345.exists_block_avoiding
#print axioms Erdos345.real_div_badcount_lower
#print axioms Erdos345.exists_zero_run_of_badcount
#print axioms Erdos345.exists_zero_run_of_energy
#print axioms Erdos345.exists_recurrence_zero_run
#print axioms Finset.Nonempty.addStab
#print axioms Finset.Nonempty.addStab_nontrivial
#print axioms Finset.Nonempty.mulStab
#print axioms Finset.Nonempty.mulStab_nontrivial
#print axioms Finset.Nonempty.of_addStab
#print axioms Finset.Nonempty.of_mulStab
#print axioms Finset.Nonempty.of_mulStab._simp_1_1
#print axioms Finset.Nonempty.of_mulStab._simp_1_2
#print axioms Finset.Nonempty.one_mem_mulStab
#print axioms Finset.Nonempty.zero_mem_addStab
#print axioms Finset.addStab.eq_1
#print axioms Finset.addStab_add
#print axioms Finset.addStab_add_addStab
#print axioms Finset.addStab_add_ssubset_addStab
#print axioms Finset.addStab_empty
#print axioms Finset.addStab_idem
#print axioms Finset.addStab_image_coe_quotient
#print axioms Finset.addStab_nonempty
#print axioms Finset.addStab_nonempty._simp_1
#print axioms Finset.addStab_quotient_addCommute_addSubgroup
#print axioms Finset.addStab_singleton
#print axioms Finset.addStab_subset_sub
#print axioms Finset.addStab_subset_sub_left
#print axioms Finset.addStab_subset_sub_right
#print axioms Finset.addStab_union
#print axioms Finset.addStab_vadd
#print axioms Finset.addSubgroup_add_card_eq_add_of_add_stab_subset
#print axioms Finset.add_addStab
#print axioms Finset.add_addStab_add_add_add_addStab_add
#print axioms Finset.add_aux1
#print axioms Finset.add_aux1._abel_1_1
#print axioms Finset.add_kneser
#print axioms Finset.add_strict_kneser
#print axioms Finset.add_subset_left
#print axioms Finset.add_subset_left_iff
#print axioms Finset.add_subset_right
#print axioms Finset.add_subset_right_iff
#print axioms Finset.card_addStab_add_card_image_coe
#print axioms Finset.card_addStab_add_card_image_coe'
#print axioms Finset.card_addStab_dvd_card
#print axioms Finset.card_addStab_dvd_card_addStab
#print axioms Finset.card_addStab_dvd_card_add_addStab
#print axioms Finset.card_addStab_eq_zero
#print axioms Finset.card_addStab_eq_zero._simp_1
#print axioms Finset.card_addStab_le_card
#print axioms Finset.card_add_card_eq_addStab_card_add_coe
#print axioms Finset.card_mulStab_dvd_card
#print axioms Finset.card_mulStab_dvd_card_mulStab
#print axioms Finset.card_mulStab_dvd_card_mul_mulStab
#print axioms Finset.card_mulStab_eq_one
#print axioms Finset.card_mulStab_eq_one._simp_2
#print axioms Finset.card_mulStab_le_card
#print axioms Finset.card_mulStab_mul_card_image_coe
#print axioms Finset.card_mulStab_mul_card_image_coe'
#print axioms Finset.card_mulStab_mul_card_image_coe'._simp_1_1
#print axioms Finset.card_mulStab_mul_card_image_coe'._simp_1_2
#print axioms Finset.card_mulStab_mul_card_image_coe'._simp_1_3
#print axioms Finset.card_mulStab_mul_card_image_coe'._simp_1_4
#print axioms Finset.card_mulStab_mul_card_image_coe'._simp_1_5
#print axioms Finset.card_mulStab_mul_card_image_coe'._simp_1_6
#print axioms Finset.card_mul_card_eq_mulStab_card_mul_coe
#print axioms Finset.coe_addStab
#print axioms Finset.coe_mulStab
#print axioms Finset.disjoint_add_sub_card_le
#print axioms Finset.disjoint_mul_sub_card_le
#print axioms Finset.disjoint_mul_sub_card_le._simp_1_1
#print axioms Finset.disjoint_smul_finset_mulStab_mul_mulStab
#print axioms Finset.disjoint_smul_finset_mulStab_mul_mulStab._simp_1_1
#print axioms Finset.disjoint_smul_finset_mulStab_mul_mulStab._simp_1_2
#print axioms Finset.disjoint_smul_finset_mulStab_mul_mulStab._simp_1_3
#print axioms Finset.disjoint_smul_finset_mulStab_mul_mulStab._simp_1_4
#print axioms Finset.disjoint_smul_mulStab
#print axioms Finset.disjoint_smul_mulStab._simp_1_1
#print axioms Finset.disjoint_vadd_addStab
#print axioms Finset.disjoint_vadd_finset_addStab_add_addStab
#print axioms Finset.instDecidablePredMemAddSubgroupStabilizerSetCoe_erdos345._proof_1
#print axioms Finset.instDecidablePredMemAddSubgroupStabilizerSetCoe_erdos345.eq_1
#print axioms Finset.instDecidablePredMemSubgroupStabilizerSetCoe_erdos345._proof_1
#print axioms Finset.instDecidablePredMemSubgroupStabilizerSetCoe_erdos345.eq_1
#print axioms Finset.inter_addStab_subset_addStab_union
#print axioms Finset.inter_add_sub_card_le
#print axioms Finset.inter_mulStab_subset_mulStab_union
#print axioms Finset.inter_mul_sub_card_le
#print axioms Finset.inter_mul_sub_card_le._simp_1_1
#print axioms Finset.mem_addStab
#print axioms Finset.mem_addStab'
#print axioms Finset.mem_addStab._simp_1
#print axioms Finset.mem_addStab_iff_subset_vadd_finset
#print axioms Finset.mem_addStab_iff_vadd_finset_subset
#print axioms Finset.mem_mulStab
#print axioms Finset.mem_mulStab'
#print axioms Finset.mem_mulStab._simp_2
#print axioms Finset.mem_mulStab_iff_smul_finset_subset
#print axioms Finset.mem_mulStab_iff_subset_smul_finset
#print axioms Finset.mulStab.eq_1
#print axioms Finset.mulStab_empty
#print axioms Finset.mulStab_idem
#print axioms Finset.mulStab_image_coe_quotient
#print axioms Finset.mulStab_image_coe_quotient._simp_1_1
#print axioms Finset.mulStab_mul
#print axioms Finset.mulStab_mul._simp_1_1
#print axioms Finset.mulStab_mul_mulStab
#print axioms Finset.mulStab_mul_mulStab._simp_1_1
#print axioms Finset.mulStab_mul_mulStab._simp_1_2
#print axioms Finset.mulStab_mul_mulStab._simp_1_3
#print axioms Finset.mulStab_mul_ssubset_mulStab
#print axioms Finset.mulStab_mul_ssubset_mulStab._simp_1_1
#print axioms Finset.mulStab_mul_ssubset_mulStab._simp_1_2
#print axioms Finset.mulStab_nonempty
#print axioms Finset.mulStab_nonempty._simp_2
#print axioms Finset.mulStab_quotient_commute_subgroup
#print axioms Finset.mulStab_quotient_commute_subgroup._simp_1_2
#print axioms Finset.mulStab_quotient_commute_subgroup._simp_1_3
#print axioms Finset.mulStab_quotient_commute_subgroup._simp_1_4
#print axioms Finset.mulStab_singleton
#print axioms Finset.mulStab_smul
#print axioms Finset.mulStab_subset_div
#print axioms Finset.mulStab_subset_div_left
#print axioms Finset.mulStab_subset_div_right
#print axioms Finset.mulStab_union
#print axioms Finset.mulStab_union._simp_1_1
#print axioms Finset.mulStab_union._simp_1_2
#print axioms Finset.mulStab_union._simp_1_3
#print axioms Finset.mul_aux1
#print axioms Finset.mul_aux1._abel_1_1
#print axioms Finset.mul_kneser
#print axioms Finset.mul_kneser._simp_1_1
#print axioms Finset.mul_kneser._simp_1_10
#print axioms Finset.mul_kneser._simp_1_11
#print axioms Finset.mul_kneser._simp_1_12
#print axioms Finset.mul_kneser._simp_1_13
#print axioms Finset.mul_kneser._simp_1_2
#print axioms Finset.mul_kneser._simp_1_3
#print axioms Finset.mul_kneser._simp_1_4
#print axioms Finset.mul_kneser._simp_1_5
#print axioms Finset.mul_kneser._simp_1_6
#print axioms Finset.mul_kneser._simp_1_7
#print axioms Finset.mul_kneser._simp_1_8
#print axioms Finset.mul_kneser._simp_1_9
#print axioms Finset.mul_mulStab
#print axioms Finset.mul_mulStab_mul_mul_mul_mulStab_mul
#print axioms Finset.mul_strict_kneser
#print axioms Finset.mul_subset_left
#print axioms Finset.mul_subset_left_iff
#print axioms Finset.mul_subset_right
#print axioms Finset.mul_subset_right_iff
#print axioms Finset.mul_subset_right_iff._simp_1_1
#print axioms Finset.mul_subset_right_iff._simp_1_2
#print axioms Finset.mul_subset_right_iff._simp_1_3
#print axioms Finset.mul_subset_right_iff._simp_1_4
#print axioms Finset.one_mem_mulStab
#print axioms Finset.one_mem_mulStab._simp_2
#print axioms Finset.pairwiseDisjoint_smul_finset_mulStab
#print axioms Finset.pairwiseDisjoint_smul_finset_mulStab._simp_1_1
#print axioms Finset.pairwiseDisjoint_vadd_finset_addStab
#print axioms Finset.preimage_image_quotientMk_addStabilizer
#print axioms Finset.preimage_image_quotientMk_mulStabilizer
#print axioms Finset.preimage_image_quotientMk_stabilizer_eq_add_addStab
#print axioms Finset.preimage_image_quotientMk_stabilizer_eq_mul_mulStab
#print axioms Finset.smul_finset_mulStab_subset
#print axioms Finset.smul_mulStab
#print axioms Finset.subgroup_mul_card_eq_mul_of_mul_stab_subset
#print axioms Finset.subgroup_mul_card_eq_mul_of_mul_stab_subset._simp_1_1
#print axioms Finset.subset_addStab_add_left
#print axioms Finset.subset_addStab_add_right
#print axioms Finset.subset_mulStab_mul_left
#print axioms Finset.subset_mulStab_mul_left._simp_1_1
#print axioms Finset.subset_mulStab_mul_right
#print axioms Finset.vadd_addStab
#print axioms Finset.vadd_finset_addStab_subset
#print axioms Finset.zero_mem_addStab
#print axioms Finset.zero_mem_addStab._simp_1
#print axioms Set.fintypeImage._proof_1._to_additive_1
#print axioms OAI.LargePrimeGaps.siegelWalfisz
#print axioms OAI.LargePrimeGaps.bombieriVinogradov
