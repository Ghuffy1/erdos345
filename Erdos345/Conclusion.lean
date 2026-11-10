import Erdos345.PrimeDistributionAssembly
import OAI.NumberTheory.PrimeGaps.Main

namespace Erdos345

/-- The weak shifted-prime abundance needed by the threshold comparison,
now supplied by the checked classical prime-distribution theorem. -/
theorem shifted_prime_abundance_proved :
    ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ 2 ≤ n ∧
      32768 * logScale (2 * (n + 1)) ^ 8 ≤ (shiftedPrimes n).card :=
  shifted_prime_abundance_of_bombieri_vinogradov OAI.LargePrimeGaps.bombieriVinogradov

/-- Infinitely many positive exponents have a strict adjacent decrease of
the least threshold for finite sums of distinct positive powers. -/
theorem erdos_345 : IntendedStatement :=
  intended_of_many_shifted_primes shifted_prime_abundance_proved

end Erdos345
