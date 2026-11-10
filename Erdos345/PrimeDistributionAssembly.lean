import Erdos345.BelovAnalyticInput
import Erdos345.ShiftedPrimeAbundance

namespace Erdos345

/-- The exact original target follows from the classical prime-distribution theorem.
This is a conditional interface until that theorem's full local proof is checked. -/
theorem intended_of_bombieri_vinogradov (hbv : OAI.LargePrimeGaps.BombieriVinogradov) :
    IntendedStatement :=
  intended_of_many_shifted_primes (shifted_prime_abundance_of_bombieri_vinogradov hbv)

end Erdos345
