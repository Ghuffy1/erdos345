# Relationship between the paper and the formal proof

The paper and Lean prove the same final infinitude statement. The paper's main
result is Theorem 1.1 on p. 1, with the concluding proof on p. 14. The formal
target is `Erdos345.erdos_345` in `Erdos345/Conclusion.lean`.

The Lean development uses alternate intermediate arguments. Its successful
verification must not be described as checking every sentence of the PDF.

| Topic | Paper | Formal development |
| --- | --- | --- |
| Existence of finite thresholds | Cites Kim's completeness result | Constructs completeness by a radix/Prouhet argument |
| Flat trigonometric input | Uses the Belov–Konyagin theorem | Proves a suitable explicit cosine construction through a global sine inequality |
| Mixed-frequency estimate | Legendre-polynomial calculation | Shifted Chebyshev polynomials and discrete sampling |
| Dilation | Characteristic-polynomial presentation | Explicit integral annihilator of dilation |
| Infinitely many large lower bounds | Quantitative Fan–Pollack shifted-prime theorem | Weaker sufficient shifted-prime abundance, proved from the checked Bombieri–Vinogradov development |

Both routes combine suitable upper bounds on degrees in every sufficiently large
dyadic interval with large lower bounds at arbitrarily large degrees. Eventual
monotonicity would contradict these bounds, so adjacent strict decreases occur
infinitely often. The stronger unused `FanPollackInput` interface is not an
assumption of the final Lean theorem.

The mathematical paper contains only its proof, scholarly references and AI
acknowledgment. Reproduction and technical verification materials are kept here.
