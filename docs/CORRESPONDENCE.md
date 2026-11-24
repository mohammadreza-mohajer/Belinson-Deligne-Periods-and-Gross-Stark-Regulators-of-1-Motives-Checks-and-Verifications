# Correspondence with the manuscript

Page numbers refer to the bundled PDF. Links open the exact source line. Each entry describes the scope of its Lean declarations and names the argument that still requires a mathematical input. The arithmetic constructions are stated in the accompanying manuscript.

## Theorem 2.1. Inertia invariants and the Euler polynomial

[Manuscript, p. 4](../paper/manuscript.pdf#page=4) · [LaTeX statement](../paper/manuscript.tex#L285)

Block determinant and quotient correction, including vanishing denominators. An injective tame map preserves the valuation kernel.

[BD.Euler.blockFactor](../BD/Euler.lean#L13), [BD.Euler.constantFactor](../BD/Euler.lean#L21), [BD.Euler.correction](../BD/Euler.lean#L29), [BD.Realizations.inertiaKernel](../BD/Realizations.lean#L12)

**Arithmetic or analytic scope.** Construction of the semiabelian valuation, Kummer restriction, duality, inertia exactness, comparison with geometric Frobenius.

## Example 2.2. Quadratic twist at an inert or ramified prime

[Manuscript, p. 5](../paper/manuscript.pdf#page=5) · [LaTeX statement](../paper/manuscript.tex#L382)

Euler determinant of the sign line. The zero-dimensional determinant is covered by the general block formula.

[BD.Euler.inertSignFactor](../BD/Euler.lean#L32), [BD.Euler.constantFactor](../BD/Euler.lean#L21)

**Arithmetic or analytic scope.** Descent of the quadratic twist and identification of its actual inertia module.

## Proposition 2.3. Real comparison defect

[Manuscript, p. 6](../paper/manuscript.pdf#page=6) · [LaTeX statement](../paper/manuscript.tex#L414)

Range after cancelling an invertible abelian diagonal map, and the dimension of a kernel.

[BD.Realizations.splitRange](../BD/Realizations.lean#L39), [BD.Linear.projectionLoss](../BD/Linear.lean#L48)

**Arithmetic or analytic scope.** The Betti and de Rham comparison maps, real plus parts, and the exact sequence for a general semiabelian extension.

## Theorem 3.1. Relative norm tori and the leading term

[Manuscript, p. 7](../paper/manuscript.pdf#page=7) · [LaTeX statement](../paper/manuscript.tex#L521)

Constructive lifting in the relative divisor kernel, product of comparison determinants and formal Taylor orders and coefficients.

[BD.Linear.relativeLift](../BD/Linear.lean#L15), [BD.Linear.extensionDet](../BD/Linear.lean#L54), [BD.Linear.periodProduct](../BD/Linear.lean#L67), [BD.Series.complexLeading](../BD/Series.lean#L65), [BD.Series.finiteProduct](../BD/Series.lean#L43), [BD.Series.exactOrder](../BD/Series.lean#L23)

**Arithmetic or analytic scope.** Dirichlet units, the class group, the integral comparison lattices and the complex analytic class number formula.

## Remark 3.2. Comparison with the graded Euler product

[Manuscript, p. 8](../paper/manuscript.pdf#page=8) · [LaTeX statement](../paper/manuscript.tex#L636)

Effect of adjoining finite vanishing factors once their expansions have been identified.

[BD.Euler.correction](../BD/Euler.lean#L29), [BD.Series.term_coeff](../BD/Series.lean#L14)

**Arithmetic or analytic scope.** Arithmetic interpretation of the augmented map and its relationship with Scholl’s comparison.

## Theorem 3.3. Arbitrary critical lattice

[Manuscript, p. 8](../paper/manuscript.pdf#page=8) · [LaTeX statement](../paper/manuscript.tex#L663)

The rank inequality and equality of kernels at equal dimension, cancellation of split poles and the determinant step.

[BD.Linear.criticalProjection](../BD/Linear.lean#L28), [BD.Series.splitCancellation](../BD/Series.lean#L55), [BD.Series.exactOrder](../BD/Series.lean#L23), [BD.Linear.extensionDet](../BD/Linear.lean#L54)

**Arithmetic or analytic scope.** Construction of the split projection from actual valuations, saturation by relative units, real logarithmic periods and the rationality claim for the motive.

## Theorem 4.1. Relative p-adic residue

[Manuscript, p. 10](../paper/manuscript.pdf#page=10) · [LaTeX statement](../paper/manuscript.tex#L798)

Cancellation of Euler factors in the quotient, valid with zero numerator, and determinant multiplicativity.

[BD.Linear.residueQuotient](../BD/Linear.lean#L76), [BD.Linear.periodProduct](../BD/Linear.lean#L67), [BD.Linear.extensionDet](../BD/Linear.lean#L54)

**Arithmetic or analytic scope.** Colmez’s formula, p-adic zeta germs, normalized regulators, Leopoldt’s condition and Brumer’s abelian case.

## Corollary 4.2. Adding primes away from p

[Manuscript, p. 11](../paper/manuscript.pdf#page=11) · [LaTeX statement](../paper/manuscript.tex#L876)

Powers of finite Taylor factors, their expected coefficient and the nonvanishing criterion.

[BD.Series.finiteProduct](../BD/Series.lean#L43), [BD.Series.power](../BD/Series.lean#L37), [BD.Series.exactOrder](../BD/Series.lean#L23)

**Arithmetic or analytic scope.** Construction of the local logarithm, identification of each cyclotomic Euler factor and its nonzero slope.

## Corollary 4.3. Split pole cancellation at p

[Manuscript, p. 11](../paper/manuscript.pdf#page=11) · [LaTeX statement](../paper/manuscript.tex#L917)

Pole cancellation and the critical rank bound for the finite model.

[BD.Series.splitCancellation](../BD/Series.lean#L55), [BD.Linear.criticalProjection](../BD/Linear.lean#L28), [BD.Series.exactOrder](../BD/Series.lean#L23), [BD.Linear.residueQuotient](../BD/Linear.lean#L76)

**Arithmetic or analytic scope.** The relative unit comparison, Leopoldt hypotheses and identification of the reduced p-adic zeta quotient.

## Theorem 4.4. Algebraicity versus the global unit condition

[Manuscript, p. 12](../paper/manuscript.pdf#page=12) · [LaTeX statement](../paper/manuscript.tex#L968)

Valuation and nonzero unit logarithm force both coefficients in a rational relation to vanish, once the multiplicative-to-additive reduction is given.

[BD.Characters.quadraticIndependence](../BD/Characters.lean#L52), [BD.Realizations.oddLogKernel](../BD/Realizations.lean#L19)

**Arithmetic or analytic scope.** The rational kernel of a local logarithm, classification of the units, Baker’s theorem and the Baker–Brumer theorem on linear independence of logarithms over algebraic coefficients.

## Example 4.5. The real quadratic example at 11

[Manuscript, p. 13](../paper/manuscript.pdf#page=13) · [LaTeX statement](../paper/manuscript.tex#L1017)

Exact norm numerator and the two roots of 5 modulo 11.

[BD.Arithmetic.quadraticNorms](../BD/Arithmetic.lean#L43), [BD.Arithmetic.splitAtEleven](../BD/Arithmetic.lean#L44)

**Arithmetic or analytic scope.** Identification of the two prime ideals, valuations, period nonvanishing and the graded special-value conclusion.

## Lemma 5.1. Single-embedding logarithm on the odd part

[Manuscript, p. 14](../paper/manuscript.pdf#page=14) · [LaTeX statement](../paper/manuscript.tex#L1107)

Triviality of the intersection of odd vectors with an even logarithm kernel, and the abstract affine-injectivity implication.

[BD.Realizations.oddLogKernel](../BD/Realizations.lean#L19), [BD.Realizations.affineEvaluation](../BD/Realizations.lean#L25)

**Arithmetic or analytic scope.** Local logarithm kernel, Baker–Brumer and the p-adic analytic subgroup theorem for the additive coordinate.

## Proposition 5.2. Simultaneous affine independence of regulator entries

[Manuscript, p. 14](../paper/manuscript.pdf#page=14) · [LaTeX statement](../paper/manuscript.tex#L1150)

Affine separation when the image of an injective logarithm meets the base scalars trivially.

[BD.Realizations.affineEvaluation](../BD/Realizations.lean#L25), [BD.Characters.affineTrace](../BD/Characters.lean#L26)

**Arithmetic or analytic scope.** Nondegeneracy of the compressed group-algebra pairing and identification of its evaluation with an actual norm logarithm.

## Proposition 5.3. Restriction and residue-degree scaling

[Manuscript, p. 15](../paper/manuscript.pdf#page=15) · [LaTeX statement](../paper/manuscript.tex#L1234)

The inverse order for a row-scaled valuation matrix, branch translation and conjugacy under a compatible basis change.

[BD.Matrices.normalizeValuations](../BD/Matrices.lean#L33), [BD.Matrices.descentConjugacy](../BD/Matrices.lean#L41), [BD.Matrices.determinantConjugacy](../BD/Matrices.lean#L44), [BD.Matrices.branchShift](../BD/Matrices.lean#L28)

**Arithmetic or analytic scope.** Norms of local-field extensions, character projection of the p-unit groups and the field-enlargement diagram.

## Theorem 5.4. Dual lifts and every principal minor

[Manuscript, p. 16](../paper/manuscript.pdf#page=16) · [LaTeX statement](../paper/manuscript.tex#L1323)

The graph of the obstruction, the singularity criterion and the multivariate determinant expansion in every finite rank, including zero.

[BD.Matrices.liftGraph](../BD/Matrices.lean#L14), [BD.Matrices.existsLift_iff_det](../BD/Matrices.lean#L100), [BD.Matrices.principalMinorExpansion](../BD/Matrices.lean#L84), [BD.Applications.grossExactIffNoPureLift](../BD/Applications.lean#L12)

**Arithmetic or analytic scope.** The local reciprocity convention and the identification of the cohomological connecting map with the obstruction row by cup product and Shapiro.

## Theorem 6.1. Common Artin blocks

[Manuscript, p. 17](../paper/manuscript.pdf#page=17) · [LaTeX statement](../paper/manuscript.tex#L1432)

For an arbitrary finite collection of blocks of different dimensions, the characteristic polynomial and determinant are products with the required multiplicities. This includes multiplicity zero. Determinants are invariant under conjugation.

[BD.Linear.extensionCharpoly](../BD/Linear.lean#L58), [BD.Matrices.determinantConjugacy](../BD/Matrices.lean#L44), [BD.Characters.monomialProduct](../BD/Characters.lean#L12), [BD.Blocks.repeatedCharpoly](../BD/Blocks.lean#L78), [BD.Blocks.repeatedDeterminant](../BD/Blocks.lean#L33)

**Arithmetic or analytic scope.** Representation-theoretic decomposition of the odd permutation module and the dimension of the entry span for actual p-units.

## Corollary 6.2. Relations among traces

[Manuscript, p. 18](../paper/manuscript.pdf#page=18) · [LaTeX statement](../paper/manuscript.tex#L1472)

The trace of repeated heterogeneous blocks is the multiplicity-weighted sum. Given independent block traces, affine trace relations are equivalent to the linear equations on multiplicities.

[BD.Characters.affineTrace](../BD/Characters.lean#L26), [BD.Blocks.repeatedTrace](../BD/Blocks.lean#L40)

**Arithmetic or analytic scope.** The independence and identification of the actual block traces.

## Corollary 6.3. Bound on the space of pure logarithm lifts

[Manuscript, p. 18](../paper/manuscript.pdf#page=18) · [LaTeX statement](../paper/manuscript.tex#L1491)

Weighted sum of the blockwise nullity bounds and the obstruction graph.

[BD.Characters.liftDimensionBound](../BD/Characters.lean#L40), [BD.Matrices.liftGraph](../BD/Matrices.lean#L14)

**Arithmetic or analytic scope.** Maksoud’s rank theorem and identification of the nullity of the actual lifting space with the sum of the block nullities.

## Theorem 6.4. Normalized Gross–Stark coefficients

[Manuscript, p. 18](../paper/manuscript.pdf#page=18) · [LaTeX statement](../paper/manuscript.tex#L1560)

Normalized coefficient extraction, the equivalence of exact order and absence of a pure logarithm lift, and the product formula for determinants with arbitrary block sizes and multiplicities.

[BD.Applications.grossCoefficient](../BD/Applications.lean#L28), [BD.Applications.grossExactIffNoPureLift](../BD/Applications.lean#L12), [BD.Series.exactOrder](../BD/Series.lean#L23), [BD.Characters.monomialProduct](../BD/Characters.lean#L12), [BD.Blocks.repeatedDeterminant](../BD/Blocks.lean#L33)

**Arithmetic or analytic scope.** Gross–Stark vanishing and the Dasgupta–Kakde–Ventullo formula for the cyclotomic Taylor series. Nonvanishing of one-dimensional arithmetic blocks.

## Remark 6.5. Higher-rank nonvanishing

[Manuscript, p. 19](../paper/manuscript.pdf#page=19) · [LaTeX statement](../paper/manuscript.tex#L1586)

Exact-order criterion once the expected coefficient is identified.

[BD.Applications.grossExactIffNoPureLift](../BD/Applications.lean#L12), [BD.Series.exactOrder](../BD/Series.lean#L23)

**Arithmetic or analytic scope.** Gross–Kuz’min nonvanishing and its known rank-one cases. The remark makes no new unconditional higher-rank nonvanishing assertion.

## Corollary 6.6. Order-one coefficient relations

[Manuscript, p. 19](../paper/manuscript.pdf#page=19) · [LaTeX statement](../paper/manuscript.tex#L1599)

Compression of affine relations after repetition of the same independent coordinate.

[BD.Characters.affineTrace](../BD/Characters.lean#L26), [BD.Characters.coefficientBinomial](../BD/Characters.lean#L19)

**Arithmetic or analytic scope.** Rank-one block identification, arithmetic independence, transcendence of a coefficient and of ratios of differently labelled coefficients.

## Corollary 6.7. Field generated by a coefficient

[Manuscript, p. 19](../paper/manuscript.pdf#page=19) · [LaTeX statement](../paper/manuscript.tex#L1623)

The stabilizer criterion follows from injective equivariant labels. In any finite Galois extension, the equality of stabilizers implies equality of the field generated by the trace and the field generated by the character values.

[BD.Characters.stabilizerCriterion](../BD/Characters.lean#L45), [BD.CoefficientField.fixesGenerators](../BD/CoefficientField.lean#L10), [BD.CoefficientField.fieldOfTrace](../BD/CoefficientField.lean#L23)

**Arithmetic or analytic scope.** Identification of the ambient arithmetic splitting field, the equivariant labelling of the actual regulator traces, and the reduction of the coefficient to the stated trace.

## Theorem 6.8. Ideal of numerical relations

[Manuscript, p. 19](../paper/manuscript.pdf#page=19) · [LaTeX statement](../paper/manuscript.tex#L1661)

Unconditional exponent binomials, algebraic independence of determinants of disjoint generic blocks of positive size, the full exponent-fiber ideal under an injective specialization, and equivalence of monomial independence with injectivity of the exponent map.

[BD.Characters.coefficientBinomial](../BD/Characters.lean#L19), [BD.GenericDet.independentDeterminants](../BD/GenericDet.lean#L43), [BD.Relations.kernel_eq_fiberIdeal](../BD/Relations.lean#L22), [BD.Relations.realized_kernel](../BD/Relations.lean#L60), [BD.Monomials.independence](../BD/Monomials.lean#L31), [BD.Monomials.genericBlockIndependence](../BD/Monomials.lean#L44)

**Arithmetic or analytic scope.** Weak p-adic Schanuel, independence of the arithmetic regulator entries and the Laurent fraction-field transcendence-degree argument.

## Theorem 7.1. Relations among cyclotomic germs

[Manuscript, p. 20](../paper/manuscript.pdf#page=20) · [LaTeX statement](../paper/manuscript.tex#L1749)

Descent for any family of algebraic rows, factorial dominance, bounds for a summable tail, elimination at an isolated frequency, separation of character tuples, the full fiber-binomial ideal, and the independence criterion for the formal monomials.

[BD.Interpolation.descendRows](../BD/Interpolation.lean#L15), [BD.Interpolation.factorialDominates](../BD/Interpolation.lean#L82), [BD.Tails.polynomialTail](../BD/Tails.lean#L19), [BD.Interpolation.leadingFrequency](../BD/Interpolation.lean#L72), [BD.Separation.moments_separate](../BD/Separation.lean#L34), [BD.Artin.isolateScale](../BD/Artin.lean#L16), [BD.Relations.realized_kernel](../BD/Relations.lean#L60), [BD.Monomials.independence](../BD/Monomials.lean#L31)

**Arithmetic or analytic scope.** The Deligne–Ribet interpolation and identity theorem for these germs, the functional equation, full construction of the scaled Dirichlet frequencies, squarefree coefficients and Chebotarev realization of the isolating samples. The transcendence-degree computation of the monomial field is outside this proof.

## Lemma 7.2. Values at interpolation integers

[Manuscript, p. 21](../paper/manuscript.pdf#page=21) · [LaTeX statement](../paper/manuscript.tex#L1780)

Growth and absolute-convergence estimates used after substituting the sample formula.

[BD.Interpolation.factorialDominates](../BD/Interpolation.lean#L82), [BD.Tails.envelope](../BD/Tails.lean#L10)

**Arithmetic or analytic scope.** The global Artin functional equation, gamma reflection and duplication, reciprocal Frobenius polynomial and squarefree Euler-coefficient formula.

## Corollary 7.3. Information lost at zero

[Manuscript, p. 23](../paper/manuscript.pdf#page=23) · [LaTeX statement](../paper/manuscript.tex#L1931)

Rank difference equals kernel dimension for the linear projection; exponent-fiber identification.

[BD.Linear.projectionLoss](../BD/Linear.lean#L48), [BD.Relations.kernel_eq_fiberIdeal](../BD/Relations.lean#L22)

**Arithmetic or analytic scope.** The analytic and numerical transcendence degrees on the two sides, including weak p-adic Schanuel on the numerical side.

## Corollary 7.4. Odd Brauer induction and irreducible germs

[Manuscript, p. 23](../paper/manuscript.pdf#page=23) · [LaTeX statement](../paper/manuscript.tex#L1968)

Cancellation of a common formal character and persistence of the ideal under injective realization; extraction of the expected coefficient.

[BD.Relations.brauer_clear](../BD/Relations.lean#L69), [BD.Relations.realized_kernel](../BD/Relations.lean#L60), [BD.Applications.grossCoefficient](../BD/Applications.lean#L28)

**Arithmetic or analytic scope.** Odd Brauer induction, meromorphic p-adic Artin functions, the exact-order arithmetic hypotheses and irreducible character independence for these functions.

## Example 8.1. The cubic at 7 and the quadratic field

[Manuscript, p. 24](../paper/manuscript.pdf#page=24) · [LaTeX statement](../paper/manuscript.tex#L2083)

Irreducibility over the rationals, positive nonsquare discriminant, three real roots and the polynomial factorization at 7. Exact finite splitting and actual permutation character calculations.

[BD.Cubic.irreducible](../BD/Cubic.lean#L25), [BD.Cubic.discriminantNotSquare](../BD/RealCubic.lean#L9), [BD.Cubic.threeRealRoots](../BD/RealCubic.lean#L15), [BD.Cubic.factorSeven](../BD/Cubic.lean#L32), [BD.Arithmetic.cubicFactorsSeven](../BD/Arithmetic.lean#L45), [BD.Arithmetic.quadraticLocalData](../BD/Arithmetic.lean#L49), [BD.Arithmetic.quadraticNorms](../BD/Arithmetic.lean#L43), [BD.Permutations.charactersOfAction](../BD/Permutations.lean#L40)

**Arithmetic or analytic scope.** Galois group and Frobenius interpretations for the particular splitting field, and identification of the coefficient with a local norm logarithm.

## Proposition 8.2. The next coefficient at 7

[Manuscript, p. 25](../paper/manuscript.pdf#page=25) · [LaTeX statement](../paper/manuscript.tex#L2115)

Lean identifies the character and evaluates the first and seventh Bernoulli polynomials. It verifies all three rational secants before reduction. For an arbitrary integral p-adic power series, its series converges on pℤₚ, its difference quotient tends to the linear coefficient, and its tail after that term vanishes modulo p². At the unique 7-adic coordinate with 8⁶(1+t)=1, the two interpolation residues force the normalized first-jet slope 42 modulo 49.

[BD.Arithmetic.delta_legendre](../BD/Legendre.lean#L37), [BD.Arithmetic.valueZero](../BD/Arithmetic.lean#L24), [BD.Arithmetic.valueMinusSix](../BD/Arithmetic.lean#L25), [BD.Arithmetic.secantSix](../BD/Bernoulli.lean#L55), [BD.Arithmetic.secantTwelve](../BD/Bernoulli.lean#L60), [BD.Arithmetic.secantFortyTwo](../BD/Bernoulli.lean#L65), [BD.Jet.slopeFromSample](../BD/Jet.lean#L51), [BD.Jet.logTermValuation](../BD/Jet.lean#L37), [BD.Jet.firstOrderFailure](../BD/Jet.lean#L74), [BD.Examples.characterRelation](../BD/Examples.lean#L19), [BD.Examples.quotientIdentity](../BD/Examples.lean#L37), [BD.SpecialValues.actualFirstValue](../BD/SpecialValues.lean#L36), [BD.SpecialValues.actualSeventhValue](../BD/SpecialValues.lean#L42), [BD.Arithmetic.exactMinusTwelve](../BD/Bernoulli.lean#L31), [BD.Arithmetic.exactMinusFortyTwo](../BD/Bernoulli.lean#L34), [BD.Arithmetic.exactSecants](../BD/Bernoulli.lean#L46), [BD.PadicJet.integralSeriesSummable](../BD/PadicJet.lean#L16), [BD.PadicJet.differenceQuotient](../BD/PadicJet.lean#L45), [BD.PadicJet.reduceValue](../BD/PadicJet.lean#L75), [BD.PadicJet.existsUniqueNegativeSix](../BD/PadicJet.lean#L90), [BD.PadicJet.negativeSixSample](../BD/PadicJet.lean#L106)

**Arithmetic or analytic scope.** The generalized Bernoulli special-value theorem, construction and interpolation of the Deligne–Ribet series, and the analytic change of variable from the power-series coordinate to the cyclotomic parameter using the p-adic logarithm.

## Proposition 9.1. Adding an abelian part

[Manuscript, p. 26](../paper/manuscript.pdf#page=26) · [LaTeX statement](../paper/manuscript.tex#L2247)

Multiplication of determinant classes and Euler factors on block extensions, plus the order and coefficients for ordinary or simple-zero formal Taylor factors.

[BD.Linear.extensionDet](../BD/Linear.lean#L54), [BD.Linear.periodProduct](../BD/Linear.lean#L67), [BD.Euler.blockFactor](../BD/Euler.lean#L13), [BD.Applications.ordinaryProduct](../BD/Applications.lean#L39), [BD.Series.ellipticExceptional](../BD/Series.lean#L70)

**Arithmetic or analytic scope.** Mixed realization exactness for the extension, the Hasse–Weil factor and modular-symbol rationality. The elliptic exceptional-zero discussion uses the named arithmetic theorems.

## Cubic, normal and C₃ character projections

The finite action, the dimension vector (1,0,1,2,3), residue-degree rescaling, and the scalar coefficient identity.

[BD.Examples.decompositions](../BD/Examples.lean#L22), [BD.Examples.localDimensions](../BD/Examples.lean#L28), [BD.Permutations.enumerationComplete](../BD/Permutations.lean#L21), [BD.Permutations.orderSixInduction](../BD/Permutations.lean#L43), [BD.Examples.coefficientIdentity](../BD/Examples.lean#L31), [BD.Examples.unscaledIdentity](../BD/Examples.lean#L34)

**Arithmetic or analytic scope.** Frobenius reciprocity for the stated number fields and the nonzero arithmetic regulators.

## Field of definition at 29 and growth in towers

Frobenius and quadratic tests modulo 29, recovery of a field from its stabilizer inside a finite Galois extension, and the combinatorial order 3·2ᵐ.

[BD.Arithmetic.cubicRootsTwentyNine](../BD/Arithmetic.lean#L48), [BD.Arithmetic.quadraticLocalData](../BD/Arithmetic.lean#L49), [BD.Characters.stabilizerCriterion](../BD/Characters.lean#L45), [BD.Examples.towerOrder](../BD/Examples.lean#L41), [BD.CoefficientField.fieldOfTrace](../BD/CoefficientField.lean#L23)

**Arithmetic or analytic scope.** Linear disjointness of the field towers, Dirichlet primes, p-adic character fields and nonvanishing of each arithmetic block.

## Ordinary and split multiplicative elliptic factors

The unit root differs from one under the point-count identity. A simple-zero factor increases the order exactly by one with nonzero coefficients.

[BD.Applications.ordinaryUnitRoot](../BD/Applications.lean#L33), [BD.Applications.ordinaryProduct](../BD/Applications.lean#L39), [BD.Series.ellipticExceptional](../BD/Series.lean#L70)

**Arithmetic or analytic scope.** Ordinary interpolation, Greenberg–Stevens for p ≥ 5, Kobayashi’s odd-prime result, and nonvanishing of the logarithm of the Tate parameter.

## Conjectures and normalizations

Local trivial Frobenius factor, constant Taylor factors and logarithm branch convention in coordinates.

[BD.Euler.constantFactor](../BD/Euler.lean#L21), [BD.Series.complexLeading](../BD/Series.lean#L65), [BD.Matrices.branchShift](../BD/Matrices.lean#L28)

**Arithmetic or analytic scope.** Definitions of Deligne 1-motives and Scholl’s critical value conjecture. The manuscript contains the arithmetic definitions and references.

## Labelled formulas

| Formula | Page | Manuscript result | What the correspondence covers |
| --- | ---: | --- | --- |
| [(1.1)](../paper/manuscript.tex#L100) | 2 | 1a | Definition. Betti to de Rham comparison at infinity. |
| [(2.1)](../paper/manuscript.tex#L238) | 4 | 2.1 | Arithmetic construction. Extension of the toric valuation to the semiabelian group. |
| [(2.2)](../paper/manuscript.tex#L288) | 4 | 2.1 | Reduction. Injectivity of tame restriction gives the valuation kernel after identifying the connecting map. |
| [(2.3)](../paper/manuscript.tex#L295) | 4 | 2.1 | Reduction. The cross-multiplied Euler identity and its determinant on split exact rows. |
| [(2.4)](../paper/manuscript.tex#L370) | 5 | 2.1 | Reduction. Place-by-place correction in the finite product. Realization and meromorphic continuation are external. |
| [(2.5)](../paper/manuscript.tex#L418) | 6 | 2.3 | Reduction. Range and rank calculations in the product case. General comparison sequence is external. |
| [(3.1)](../paper/manuscript.tex#L475) | 6 | 3.1 | Definition. Residue-degree weighted divisor map. |
| [(3.2)](../paper/manuscript.tex#L483) | 6 | 3.1 | Reduction. Lifting inside the kernel of the norm once the absolute norm diagram is available. |
| [(3.3)](../paper/manuscript.tex#L505) | 7 | 3.1 | Definition. Comparison with logarithm-weighted finite valuation rows. |
| [(3.4)](../paper/manuscript.tex#L525) | 7 | 3.1 | Reduction. Block determinant and product of period classes. Residue/period comparison is arithmetic. |
| [(3.5)](../paper/manuscript.tex#L533) | 7 | 3.1 | Arithmetic identity. Dedekind zeta factorization for relative norm tori. |
| [(3.6)](../paper/manuscript.tex#L535) | 7 | 3.1 | Reduction. Mixed finite-factor correction, formal order and product coefficient. |
| [(3.7)](../paper/manuscript.tex#L539) | 7 | 3.1 | Reduction. Formal product at the expected order with zeta constant and residue ratio supplied. |
| [(3.8)](../paper/manuscript.tex#L552) | 7 | 3.1 | Arithmetic construction. Absolute augmentation by the trace-one column. |
| [(3.9)](../paper/manuscript.tex#L666) | 8 | 3.3 | Reduction. Rank bound, removal of t powers of the variable and the leading coefficient of a product. |
| [(3.10)](../paper/manuscript.tex#L684) | 9 | 3.3 | Reduction. Surjectivity and equality of kernels at equal finite dimension. |
| [(4.1)](../paper/manuscript.tex#L775) | 10 | 4.1 | Definition. Logarithms of relative units in the local trace-zero subspace. |
| [(4.2)](../paper/manuscript.tex#L801) | 10 | 4.1 | Reduction. Normalization of a relative residue. Colmez’s formula is an external arithmetic input. |
| [(4.3)](../paper/manuscript.tex#L852) | 11 | 4.2 | Reduction. Finite product and powers of lower-bounded Taylor factors. |
| [(4.4)](../paper/manuscript.tex#L906) | 11 | 4.3 | Definition and reduction. Definition of the reduced branch in the paper; cancellation of powers in Lean. |
| [(5.1)](../paper/manuscript.tex#L1076) | 13 | 5.3 | Arithmetic identity. Local norm valuation equals residue degree times the normalized valuation. |
| [(5.2)](../paper/manuscript.tex#L1079) | 13 | 5.3 | Definition. Negative norm logarithm in the chosen branch. |
| [(5.3)](../paper/manuscript.tex#L1084) | 13 | 5.3 | Reduction. Branch translation and valuation normalization for actual matrices. |
| [(5.4)](../paper/manuscript.tex#L1154) | 14 | 5.2 | Reduction. Affine isolation from injectivity and disjointness of the logarithm image. |
| [(5.5)](../paper/manuscript.tex#L1226) | 15 | 5.3 | Reduction. Order of the inverse factors and compatibility under basis change. |
| [(5.6)](../paper/manuscript.tex#L1288) | 15 | 5.4 | Arithmetic convention. Order of cup factors and sign of local reciprocity. |
| [(5.7)](../paper/manuscript.tex#L1326) | 16 | 5.4 | Matrix identity. Obstruction equals zero exactly on the negative transpose graph. |
| [(5.8)](../paper/manuscript.tex#L1333) | 16 | 5.4 | Matrix identity. All principal minors and their signs over arbitrary commutative rings. |
| [(6.1)](../paper/manuscript.tex#L1409) | 17 | 6.1 | Representation theory. Decomposition of the odd permutation module and its commutant. |
| [(6.2)](../paper/manuscript.tex#L1436) | 17 | 6.1 | Reduction. The full characteristic-polynomial product for different block dimensions and arbitrary multiplicities. The representation-theoretic decomposition supplies the blocks. |
| [(6.3)](../paper/manuscript.tex#L1445) | 17 | 6.1 | Arithmetic and representation theory. Dimension of the algebraic span of actual simultaneous entries. |
| [(6.4)](../paper/manuscript.tex#L1524) | 18 | 6.4 | Arithmetic identity. Artin L-value and the local complex Euler slopes. |
| [(6.5)](../paper/manuscript.tex#L1548) | 18 | 6.4 | Definition and reduction. Normalization of a Taylor coefficient, including when the coefficient is zero. |
| [(6.6)](../paper/manuscript.tex#L1562) | 18 | 6.4 | Reduction. The supplied Taylor coefficient is normalized, and the determinant of the repeated block sum is the exact product with multiplicities. |
| [(6.7)](../paper/manuscript.tex#L1605) | 19 | 6.6 | Reduction. Linear trace-multiplicity equations under affine independence. |
| [(6.8)](../paper/manuscript.tex#L1665) | 19 | 6.8 | Algebraic identity. The full exponent-fiber ideal, the monomial independence criterion and algebraic independence of determinants of disjoint generic blocks of positive size. |
| [(7.1)](../paper/manuscript.tex#L1752) | 20 | 7.1 | Reduction. The complete kernel of the exponent map. Injectivity for the specified p-adic germs is a separate step. |
| [(7.2)](../paper/manuscript.tex#L1790) | 21 | 7.2 | Arithmetic and analytic identity. Explicit Artin functional equation and archimedean gamma factors. |
| [(7.3)](../paper/manuscript.tex#L1797) | 21 | 7.2 | Arithmetic identity. Squarefree Euler coefficients at specified unramified primes. |
| [(7.4)](../paper/manuscript.tex#L1846) | 22 | 7.1 | Reduction. A nonzero solution to any family of algebraic sample equations descends to the base field. |
| [(7.5)](../paper/manuscript.tex#L1873) | 22 | 7.1 | Reduction. A normalized isolated polynomial with vanishing tail is zero; all weights at a scale vanish under the formal sample hypotheses. |
| [(7.6)](../paper/manuscript.tex#L1978) | 23 | 7.4 | Reduction. Formal coefficient extraction and multiplicative cancellation. Brauer and analytic identification remain external. |
| [(8.1)](../paper/manuscript.tex#L2071) | 24 | 8a | Algebraic and finite identities. Actual permutation character table, algebraic coefficient identity and unscaled factor of two. |
| [(9.1)](../paper/manuscript.tex#L2236) | 26 | 9.1 | Arithmetic construction. Exact sequence of 1-motives with abelian quotient. The diagonal determinant identity is checked. |
