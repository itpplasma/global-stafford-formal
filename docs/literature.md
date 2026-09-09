# Literature and proof index

This index connects the source problem, structural background, formal imports,
and the source-changing proof. The [dated literature audit](provenance-literature-novelty.md)
contains the broader prior-art search, including stable-range, curve,
Laurent-series and algorithmic results. Its qualified novelty assessment
remains authoritative; this index adds no priority claim.

## Reading order

Read [Sta78](#sta78) for the Weyl source problem and [Bel26](#bel26),
[Bjo81](#bjo81), [CH88](#ch88) for smooth-affine context. Then follow the
[paper/Lean correspondence](paper-lean-specification.md) and the
[clickable proof-map PDF](dossier/global-stafford-dossier.pdf).
The internal exposition records the same research development; it is not a
separately published article. All proof steps needed by this public repository
are available in its Lean sources and pinned public dependencies.

## Sources mapped to the proof

| Ingredient and role | Source or context | Lean entry points |
| --- | --- | --- |
| Weyl same-divisor identity over every characteristic-zero field, including `k(t)` | Conjecture in [Sta78](#sta78); actual proof imported from Stafford38 v1.1.0 | [ChartDataOverK](../GlobalStafford/Chart/ChartDataOverK.lean), [PhaseI](../GlobalStafford/Assembly/PhaseI.lean); [pinned upstream theorem](https://github.com/itpplasma/stafford38-formal/blob/e77e176c381ca2d6b20c030f9227f1b031415d2e/Stafford38/FoundationClosure.lean) |
| Intrinsic finite-order operators and localization | [StacksD](#stacksd), [Bav10](#bav10) as structural context; concrete proofs in Lean | [Basic](../GlobalStafford/Operators/Basic.lean), [Construction](../GlobalStafford/Localization/Construction.lean) |
| Smooth cover, étale derivations, finite generic fibre and domain | [StacksS](#stackss); pinned Mathlib plus local producers | [SmoothCover](../GlobalStafford/Chart/SmoothCover.lean), [EtaleDerivations](../GlobalStafford/Chart/EtaleDerivations.lean), [GenericFibre](../GlobalStafford/Chart/GenericFibre.lean), [ChartDomain](../GlobalStafford/Chart/ChartDomain.lean) |
| Finite-right-rank ascent and scalar extension | Project argument; uses the Weyl theorem, not a finite-generation assumption on the chart | [FiniteRankAscent](../GlobalStafford/Chart/FiniteRankAscent.lean), [ScalarExtensionConstruction](../GlobalStafford/Chart/ScalarExtensionConstruction.lean) |
| Ordered clearance and squared-annihilator extraction | Project exposition §1 and §3; explicit right cofactors | [Commutator](../GlobalStafford/Operators/Commutator.lean), [SquaredAnnihilator](../GlobalStafford/Certificate/SquaredAnnihilator.lean) |
| Bounded-order sources, old-chart protection, finite-cover patching | Project exposition Remark 4.2, Theorems 4.1 and 5.1 | [RightMoved](../GlobalStafford/Conjugation/RightMoved.lean), [BoundedOrderSource](../GlobalStafford/Descent/BoundedOrderSource.lean), [OldChartProtection](../GlobalStafford/Certificate/OldChartProtection.lean), [FiniteCoverPatching](../GlobalStafford/Descent/FiniteCoverPatching.lean) |
| Terminal theorem and independent statement transport | Theorem 6.3 of the project exposition | [Closure](../GlobalStafford/Assembly/Closure.lean), [ChallengeTransport](../GlobalStafford/Assembly/ChallengeTransport.lean) |
| Two-/three-generator frontier | [Bjo81](#bjo81), [CH88](#ch88), [Bel26](#bel26) | Prior art only; no proof edge |

The chart parameter is central and only scalar denominators are inverted.
Finite right rank is not finite generation. Neither the separate Björk
programme nor a three-generator theorem supplies the whole-chart S38 input.
Gabber’s involutivity enters transitively through the proved Stafford38 theorem;
its source and visible-frame route are indexed in the
[Stafford38 literature guide](https://github.com/itpplasma/stafford38-formal/blob/main/docs/literature.md).

## Formal foundations

The consumed pins remain Stafford38 `e77e176c381ca2d6b20c030f9227f1b031415d2e`,
AlgebraicAnalysis `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`, and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
The [verification report](verification-results.json) fixes the checked snapshot.
The [AlgebraicAnalysis index](https://github.com/itpplasma/algebraic-analysis/blob/main/docs/literature.md)
explains the reusable library; its newer documentation does not change these pins.

## Bibliography

<a id="sta78"></a>

**[Sta78]** J. T. Stafford, *[Module Structure of Weyl Algebras](https://doi.org/10.1112/jlms/s2-18.3.429)*, Journal of the London Mathematical Society (2) 18 (1978), 429–442.

Source of Conjecture 3.8 (p. 438). The 1978 conjecture is the target, not a proof of its general case.

<a id="bel26"></a>

**[Bel26]** Gwyn Bellamy, *[Module structure of Weyl algebras](https://doi.org/10.1112/jlms.70373)*, Journal of the London Mathematical Society 113 (2026), no. 1, e70373.

Historical status and adjacent results, especially Sections 3 and 6; not an imported proof theorem.

<a id="bjo81"></a>

**[Bjo81]** J.-E. Björk, *[The Bernstein class of modules on algebraic manifolds](https://doi.org/10.1112/jlms.70373)*, Lecture Notes in Mathematics 867 (1981), 148–156, Problem 2.10.

Prior-art question, Problem 2.10. The link is Bellamy’s survey, which supplies the bibliographic locator; this is not a dependency on a separate Björk formalization.

<a id="ch88"></a>

**[CH88]** S. C. Coutinho and M. P. Holland, *[Module Structure of Rings of Differential Operators](https://doi.org/10.1112/plms/s3-57.3.417)*, Proceedings of the London Mathematical Society (3) 57 (1988), 417–432.

Prior art: three-generation for smooth-affine differential-operator rings. Not the same-divisor theorem and not an input to the source-changing descent.

<a id="stacksd"></a>

**[StacksD]** The Stacks Project Authors, *[Finite order differential operators](https://stacks.math.columbia.edu/tag/09CH)*, The Stacks Project, Section 10.133, tag 09CH (accessed 2026-09-09).

Background for the recursive commutator definition and localization of finite-order differential operators; Lean implementations and hypotheses are indexed below.

<a id="stackss"></a>

**[StacksS]** The Stacks Project Authors, *[Smooth ring maps](https://stacks.math.columbia.edu/tag/00T1)*, The Stacks Project, Section 10.137, tag 00T1 (accessed 2026-09-09).

Background for smooth algebras and local standard-smooth presentations; concrete chart producers use the pinned Mathlib API.

<a id="bav10"></a>

**[Bav10]** V. V. Bavula, *[Generators and Defining Relations for the Ring of Differential Operators on a Smooth Affine Algebraic Variety](https://doi.org/10.1007/s10468-008-9112-7)*, Algebras and Representation Theory 13 (2010), 159–187.

Structural background for smooth-affine differential-operator rings; not a same-divisor theorem or an imported axiom.
