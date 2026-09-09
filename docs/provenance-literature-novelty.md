# Provenance, prior art, and novelty assessment

Date of literature audit: 2026-09-09.

This document separates three questions that must not be conflated:

1. **mathematical verification** of the Lean theorem;
2. **project provenance** of the proof developed in this repository and its internal research companion; and
3. **external novelty / priority** relative to the mathematical literature.

The first is machine-checkable and is recorded in `docs/verification.md` and
`docs/verification-results.json`. The second is documented by Git history and
the paper/Lean correspondence. The third can only be assessed by literature
search; no search can certify absolute historical priority.

## Result under assessment

For every characteristic-zero field `k`, every smooth integral finitely
generated `k`-algebra `A`, and every nonzero finite-order differential
operator `d ∈ D_k(A)`, the formal theorem states that there are `F,R,S ∈ D_k(A)`
with

```text
1 = d R + F d S.
```

The first generator is exactly `d` and the second generator retains the same
right divisor `d`.

The internal research programme also proves that this same-divisor property
implies cyclicity of finitely generated torsion right modules and hence
two-generation of right ideals. Thus the literature status of the weaker
smooth-affine two-generator problem is directly relevant novelty evidence,
although that consequence is not itself a Palomar endpoint of this repository.

## Literature-search method

The 2026-09-09 audit searched the exact identity and natural verbal variants
("same divisor", Stafford, `D(X)`, smooth affine varieties, two/three
generators, right ideals, torsion modules), and followed the citation chain
through the principal primary and survey literature. Sources checked include
publisher records/full text, DOI-indexed records, arXiv and institutional
copies, recent surveys, and cited follow-up work.

The search deliberately covered several partially overlapping literatures:

- Stafford's general simple-Noetherian stable-range work;
- Stafford's Weyl-algebra generation and torsion-module results;
- algorithmic/constructive Stafford theorems;
- extensions from Weyl algebras to rings `D(X)` of differential operators on
  smooth affine varieties;
- right-ideal generation and module structure for `D(X)`;
- the special theory for affine curves;
- formal/convergent Laurent-series differential-operator rings;
- structural results on generators, PBW and noetherianity of smooth-affine
  differential-operator rings.

No published, preprint, thesis, or survey source located in this search states
or proves the literal universal same-divisor identity above for arbitrary
smooth integral affine `A`.

## Closest prior art

### Stafford 1976–1977 — general simple-Noetherian stable range

J. T. Stafford, *Completely Faithful Modules and Ideals of Simple Noetherian
Rings*, Bulletin of the London Mathematical Society 8 (1976), 168–173,
DOI `10.1112/blms/8.2.168`.

J. T. Stafford, *Stable Structure of Noncommutative Noetherian Rings*, Journal
of Algebra 47 (1977), 244–267, DOI `10.1016/0021-8693(77)90224-1`.

These papers develop dimension-dependent generation/stable-range results for
simple Noetherian rings. Bellamy's 2026 survey recalls, for example, that a
simple right Noetherian ring of Krull dimension `n` has right ideals generated
by at most `n+1` elements, and that Stafford then develops a noncommutative
stable-range theorem. These broad results are important ancestry but do not
give a dimension-free two-generator theorem or the present same-divisor
identity for arbitrary smooth-affine `D(X)`.

### Stafford 1978 — Weyl algebra source problem

J. T. Stafford, *Module Structure of Weyl Algebras*, Journal of the London
Mathematical Society (2) 18 (1978), 429–442,
DOI `10.1112/jlms/s2-18.3.429`.

Stafford proves that every right ideal of the Weyl algebra is two-generated,
that finitely generated torsion modules are two-generated, and formulates
Conjecture 3.8, the stronger same-divisor/cyclicity frontier imported by this
project through `stafford38-formal`. Gwyn Bellamy's 2026 retrospective states
that Conjecture 3.8 is a slightly stronger form of the conjecture that every
finitely generated torsion Weyl-algebra module is cyclic and records it as
still open in the pre-existing literature.

### Leykin 2004 — algorithms, still Weyl-specific

A. Leykin, *Algorithmic Proofs of Two Theorems of Stafford*, Journal of
Symbolic Computation 38 (2004), 1535–1550,
DOI `10.1016/j.jsc.2004.07.003`.

Leykin makes algorithmic two classical Weyl-algebra results: two-generation of
ideals and cyclicity of holonomic modules. This is computationally important
prior art but does not address arbitrary smooth-affine `D(X)` or the stronger
same-divisor identity.

### Björk 1981 — two-generator question for `D(X)`

J.-E. Björk, *The Bernstein class of modules on algebraic manifolds*, Lecture
Notes in Mathematics 867 (1981), 148–156. Problem 2.10 asks whether the
smooth-affine differential-operator analogue can be generated by two elements.
Bellamy 2026 cites this question explicitly as open.

### Coutinho–Holland 1988 — three generators for general smooth affine `D(X)`

S. C. Coutinho and M. P. Holland, *Module Structure of Rings of Differential
Operators*, Proceedings of the London Mathematical Society (3) 57 (1988),
417–432, DOI `10.1112/plms/s3-57.3.417`.

For a smooth irreducible affine variety `X` over a characteristic-zero field,
they prove that every right ideal of `D(X)` is generated by **three** elements
and that stably free modules of rank at least three are free. Their abstract
does not state a two-generator theorem, much less the present same-divisor
identity. Bellamy 2026 identifies this as the relevant general theorem before
repeating Björk's two-generator question.

A 2001 master's dissertation by Laura Mercedes Cárdenas Cortés,
*Ideais de anéis de operadores diferenciais* (Universidade de São Paulo,
DOI `10.11606/D.45.2001.tde-23102024-181525`), likewise presents the
Coutinho–Holland three-generator result for rings of differential operators and
two-generation only for the Weyl algebra. This is useful negative evidence
against an unnoticed standard two-generator upgrade in the intervening
literature.

### Bellamy 2026 — contemporary status check

G. Bellamy, *Module structure of Weyl algebras*, Journal of the London
Mathematical Society 113 (2026), e70373, DOI `10.1112/jlms.70373`, first
published 7 January 2026.

Section 3 states that Stafford's torsion cyclicity / Conjecture 3.8 remains open
as far as the author is aware. Section 6 says that for differential operators
on smooth affine varieties, Coutinho–Holland proved three-generation of every
right ideal and that it is a question of Björk whether **two** generators
suffice. This is the strongest recent independent status evidence found because
it postdates the classical and modern follow-up literature and specifically
surveys Stafford-type module structure.

### Curve-specific structure

S. P. Smith and J. T. Stafford, *Differential Operators on an Affine Curve*,
Proceedings of the London Mathematical Society (3) 56 (1988), 229–259,
DOI `10.1112/plms/s3-56.2.229`, develops the structure of `D(X)` for affine
curves, including noetherianity, simplicity/Morita criteria, and normalization.

R. C. Cannings and M. P. Holland, *Right Ideals of Rings of Differential
Operators*, Journal of Algebra 167 (1994), 116–141,
DOI `10.1006/jabr.1994.1179`, studies right ideals in rings of differential
operators on curves and related rings.

Y. Berest and O. Chalykh, *Ideals of Rings of Differential Operators on
Algebraic Curves*, Journal of Pure and Applied Algebra 216 (2012), 1493–1527,
DOI `10.1016/j.jpaa.2012.01.006`, geometrically classifies ideals for smooth
affine irreducible curves. These results are substantial neighboring prior art
but do not provide the general smooth higher-dimensional same-divisor theorem.

### Laurent-series and other special two-generator extensions

N. Caro and D. Levcovitz, *On a Theorem of Stafford*, Cadernos de Matemática
11 (2010), 63–70; arXiv `1005.4427`, proves two-generation of left and right
ideals for differential operators over fields of formal Laurent series and the
analogous convergent Laurent-series setting. The authors explicitly describe
this as being in accordance with the broader conjecture that ideals in
noncommutative Noetherian simple rings should be two-generated; it is not a
proof for all smooth-affine `D(X)`.

N. Caro-Tuesta and D. Levcovitz, *Module Structure of Certain Rings of
Differential Operators*, Algebras and Representation Theory 23 (2020),
1637–1657, DOI `10.1007/s10468-019-09905-4`, proves analogous two-generator
results for specified formal-series/Laurent-series differential-operator
rings. Again, the scope is special and does not contain the universal
smooth-affine theorem here.

### Constructive Stafford-type results

A. Quadrat and D. Robertz, *A Constructive Study of the Module Structure of
Rings of Partial Differential Operators*, Acta Applicandae Mathematicae 133
(2014), 187–234, DOI `10.1007/s10440-013-9864-x`, develops constructive
versions of Stafford's Weyl-algebra results and extensions to certain "very
simple" domains based on Stafford and Coutinho–Holland. The paper does not
supply the literal theorem here for all smooth integral affine varieties.

### Structural smooth-affine `D(X)` literature

V. V. Bavula, *Generators and Defining Relations for the Ring of Differential
Operators on a Smooth Affine Algebraic Variety*, Algebras and Representation
Theory 13 (2010), 159–187, DOI `10.1007/s10468-008-9112-7`, arXiv
`math/0504475`, gives explicit algebra generators/relations and establishes
standard structural properties for smooth-affine differential-operator rings.
This supports the ambient `D(X)` framework but is not an ideal-generation or
same-divisor theorem.

## Novelty assessment

**Evidence level: strong literature evidence, not an absolute priority
certificate.**

The search found no prior statement or proof of the literal universal identity
`1 = dR + FdS` for `D_k(A)` on every smooth integral affine variety. More
importantly, Bellamy's January 2026 literature survey describes the weaker
two-generator question for right ideals of `D(X)` as still open, with the
strongest general published smooth-affine result cited there being
Coutinho–Holland's three-generator theorem. Special two-generator results for
Weyl algebras, Laurent-series rings, curves, holonomic modules, or selected
"very simple" domains do not bridge this gap.

The project theorem is therefore not presented as a routine reformulation of
known `D(X)` literature. Nevertheless, this repository does **not** claim that
a bibliographic search can prove first-ever discovery or publication priority.
The correct claim is:

> As of the 2026-09-09 audit, no prior proof of the exact theorem was located,
> and recent expert survey literature still records a weaker adjacent
> generation problem as open. This provides strong evidence of novelty, while
> absolute priority remains unasserted pending independent expert/journal
> review and the possibility of uncatalogued prior work.

Any earlier wording saying that this formalization is *the first presentation*
of the theorem is superseded by this evidence-graded statement. Dated internal
notes establish project chronology only.

## Project provenance and dependency revisions

The internal research exposition predates parts of the Lean implementation and
is retained in `itpplasma/global-stafford`, especially
`notes/source-changing-descent-2026-09-07.md`. This establishes project
chronology; it is not evidence of external publication priority.

The mechanically reviewed Global Stafford snapshot is
`b21883a5b3d8f46922713049c3b060523ea3a771`. Its machine-readable replay
record consumes:

- `stafford38-formal@e77e176c381ca2d6b20c030f9227f1b031415d2e`;
- `algebraic-analysis@4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`;
- Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

The older Stafford38 revision
`784b59925beb9a480519142336bd6434f6eeef16` is retained only as a
**historical inspection pin** used by the informal proof development. It is
not the dependency revision consumed by the reviewed build. The file
`Stafford38/FoundationClosure.lean` containing `Stafford38.universalStatement`
has the same source text at the historical and consumed revisions; current
reproduction must nevertheless use the consumed `e77e176...` pin recorded in
`lake-manifest.json` and `docs/verification-results.json`.

Release `v1.0.5` packages this provenance/literature correction and Palomar
citation metadata; it does not change Lean proof bytes or the mathematical
verification report.

## Palomar provenance pointer

Registry record supplied for this formalization:

- entry ID: `PALOMAR-2026-09-05-000007`
- version: `2`
- URL: <https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2>

Palomar mechanical/editorial status and the mathematical literature-priority
assessment are separate evidence layers. A successful proof check does not by
itself establish novelty, and this literature audit does not replace human
mathematical review.
