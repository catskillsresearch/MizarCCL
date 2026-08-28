# Tarski–Grothendieck Set Theory (Mizar TARSKI)

---

## Abstract

This note is the write-up of a Lean 4 translation of Andrzej Trybulec,
*Tarski Grothendieck Set Theory* (Mizar article `TARSKI`, received
1 January 1989). The source file is `vendor/mml/tarski.miz` from
the [Mizar Mathematical Library](https://github.com/MizarSystem/MML.git)
at revision `047822c4d814630b28eec8ca6b455e9eb912d5ff`. The article
is the axiomatic root of the MML: extensionality, singleton and
unordered pair, inclusion, union, regularity, the Fraenkel scheme,
the Kuratowski pair, equipotence, and the Tarski–Grothendieck
universe axiom. The Lean development defines a model (`TarskiSet`)
and proves those statements; it is sorry-free. Compared theorems
audit to `{propext, Classical.choice, Quot.sound}`.

---

## 1. Introduction

`TARSKI` is the first article of the Mizar Mathematical Library and
the first item of the MizarCCL translation queue (368 used articles
in the YELLOW* / WAYBEL* environ closure). Mizar treats `set` as an
untyped sort with a primitive membership predicate `in`. This
package does **not** post `axiom set` and does **not** use `set` as
a synonym for `Type`. The carrier is a defined type `TarskiSet.{u}`:
Aczel pre-sets indexed by `Type u`, quotiented by extensional
equivalence. Membership is defined.

The compared claim is a machine-checked Lean rendering of the
Mizar-labelled items `TARSKI:1`–`TARSKI:3`, `TARSKI:def 1`–`def 6`,
and `TARSKI:sch 1`. `TARSKI:3` is universe-polymorphic: the
collection of all `TarskiSet.{u}` lives in `TarskiSet.{u+1}`. Mizar’s
power-set witness (iii) and inaccessibility clause (iv) are not
theorems of `Type u` and are **not** posted as a Lean `axiom`, so
the compared surface stays free of `axiom` / `sorry` / `admit` for
Palomar. Downstream theorems whose Mizar proofs need those clauses
use alternate arguments and must document the variation (example:
`WELLORD2.th17`).

The Mizar source is vendored from
[`MizarSystem/MML`](https://github.com/MizarSystem/MML.git)
as `vendor/mml/tarski.miz` (AMU dual license). The Lean package is
Apache-2.0. Pin:
`vendor/MML_PIN` = `047822c4d814630b28eec8ca6b455e9eb912d5ff`. This
repository uses the same dual license.

## 2. Representation

A pre-set is a family of pre-sets indexed by a `Type u`. Two
pre-sets are equivalent when their families are mutually dense under
that relation. `TarskiSet.{u}` is the quotient. Lean notation
`x ∈ X` is Mizar `x in X`. Inclusion `X ⊆ Y` is Mizar `X c= Y`.
The constructors `{y}`, `{y,z}`, `union X`, and `[x,y]` are
definitions on the quotient (singleton, unordered pair, union,
Kuratowski pair). A lift `ulift` embeds `TarskiSet.{u}` into
`TarskiSet.{u+1}`.

## 3. Mizar inventory

The table is the inventory of the article. In Markdown tables,
literal `|` is written `\|`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `TARSKI:1` | `th1` | Extensionality |
| `TARSKI:def 1` | `def1` / `singleton` | `x ∈ {y}` iff `x = y` |
| `TARSKI:def 2` | `def2` / `upair` | `x ∈ {y,z}` iff `x = y` or `x = z` |
| commutativity | `upair_comm` | `{y,z} = {z,y}` |
| `TARSKI:def 3` | `def3` / `subset` | `X ⊆ Y` iff every element of `X` is in `Y` |
| reflexivity | `subset_refl` | `X ⊆ X` |
| `TARSKI:def 4` | `def4` / `union` | `x ∈ union X` iff some `Y` has `x ∈ Y` and `Y ∈ X` |
| `TARSKI:2` | `th2` | Regularity; uses `Classical.choice` |
| `TARSKI:sch 1` | `sch1` | Fraenkel; uses `Classical.choice` |
| `TARSKI:def 5` | `def5` / `pair` | `[x,y] = {{x,y},{x}}` |
| `TARSKI:def 6` | `def6` / `are_equipotent` | Functional graph of a bijection |
| `TARSKI:3` | `th3` / `ulift` | Universe of all `u`-sets in `u+1`; subset-closed. Not Mizar (iii)–(iv) |

**Complete?**

- Yes for the **statements** of `TARSKI:1`–`2`, `def 1`–`6`, and
  `sch 1`, and for clauses (i)–(ii) of `TARSKI:3` in the
  universe-polymorphic reading.
- No for a **single-sort inaccessible** as in Mizar (iii)–(iv).
  Lean does not treat `Type u` as a ZFC inaccessible. Those clauses
  are omitted on purpose (no Lean `axiom`) rather than posted for
  proof fidelity; see the `TARSKI` module docstring and the
  variation note on `WELLORD2.th17`.

**Proof note (choice).** `#print axioms` of `th2` and `sch1` includes
`Classical.choice` (well-founded descent on pre-set membership;
selection of a Fraenkel image). The remaining compared theorems
use at most `{propext, Quot.sound}`. There is no project-defined
`axiom` and no `sorry` outside `Challenge.lean`.

## 4. Palomar statement of record

`Challenge.lean` restates every compared `TARSKI` theorem and
constructor with `sorry`. `Solution.lean` imports
`MizarCCL/TARSKI.lean`. `comparator.json` lists 12 theorems and
7 definitions. Types must match under `pp.all` / `pp.explicit`
(`scripts/compare_challenge_solution_types.sh`).

## 5. Build

Toolchain: Lean **v4.33.0**. No Mathlib.

```
lake build
bash scripts/palomar_preflight.sh
bash scripts/build_arxiv_pdf.sh
```

`lake build` typechecks `MizarCCL`, `Challenge`, and `Solution`.
Narrative inventory: this file. Metadata: `comparator.json`,
`formalization.yaml`. MML pin: `vendor/MML_PIN` =
`047822c4d814630b28eec8ca6b455e9eb912d5ff`.

## References

- **[Tar38]** Alfred Tarski. *Über unerreichbare Kardinalzahlen*.
  Fundamenta Mathematicae 30 (1938), 68–69.
- **[Tar39]** Alfred Tarski. *On Well-ordered Subsets of any Set*.
  Fundamenta Mathematicae 32 (1939), 176–183.
- **[Try89]** Andrzej Trybulec. *Tarski Grothendieck Set Theory*.
  Mizar article `TARSKI`, received 1 January 1989. Source:
  [`mml/tarski.miz`](https://github.com/MizarSystem/MML/blob/047822c4d814630b28eec8ca6b455e9eb912d5ff/mml/tarski.miz)
  in [MizarSystem/MML](https://github.com/MizarSystem/MML.git)
  at `047822c4d814630b28eec8ca6b455e9eb912d5ff` (Mizar 7.13.01 /
  MML 4.181.1147).

## 6. Boolean articles (`XBOOLE_0`, `XBOOLE_1`)

The next two queue items are Library Committee Boolean properties
of sets. Lean modules import as the Mizar environs do: `XBOOLE_0`
imports `TARSKI`; `XBOOLE_1` imports `TARSKI` and `XBOOLE_0`.
Mathlib `Set α` is not a stand-in for `TarskiSet`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `XBOOLE_0:sch Separation` | `sch_separation` | Fraenkel with `x = y ∧ P[y]` |
| `XBOOLE_0:def 1`–`def 10` | `isEmpty`, `∅`, `∪`, `∩`, `\`, `∆`, `misses`, `⊂`, `are_ccomparable`, `def10` | Boolean constructors |
| `XBOOLE_0:1`–`7` | `th1`–`th7` | Symmetric difference, `meets`, schemes |
| `XBOOLE_1:1`–`117` | `th1`–`th117` | Union/intersection/difference algebra; `Lm1`–`Lm5` |

**Complete?** Yes for both articles. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}` (choice from Separation /
empty set). No `sorry` in `MizarCCL/`.

## 7. Enumerated sets (`ENUMSET1`)

Finite enumerations `{x1,…,xn}` for `n = 3..10` are
`union({{prefix},{xn}})` as in the Mizar article. Lean insert
notation is not used. Environ: `TARSKI`, `XBOOLE_0`, `XBOOLE_1`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `ENUMSET1:def 1`–`def 8` | `enumset3`–`enumset10`, `def1`–`def8` | Membership is a right-associated disjunction |
| `ENUMSET1:1`–`28` | `th1`–`th28`, `lm2`–`lm6` | Union splits of an enumeration |
| `ENUMSET1:29`–`56` | `th29`–`th56` | Duplicate-argument collapse |
| `ENUMSET1:57`–`76` | `th57`–`th76`, `lm7`–`lm8` | 3- and 4-set permutations |
| `ENUMSET1:77`–`87` | `th77`–`th87`, `lm9` | 9-/10-set splits; addenda |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`.

## 8. Kuratowski pairs and projections (`XTUPLE_0`)

Ordered pairs are `TARSKI.pair`. The article adds the pair
attribute, component functions, triples/quadruples, and
`proj1`/`proj2` of a set of pairs (Separation on
`union (union X)`). Environ theorems include `ENUMSET1`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `x is pair` | `isPair` | `∃ x1 x2, x = pair x1 x2` |
| pair projections | `fst`, `snd` | Mizar `x\`1` / `x\`2`; choice on an `isPair` witness |
| `[x1,x2,x3]`, `[x1,x2,x3,x4]` | `triple`, `quadruple` | Nested Kuratowski pairs |
| `proj1 X`, `proj2 X` | `proj1`, `proj2` | `def4`, `def5` |
| `XTUPLE_0:1`, `:3` | `th1`, `th3` | Pair/triple injectivity |
| `XTUPLE_0:10`–`20a` | `th10`–`th20a` | Projection monotonicity and members |
| `XTUPLE_0:22`–`38` | `th22`–`th38` | Boolean algebra of projections |
| second `Th32`/`Th34`/`Th36` | `th40`, `th42`, `th44` | Quadruple-projection forms |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}` (choice from
`fst`/`proj1`).

## 9. Regularity (`XREGULAR`)

Consequences of `TARSKI:2`. Environ: `TARSKI`, `XBOOLE_0`,
`XBOOLE_1`, `ENUMSET1` (not `XTUPLE_0`).

| Mizar | Lean | Notes |
| --- | --- | --- |
| `XREGULAR:1` | `th1` | Nonempty `X` has `Y ∈ X` with `Y` misses `X` |
| unlabeled depth 1–5 | `th2`–`th6` | Disjointness along ∈-chains |
| no 3–6 cycles | `th7`–`th10` | Via `th1` on an enumeration |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `ZFMISC_1`.

## 10. Some basic properties of sets (`ZFMISC_1`)

Power set, finite-set calculus, and Cartesian products. Environ:
`TARSKI`, `XBOOLE_0`, `XBOOLE_1`, `ENUMSET1`, `XTUPLE_0`, `XREGULAR`.
`bool X` is the Aczel family of subsets of `X` (same universe).
`product X Y` is Separation on `bool (bool (X ∪ Y))` as in the
article. Mizar `ZFMISC_1:27` is canceled.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `ZFMISC_1:def 1` | `bool` / `def1` | `Z ∈ bool X` iff `Z ⊆ X` |
| `ZFMISC_1:def 2` | `product` / `def2` | `z ∈ product X Y` iff `z = [x,y]` for `x ∈ X`, `y ∈ Y` |
| 3-/4-fold products | `product3`, `product4` | `[:X,Y,Z:]`, `[:X,Y,Z,W:]` |
| `ZFMISC_1:1`–`26` | `th1`–`th26` | Empty set, singletons, pairs, `bool {x}` |
| canceled | — | Mizar `ZFMISC_1:27` |
| `ZFMISC_1:28`–`66` | `th28`–`th66` | Pair/product identities; inclusion in a pair |
| `ZFMISC_1:67`–`83` | `th67`–`th83` | `bool` and `union` |
| `ZFMISC_1:84`–`111` | `th84`–`th111` | Products; `th93`/`th111` use regularity |
| `ZFMISC_1:112` | `th112` | Universe subset-closed; not Mizar `bool`-closure / (iv) |
| `ZFMISC_1:113`–`138` | `th113`–`th138` | Addenda; `def 10` is `isTrivial` |

**Complete?** Yes for numbered theorems except the extra `TARSKI:3`
clauses in `th112` (documented). `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `SUBSET_1`.

## 11. Properties of subsets (`SUBSET_1`)

Modes on `TarskiSet`, not Lean subtypes. Environ: `TARSKI`,
`XBOOLE_0`, `XBOOLE_1`, `ENUMSET1`, `ZFMISC_1`. Import is
`ZFMISC_1` only (the rest arrives transitively). `bool X` is never
empty, so a subset of `E` is just an element of `bool E`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `SUBSET_1:def 1` | `isElement` / `def1` | `x ∈ X` if `X` nonempty, else `x` empty |
| `Subset of X` | `isSubset` | `Y ⊆ X` (`Element of bool X`) |
| `{}E`, `[#]E`, `A\`` | `emptyOf`, `hash`, `compl` | Empty / full / complement relative to `E` |
| `choose S` | `choose` | `the Element of S` (choice) |
| `proper` | `isProper` | `A ≠ E` |
| `SUBSET_1:1`–`4` | `th1`–`th4` | Empty subset; subset/eq via `Element of E` |
| `SUBSET_1:5`–`26` | `th5`–`th26` | Complement and Boolean identities |
| `SUBSET_1:27`–`41` | `th27`–`th41` | Elements, enumerated subsets |
| schemes | `sch_SubsetEx`, `sch_SubsetEq`, `sch_SubsetEx2`, `sch_SubComp` | Separation on subsets |
| `SUBSET_1:42`–`48` | `th42`–`th48` | Addenda; trivial / proper |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `SETFAM_1`.

## 12. Families of sets (`SETFAM_1`)

Intersection of a family, pairwise Boolean operations on families,
and subset-families. Environ: `TARSKI`, `XBOOLE_0`, `XBOOLE_1`,
`ENUMSET1`, `ZFMISC_1`, `SUBSET_1`. Import is `SUBSET_1` only.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `SETFAM_1:def 1` | `meet` / `def1` | `x ∈ meet X` iff `∀ Y ∈ X, x ∈ Y` (`X ≠ ∅`); else `∅` |
| `is_finer_than` / `is_coarser_than` | `isFiner` / `isCoarser` | |
| `UNION` / `INTERSECTION` / `DIFFERENCE` | `familyUnion` / `familyIntersection` / `familyDifference` | `def4`–`def6` |
| `Subset-Family of D` | `isSubsetFamily` | `F ⊆ bool D` |
| `COMPLEMENT(F)` | `complement` | `P ∈ it` iff `P\` ∈ F` |
| `Intersect B` | `Intersect` | `meet B` if nonempty, else the ambient set |
| `Cover of X` | `isCover` | `X ⊆ union F` |
| `SETFAM_1:1`–`49` | `th1`–`th49` | Meet calculus, complements, covers |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `RELAT_1`.

## 13. Relations (`RELAT_1`)

Relations as sets of Kuratowski pairs. Environ: `TARSKI`,
`XBOOLE_0`, `XBOOLE_1`, `ENUMSET1`, `XTUPLE_0`, `ZFMISC_1`,
`SUBSET_1`. Import is `SUBSET_1` only. Canceled: `4`–`6`,
`116`–`117`, `136`–`137`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `RELAT_1:def 1` | `isRelation` / `def1` | every element is a pair |
| `dom` / `rng` / `field` | `dom` / `rng` / `field` | `proj1` / `proj2` / union |
| `R~` | `converse` / `def7` | `[x,y] ∈ it` iff `[y,x] ∈ R` |
| `P*R` | `comp` / `def8` | relational composition |
| `id X` | `id` / `def10` | `[x,y] ∈ it` iff `x ∈ X ∧ x = y` |
| `R` restricted to `X` | `restrict` / `def11` | Mizar `R\|X` |
| `Y` range-restricts `R` | `restrictRng` / `def12` | Mizar range restriction |
| `R.:X` | `image` / `def13` | direct image |
| `R"Y` | `invimage` / `def14` | inverse image |
| `Im(R,x)` / `Coim(R,x)` | `Im` / `Coim` | `R.:{x}` / `R"{x}` |
| `X-defined` / `X-valued` | `isXdefined` / `isXvalued` | `def18` / `def19` |
| `RELAT_1:1`–`186` | `th1`–`th186` | skip canceled numbers |
| schemes | `sch_RelExistence`, `sch_ExtensionalityR` | pair Separation; extensionality |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `FUNCT_1`.

## 14. Functions (`FUNCT_1`)

A function is a function-like relation. Environ: `TARSKI`,
`XBOOLE_0`, `XBOOLE_1`, `XTUPLE_0`, `ZFMISC_1`, `SUBSET_1`,
`SETFAM_1`, `RELAT_1`. Import is `RELAT_1` and `SETFAM_1`.
Mizar `g*f` is `RELAT_1.comp f g` (apply `f` then `g`).
Canceled: `th30`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `FUNCT_1:def 1` | `isFunctionLike` / `isFunction` / `def1` | unique value at each `x` |
| `f.x` | `apply` / `def2` | `∅` off the domain |
| `FUNCT_1:def 4` | `isOneToOne` / `def4` | injective on `dom` |
| `f"` | `inv` / `def5` | `converse` of a 1-1 function |
| `f\|X` / range-restrict | `restrict` / `restrictRng` | function-like restrictions |
| `f.:X` / `f"Y` | `image` / `invimage` / `def6` / `def7` | via `apply` |
| `empty-yielding` / `non-empty` | `def8` / `def9` | `isEmptyYieldingSet` / `isEmptyYielding` |
| `constant` | `isConstant` / `def10` | equal values on `dom` |
| `the_value_of f` | `the_value_of` | nonempty constant |
| `functional` | `isFunctional` / `def13_functional` | set of functions |
| `g-compatible` | `isCompatible` / `def14_compatible` | `f.x ∈ g.x` |
| `FUNCT_1:1`–`111` | `th1`–`th111` | skip canceled `30` |
| schemes | `sch_GraphFunc`, `sch_FuncEx`, `sch_Lambda`, `sch_LambdaB`, `sch_NonUniqBoundFuncEx` | graph, lambda, bounded choice |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `GRFUNC_1`.

## 15. Graphs of functions (`GRFUNC_1`)

A subset of a function is a function. Environ: `TARSKI`,
`XBOOLE_0`, `XBOOLE_1`, `ENUMSET1`, `XTUPLE_0`, `ZFMISC_1`,
`SUBSET_1`, `RELAT_1`, `FUNCT_1`. Import is `FUNCT_1` and
`ENUMSET1`. Canceled: `th18`, `th19`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `GRFUNC_1:1` | `th1` | `G ⊆ f` implies `G` is a function |
| `GRFUNC_1:2` | `th2` | inclusion iff domain inclusion and pointwise `apply` |
| `GRFUNC_1:5`–`8` | `th5`–`th8` | singleton and two-point graphs |
| `GRFUNC_1:13`–`17` | `th13`–`th17` | union when domains miss or both sit in `h` |
| restriction | `th22`–`th25` | domain restrict and range restrict |
| `GRFUNC_1:28`–`31` | `th28`–`th31` | restrict to a singleton, pair, or triple |
| `g-compatible` | `compatible_of_subset` / `compatible_subset` | along `g ⊆ f` |
| `GRFUNC_1:1`–`35` | `th1`–`th35` | skip canceled `18`, `19`; locals `lm1`–`lm3` |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `RELAT_2`.

## 16. Properties of binary relations (`RELAT_2`)

Reflexive, symmetric, transitive, and related attributes of a
relation. Environ: `TARSKI`, `XBOOLE_0`, `XTUPLE_0`, `ZFMISC_1`,
`SUBSET_1`, `RELAT_1`. Import is `RELAT_1` only. Canceled:
`th5`–`th11`, `th14`–`th21`, `th23`–`th26`, `th29`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `RELAT_2:def 1`–`8` | `isReflexiveIn` … `isTransitiveIn` | attributes on a set `X` |
| `RELAT_2:def 9`–`16` | `isReflexive` … `isTransitive` | same on `field R` |
| `RELAT_2:1`–`4` | `th1`–`th4` | `id` characterizations; anti/asymm via `id` |
| `RELAT_2:12`–`13` | `th12`–`th13` | reflexive domains; `R` symmetric iff `R = R~` |
| `RELAT_2:22` | `th22` | antisymmetric iff `R ∩ R~ ⊆ id (dom R)` |
| `RELAT_2:27`–`28` | `th27`–`th28` | `R*R ⊆ R`; connected via the field square |
| `RELAT_2:30`–`31` | `th30`–`th31` | strongly connected; transitivity without field |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `ORDINAL1`.

## 17. Ordinal numbers (`ORDINAL1`)

Epsilon-transitive, epsilon-connected ordinals, successors, transfinite
induction, T-sequences, and `omega`. Environ: `TARSKI`, `XBOOLE_0`,
`XBOOLE_1`, `ENUMSET1`, `XTUPLE_0`, `XREGULAR`, `ZFMISC_1`,
`SUBSET_1`, `RELAT_1`, `FUNCT_1`. Import is `FUNCT_1` and `XREGULAR`.
Canceled: `th1`–`th4`. Generalized infinity (`th36`) uses a
`Nat`-indexed successor chain in this model (Mizar uses
`ZFMISC_1:112` bool-closure, which the Lean universe does not yet
prove).

| Mizar | Lean | Notes |
| --- | --- | --- |
| `ORDINAL1:def 1` | `succ` / `def1` | `X ∪ {X}` |
| `ORDINAL1:def 2`–`4` | `isEpsilonTransitive` / `isEpsilonConnected` / `isOrdinal` | ordinal attributes |
| `ORDINAL1:def 5` | `def5` | `c=` on ordinals |
| `ORDINAL1:def 6` | `isLimitOrdinal` / `def6` | `A = union A` |
| `ORDINAL1:def 7` | `isTSequenceLike` / `isTSequence` | `dom` is an ordinal |
| `ORDINAL1:def 8` | `isCLinear` / `def8` | pairwise `c=`-comparable |
| `ORDINAL1:def 9`–`12` | `On` / `Lim` / `omega` / `isNatural` | ordinals of `X`; least limit over `∅` |
| `ORDINAL1:5`–`37` | `th5`–`th37` | skip canceled `1`–`4`; unlabeled blocks numbered consecutively |
| schemes | `sch_OrdinalMin` / `sch_TransfiniteInd` / `sch_TSUniq` / `sch_TSExist` / `sch_FuncTS` / `sch_ALFA` | min, induction, recursion |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `WELLORD1`.

## 18. The well ordering relations (`WELLORD1`)

Well-founded and well-ordering relations, initial segments, the
`|_2` restriction, transfinite induction, and order-isomorphism
comparability. Environ: `TARSKI`, `XBOOLE_0`, `XBOOLE_1`,
`XTUPLE_0`, `ZFMISC_1`, `SUBSET_1`, `RELAT_1`, `FUNCT_1`,
`RELAT_2`. Import is `FUNCT_1` and `RELAT_2`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `WELLORD1:lm 1`–`4` | `lm1`–`lm4` | refl / trans / anti / connected via `field` |
| `R-Seg(a)` | `seg` | `Coim(R,a) \ {a}` |
| `WELLORD1:def 2`–`5` | `isWellFounded` / `isWellFoundedIn` / `isWellOrdering` / `wellOrders` | well-founded; well-order |
| `WELLORD1:def 6` | `restrict2` | `R ∩ [:Y,Y:]` |
| `WELLORD1:def 7`–`9` | `isIsomorphismOf` / `areIsomorphic` / `canonical_isomorphism_of` | order isomorphism |
| `WELLORD1:1`–`37` | `th1`–`th37` | segments, restrict, induction, `id` iso |
| unlabeled `L947` | `th38` | `R ≅ R` |
| `WELLORD1:39`–`52` | `th39`–`th52` | inverse/compose; uniqueness; comparability |
| unlabeled `L1809` | `th53` | restriction of a well-order is comparable |
| unlabeled `L1853` | `th54` | isomorphism preserves well-order |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `RELSET_1`.

## 19. Relations defined on sets (`RELSET_1`)

Relations as subsets of a cartesian product. Environ: `TARSKI`,
`XBOOLE_0`, `XBOOLE_1`, `XTUPLE_0`, `ZFMISC_1`, `SUBSET_1`,
`RELAT_1`. Import is `RELAT_1` only.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `Relation of X,Y` | `isRelationOf` | `R ⊆ [:X,Y:]` |
| `RELSET_1:1`–`12` | `th1`–`th12` | subset, pairs, empty, field, total dom/rng |
| `RELSET_1:13`–`15` | `th13`–`th15` | `id X ⊆ [:X,X:]`; `id` vs dom/rng |
| unlabeled `L415`–`L507` | `th16`–`th21` | `id` equalities; restrict / range-restrict |
| `RELSET_1:22` | `th22` | `R.:X = rng R`, `R"Y = dom R` |
| unlabeled `L580` | `th23` | `R.:(R"Y) = rng`, `R"(R.:X) = dom` |
| `RelOnSetEx` / `RelOnDomEx` | `sch_RelOnSetEx` / `sch_RelOnDomEx` | existence of a relation of sets |
| unlabeled `L632`–`L726` | `th24`–`th30` | elementwise dom/rng/comp/image |
| `L758` / `L822` | `sch_ImEx` / `sch_RelEq` | image specification; equality |
| unlabeled `L790` / `L853` | `th31` / `th32` | `Im` determines `R`; miss restrict |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `PARTFUN1`.

## 20. Partial functions (`PARTFUN1`)

Functions that are relations of `X,Y`. Environ: `TARSKI`,
`XBOOLE_0`, `XBOOLE_1`, `XTUPLE_0`, `ZFMISC_1`, `SUBSET_1`,
`RELAT_1`, `FUNCT_1`, `GRFUNC_1`, `RELAT_2`, `RELSET_1`. Import is
`GRFUNC_1`, `RELAT_2`, and `RELSET_1`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `PartFunc of X,Y` | `isPartFunc` | Function ∧ `Relation of X,Y` |
| `PARTFUN1:1`–`2` | `th1`–`th2` | union of pointwise-agreeing functions |
| `LambdaC` / `PartFuncEx` / `LambdaR` | `sch_LambdaC` / `sch_PartFuncEx` / `sch_LambdaR` | existence schemes |
| `PARTFUN1:3`–`14` | `th3`–`th14` | apply, equality, `id`, 1-1, restrict as PartFunc |
| `<:f,X,Y:>` | `clip` | `Y\|`f\|X` |
| unlabeled `L384`–`L450` | `th15`–`th21` | image; singleton domain/codomain |
| `PARTFUN1:22`–`37` | `th22`–`th37` | clip ⊆, dom/apply, mono, compose, 1-1 |
| unlabeled `L782` | `th38` | `(clip f X Y)⁻¹ = clip (f⁻¹) Y X` |
| unlabeled `L848` | `th39` | `Z\|`clip = clip f X (Z ∩ Y)` |
| `PARTFUN1:def 2` | `isTotal` / `def2` | `dom f = X` |
| `PARTFUN1:40`–`44` | `th40`–`th44` | totality of clip |
| `PFuncs` / `def 3` | `PFuncs` / `def3` | set of partial functions |
| `PARTFUN1:45`–`50` | `th45`–`th50` | membership; empty; subset |
| `tolerates` / `def 4` | `tolerates` / `def4` | pointwise on `dom f ∩ dom g` |
| `PARTFUN1:51`–`67` | `th51`–`th67` | tolerance vs union / totals |
| `PARTFUN1:68` / `TotFuncs` | `th68` / `TotFuncs` / `def5` | common total extension |
| `PARTFUN1:69`–`76` | `th69`–`th76` | `TotFuncs` membership; meets ↔ tolerate |
| `lm 2`–`4` / `LambdaC9` | `lm2`–`lm4` / `sch_LambdaC9` | `id X` total / equiv; LambdaC on nonempty |
| `PARTFUN1:77`–`80` / `def 6` | `th77`–`th80` / `apply_at` | tolerate uniqueness; union; `p/.i` |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `MCART_1`.

## 21. Tuples, projections, Cartesian products (`MCART_1`)

Pair/triple/quadruple projections and products. Environ: `TARSKI`,
`XBOOLE_0`, `ZFMISC_1`, `SUBSET_1`, `XTUPLE_0`, `RELAT_1`,
`FUNCT_1`, `ENUMSET1`, `XREGULAR`. Import is `FUNCT_1`,
`ENUMSET1`, and `XREGULAR`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `MCART_1:7`–`8` / `10` | `th7`–`th8` / `th10` | pair projections; pair membership |
| unlabeled `L52`–`L220` | `th9` / `th11`–`th24` | regularity vs pairs; product facts |
| `lm 1` / `MCART_1:23`–`24` | `lm1` / `th23`–`th24` | pair witnesses; finite products |
| `MCART_1:26` / `30`–`32` | `th26` / `th30`–`th32` | `product3` nonemptiness / projections |
| unlabeled `L319`–`L428` | `th33`–`th43` | triple components; eta |
| `def 5`–`7` / `lm 2` | `def5`–`def7` / `lm2` | `fst3`/`snd3`/`thd3` |
| `MCART_1:45` / `47`–`52` | `th45` / `th47`–`th52` | `product3` subset empty; meets; `product4` |
| unlabeled `L667`–`L845` | `th53`–`th55` | `product4` equality / eta |
| `def 8`–`11` / `lm 3` | `def8`–`def11` / `lm3` | `fst4`/`snd4`/`thd4`/`fth4` |
| unlabeled `L852`–`L1077` | `th56`–`th70` / `th72`–`th73` | `product4` regularity; `product3` ext. |
| unlabeled `L1114`–`L1266` / `Th84` | `th74`–`th81` / `th83`–`th84` | `product4` projections; mono |
| `pr1`/`pr2` / `x\`11` | `pr1`/`pr2` / `fst11`…`snd22` | function projections; nest |
| unlabeled `L1396`–`L1469` / `Th87`/`Th89` | `th85`–`th92` | image; equal pairs; `proj1` of triples |
| `sch BiFuncEx` | `sch_BiFuncEx` | two functions from a ternary predicate |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `FUNCT_2`.

## 22. Zermelo Theorem and the Axiom of Choice (`WELLORD2`)

Inclusion order, order types, Zermelo well-ordering, and choice from
a well-ordering of `union M`. Environ: `TARSKI`, `XBOOLE_0`,
`ZFMISC_1`, `SUBSET_1`, `RELAT_1`, `FUNCT_1`, `RELAT_2`, `ORDINAL1`,
`WELLORD1`, `MCART_1`. Import is `WELLORD1`, `MCART_1`, and
`ORDINAL1`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `WELLORD2:def 1` | `RelIncl` / `def1` | inclusion relation on `X` |
| `WELLORD2:1`–`6` | — | canceled |
| `WELLORD2:7`–`9` | `th7`–`th9` | restrict `RelIncl`; segments |
| `WELLORD2:10`–`11` | `th10`–`th11` | uniqueness of order type |
| `WELLORD2:12`–`13` | `th12`–`th13` | existence of order type |
| `WELLORD2:def 2` | `order_type_of` / `def2` | order type of a well-ordering |
| unlabeled `L561` | `th14` | order type of a subset |
| unlabeled after `L591` | `are_equipotent_fun` / `th15` | equipotence via functions |
| `WELLORD2:16` | `th16` | restrict well-ordering |
| `WELLORD2:lm 1` | `lm1` | well-ordering along equipotence |
| `WELLORD2:17` | `th17` | Zermelo (Hartogs + enumeration) |
| unlabeled `L968` | `th18` | Axiom of Choice |
| addenda `L1058`–`L1135` | `RelIncl_*_in` / `RelIncl_empty` / … | `RelIncl` on `X`; empty; singleton; product |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `BINOP_1`.

## 23. Functions from a set to a set (`FUNCT_2`)

Total / quasi-total functions, `Funcs(X,Y)`, onto and bijective maps,
permutations, images of families, and `p/*f`. Environ: `TARSKI`,
`XBOOLE_0`, `XBOOLE_1`, `XTUPLE_0`, `ZFMISC_1`, `SUBSET_1`,
`SETFAM_1`, `MCART_1`, `RELAT_1`, `RELAT_2`, `FUNCT_1`, `RELSET_1`,
`PARTFUN1`. Import is `PARTFUN1`, `MCART_1`, and `SETFAM_1`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `FUNCT_2:def 1` | `isQuasiTotal` / `def1` | `dom = X` if `Y ≠ ∅`, else empty |
| `Function of X,Y` | `isFunctionOf` | quasi-total PartFunc |
| `FUNCT_2:def 2` | `Funcs` / `def2` | set of total functions into `Y` |
| `FUNCT_2:1`–`36` | `th1`–`th36` | typing; apply; equality; image |
| `FUNCT_2:37` | — | canceled |
| `FUNCT_2:38`–`61` | `th38`–`th61` | preimage; onto; bijective; perm |
| `FUNCT_2:def 3`–`4` | `isOnto` / `isBijective` / `isPermutation` | |
| schemes | `sch_FuncEx1` … `sch_MChoice` | Lambda / choice schemes |
| `FUNCT_2:62`–`91` | `th62`–`th91` | perm images; TotFuncs |
| `FUNCT_2:def 5`–`6` | `pr1` / `pr2` redefs | via `MCART_1` |
| `FUNCT_2:def 9`–`11` | `invimageFamily` / `imageFamily` / `composeAlong` | |
| `FUNCT_2:92`–`125` | `th92`–`th125` | families; `p/*f`; Action |
| `FUNCT_2:def 12` | `isFunctionDomain` | nonempty set of functions |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `DOMAIN_1`.

## 24. Binary operations (`BINOP_1`)

Binary application `f.(a,b)`, unary/binary operations on a set,
commutativity / associativity / idempotence, unities, and
distributivity. Environ ends at `FUNCT_2`. Import is `FUNCT_2` only.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `f.(a,b)` / Def1 | `apply2` / `def1` | `f.[a,b]` |
| `UnOp` / `BinOp` | `isUnOp` / `isBinOp` | Function of `X` / `[:X,X:]` |
| `Th1`–`Th15` + unlabeled | `th1`–`th16` | equality; unities; dist. |
| Def2–12 | commutative … unOp-dist | attrs and `the_unity_wrt` |
| schemes | `sch_FuncEx2` … `sch_PartLambda2D` | existence / lambda |
| addenda | `th17`–`th20` / `eq_iff_apply2` | FUNCT_2 / PARTFUN1 links |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `FUNCT_3`.

## 25. Domains and their Cartesian products (`DOMAIN_1`)

Domain facts for pairs/triples/quadruples, Fraenkel schemes on
products, and enumset/singleton subset redefines. Environ ends at
`ORDINAL1` / `MCART_1`. Import is `MCART_1` and `ORDINAL1`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `DOMAIN_1:1`–`34` | `th1`–`th34` | product domains; boolean ops |
| Fraenkel / Subset schemes | `sch_Fraenkel1`–`6` / `sch_Subset*` / `sch_AndScheme` | |
| redefines | pair/triple/quad / enumset subsets | coherence |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Sequential next unused was
`FUNCT_3` (parallel: `MULTOP_1` done).

## 26. Three- and four-argument operations (`MULTOP_1`)

`f.(a,b,c)` / `f.(a,b,c,d)`, ternary and quaternary ops on a set.
Environ ends at `FUNCT_2` / `DOMAIN_1`. Import is `FUNCT_2` only.

| Mizar | Lean | Notes |
| --- | --- | --- |
| Def1 / Def2 | `apply3` / `apply4` | apply on triples / quads |
| `TriOp` / `QuaOp` | `isTriOp` / `isQuaOp` | |
| `Th1`–`Th5` + unlabeled | `th1`–`th6` | equality / typing |
| schemes | `sch_FuncEx3D` … `sch_QuaOpLambda` | 8 schemes |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Sequential next unused was
`FUNCT_3`.

## 27. Basic functions and operations on functions (`FUNCT_3`)

Image / inverse-image functionals, characteristic and inclusion maps,
projections, diagonal, `<:f,g:>` / `[:f,g:]`, and product identities.
Environ ends at `BINOP_1` / `DOMAIN_1`. Import is both.

| Mizar | Lean | Notes |
| --- | --- | --- |
| Def1–Def2 | `imageFunc` / `invimageFunc` | image / preimage functionals |
| Def3–Def6 | `chi` / `incl` / `pr1` / `pr2` / `delta` | characteristic; incl; projs |
| Def7–Def8 | `complex` / `productFunc` | `<:f,g:>` / `[:f,g:]` |
| schemes | `sch_FuncEx3` / `sch_Lambda3` | |
| `FUNCT_3:1`–`80` | `th1`–`th80` | absolute theorem slots |
| registrations | `productFunc_oneToOne` / idempotent binop | |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `FUNCOP_1`.

## 28. Some properties of binary relations (`SYSREL`)

Diagonal facts and the closure relation `CL R = R ∩ id(dom R)`.
Environ ends at `RELAT_1`. Import is `RELAT_1` only.

| Mizar | Lean | Notes |
| --- | --- | --- |
| locals | `lm1` / `lm2` | nonempty products; `id` facts |
| `SYSREL:1`–`40` | `th1`–`th40` | absolute theorem slots |
| Def | `CL` / `CL_eq` | `R ∩ RELAT_1.id (dom R)` |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Sequential next unused was
`FUNCOP_1` (parallel: `WELLSET1`).

## 29. Binary operations applied to functions (`FUNCOP_1`)

Pair-swap `f~`, constant maps `A --> z`, binary ops applied to
functions (`F.:(f,g)`, `F[:]`, `F[;]`), `IFEQ`, and
function-/relation-yielding maps. Environ ends at `FUNCT_3` /
`WELLORD1`. Import is both.

| Mizar | Lean | Notes |
| --- | --- | --- |
| Def1–Def8 | `tilde` / `mapsTo` / `applied*` / `IFEQ` / `dotArrow` | |
| locals | `lm1` / `lm2` | |
| `FUNCOP_1:1`–`89` | `th1`–`th89` | absolute slots; `th46` with `x ∈ X` |
| attrs | `isFunctionYielding` / `isRelationYielding` | |

**Complete?** Yes. `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`. Next unused: `FUNCT_4`.

## 30. Modification of a function by a function (`FUNCT_4`)

Function override, domain-coordinate swap, paired function products,
two-point maps, and replacement of a value throughout a range.
Environ reduces to `FUNCOP_1` and `ORDINAL1`; both are imported.

| Mizar | Lean | Notes |
| --- | --- | --- |
| Def1–Def5 | `override` / `swapDom` / `productPair` / `pairMapsTo` / `rangeUpdate` | principal constructions |
| `FUNCT_4:1`–`125` | `th1`–`th125` | all absolute theorem slots |
| registrations | `override_*` / `pairMapsTo_*` / `dotArrow_isTrivial` | includes the Def4 redefinition as `pairMapsTo_isFunctionOf`; function, partial-function, yielding, domain/range, and compatibility closure |

**Complete?** Yes. Full `lake build` and Challenge/Solution type
comparison pass; no `sorry`. Representative `#print axioms` checks are
contained in `{propext, Classical.choice, Quot.sound}`. The numbered
declarations align one-to-one with all 125 absolute Mizar theorem slots.
Next unused: `ORDINAL2`.

## 31. Sequences and arithmetic of ordinals (`ORDINAL2`)

Ordinal sequences, suprema and infima, limits, ordinal addition,
multiplication and exponentiation, and transfinite recursion.

| Mizar | Lean | Notes |
| --- | --- | --- |
| Def1–Def17 | `def1`–`def17` | sequence operations, limits, and ordinal arithmetic |
| `ORDINAL2:1`–`50` | `th1`–`th50` | all absolute theorem slots |
| 20 schemes | `sch_OrdinalInd` through `sch_LambdaRecUn` | induction and transfinite recursion |
| registrations | named `*_isOrdinal`, `*_isNatural`, and sequence theorems | all ten registrations |

Mizar typing predicates become explicit hypotheses. The overloaded
sequence operations `sup` and `inf` are `sequenceSup` and
`sequenceInf`; guarded `lim` defaults to the empty ordinal outside its
guard.

**Complete?** Yes. No canceled slots or `sorry`; verification and axiom
checks pass.

## 32. Zermelo's theorem (`WELLSET1`)

Well-order extension and separation results culminating in Zermelo's
well-ordering theorem.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `WELLSET1:1`–`6` | `th1`–`th6` | all theorem slots |
| Lm1 / RSeparation | `lm1` / `sch_RSeparation` | auxiliary lemma and scheme |

The final theorem retains Mizar's statement while reusing the
axiom-free `WELLORD2.th17` construction.

**Complete?** Yes. No source definitions, registrations, canceled
items, or `sorry`; verification and axiom checks pass.

## 33. Partial functions between domains (`PARTFUN2`)

Composition, restriction, constant partial functions, images, and
pointwise criteria for partial functions.

| Mizar | Lean | Notes |
| --- | --- | --- |
| five redefinitions | `id_isPartFunc` / `inv_isPartFunc` / `restrictRng_isPartFunc` / `mapsTo_isPartFunc` / `def_constant` | identity, inverse, restriction, constant map, constant predicate |
| `PARTFUN2:1`–`61` | `th1`–`th61` | all absolute theorem slots |
| 3 schemes | `sch_PartFuncExD` / `sch_LambdaPFD` / `sch_UnPartFuncD` | all source schemes |

**Complete?** Yes. No registrations, canceled items, or `sorry`;
verification and axiom checks pass. `ORDINAL3` follows below.

## 34. Ordinal arithmetic (`ORDINAL3`)

Order properties of ordinal addition and multiplication, pointwise
operations on ordinal sequences, subtraction, Euclidean division and
remainder, and natural-ordinal arithmetic.

| Mizar | Lean | Notes |
| --- | --- | --- |
| Def1–Def4 | `addLeftSequence` / `addRightSequence` / `mulLeftSequence` / `mulRightSequence` | pointwise sequence operations |
| Def5–Def7 | `ordinalSub` / `ordinalDiv` / `ordinalMod` | subtraction, quotient, remainder |
| `ORDINAL3:1`–`75` | `th1`–`th75` | all absolute theorem slots |
| registrations / redefinitions | `union_isOrdinal` / `inter_isOrdinal` / `sub_natural` / `mul_natural` / `add_comm_natural` / `mul_comm_natural` | all source registrations and natural commutativity redefinitions |

The source has one lemma (`lm1`), no local schemes, and no canceled
slots.

**Complete?** Yes. Full build and Challenge/Solution comparison pass;
no `sorry`. Representative axiom checks are contained in
`{propext, Classical.choice, Quot.sound}`. `FINSET_1` follows below.

## 35. Finite sets (`FINSET_1`)

Finite and infinite sets, closure under set/relation constructions,
finite induction, centered families, finite-yielding functions, and
finite-membered families.

| Mizar | Lean | Notes |
| --- | --- | --- |
| Def1–Def6 | `isFinite` / `isFiniteYielding` / `isCentered` / `isFiniteMembered` plus redefinition theorems | all six definition blocks |
| `FINSET_1:1`–`15` | `th1`–`th15` | all absolute theorem slots |
| Lm1–Lm3 | `lm1`–`lm3` | finite singleton, union, and family-union lemmas |
| 2 schemes | `sch_OLambdaC` / `sch_Finite` | conditional ordinal lambda and finite induction |
| registrations | named closure and existence theorems | all 54 registration claims |

The source has no canceled slots; `isInfinite` represents Mizar's
antonym notation.

**Complete?** Yes. Full build and Challenge/Solution comparison pass;
no `sorry`. Representative axiom checks are contained in
`{propext, Classical.choice, Quot.sound}`. Next unused: `FINSUB_1`.

## Lean Code

- [`MizarCCL/HIDDEN.lean`](MizarCCL/HIDDEN.lean) — `TarskiSet` and `∈`
- [`MizarCCL/TARSKI.lean`](MizarCCL/TARSKI.lean) — TARSKI proofs
- [`MizarCCL/XBOOLE_0.lean`](MizarCCL/XBOOLE_0.lean) — Boolean definitions
- [`MizarCCL/XBOOLE_1.lean`](MizarCCL/XBOOLE_1.lean) — Boolean theorems
- [`MizarCCL/ENUMSET1.lean`](MizarCCL/ENUMSET1.lean) — enumerated sets
- [`MizarCCL/XTUPLE_0.lean`](MizarCCL/XTUPLE_0.lean) — pairs, tuples, projections
- [`MizarCCL/XREGULAR.lean`](MizarCCL/XREGULAR.lean) — regularity consequences
- [`MizarCCL/ZFMISC_1.lean`](MizarCCL/ZFMISC_1.lean) — power set and products
- [`MizarCCL/SUBSET_1.lean`](MizarCCL/SUBSET_1.lean) — elements and subsets
- [`MizarCCL/SETFAM_1.lean`](MizarCCL/SETFAM_1.lean) — families of sets
- [`MizarCCL/RELAT_1.lean`](MizarCCL/RELAT_1.lean) — relations
- [`MizarCCL/FUNCT_1.lean`](MizarCCL/FUNCT_1.lean) — functions
- [`MizarCCL/GRFUNC_1.lean`](MizarCCL/GRFUNC_1.lean) — graphs of functions
- [`MizarCCL/RELAT_2.lean`](MizarCCL/RELAT_2.lean) — properties of binary relations
- [`MizarCCL/ORDINAL1.lean`](MizarCCL/ORDINAL1.lean) — ordinal numbers
- [`MizarCCL/WELLORD1.lean`](MizarCCL/WELLORD1.lean) — well-ordering relations
- [`MizarCCL/RELSET_1.lean`](MizarCCL/RELSET_1.lean) — relations defined on sets
- [`MizarCCL/PARTFUN1.lean`](MizarCCL/PARTFUN1.lean) — partial functions
- [`MizarCCL/MCART_1.lean`](MizarCCL/MCART_1.lean) — tuples, projections, products
- [`MizarCCL/WELLORD2.lean`](MizarCCL/WELLORD2.lean) — Zermelo and choice
- [`MizarCCL/FUNCT_2.lean`](MizarCCL/FUNCT_2.lean) — functions from a set to a set
- [`MizarCCL/BINOP_1.lean`](MizarCCL/BINOP_1.lean) — binary operations
- [`MizarCCL/DOMAIN_1.lean`](MizarCCL/DOMAIN_1.lean) — domains and products
- [`MizarCCL/MULTOP_1.lean`](MizarCCL/MULTOP_1.lean) — multi-argument operations
- [`MizarCCL/FUNCT_3.lean`](MizarCCL/FUNCT_3.lean) — operations on functions
- [`MizarCCL/FUNCOP_1.lean`](MizarCCL/FUNCOP_1.lean) — ops applied to functions
- [`MizarCCL/FUNCT_4.lean`](MizarCCL/FUNCT_4.lean) — function modification
- [`MizarCCL/ORDINAL2.lean`](MizarCCL/ORDINAL2.lean) — ordinal sequences and arithmetic
- [`MizarCCL/ORDINAL3.lean`](MizarCCL/ORDINAL3.lean) — ordinal arithmetic
- [`MizarCCL/WELLSET1.lean`](MizarCCL/WELLSET1.lean) — Zermelo's theorem
- [`MizarCCL/SYSREL.lean`](MizarCCL/SYSREL.lean) — binary relation properties
- [`MizarCCL/FINSET_1.lean`](MizarCCL/FINSET_1.lean) — finite sets
- [`MizarCCL/PARTFUN2.lean`](MizarCCL/PARTFUN2.lean) — partial functions between domains
- [`Challenge.lean`](Challenge.lean) — Palomar statements
- [`Solution.lean`](Solution.lean) — re-export of the proofs
