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
theorems of `Type u` and are not claimed.

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
  Lean does not treat `Type u` as a ZFC inaccessible.

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
- [`Challenge.lean`](Challenge.lean) — Palomar statements
- [`Solution.lean`](Solution.lean) — re-export of the proofs
