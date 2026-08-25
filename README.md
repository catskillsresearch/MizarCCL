# yellow17

Lean 4 translation of Bartłomiej Skorulski, *The Tichonov Theorem*
(Mizar article `YELLOW_17`), packaged for Palomar.

The Mizar source is copied from the
[Mizar Mathematical Library](https://github.com/MizarSystem/MML.git)
file [`mml/yellow17.miz`](https://github.com/MizarSystem/MML/blob/047822c4d814630b28eec8ca6b455e9eb912d5ff/mml/yellow17.miz)
at revision `047822c4d814630b28eec8ca6b455e9eb912d5ff`. See
`mml/FROZEN.txt` and `PROVENANCE.md`.

The **Palomar statement of record** is every theorem and definition in
`Yellow17.lean` (headline: `yellow17_tychonoff` /
`yellow17_tychonoff_sets`). Tychonoff’s theorem itself is prior; this
package is the translation, not a first proof.

The paper of record is `view.pdf` (source `arxiv.md`).

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `Yellow17`, `Challenge`, and `Solution`.
`Challenge.lean` imports only Mathlib and leaves the compared
declarations as `sorry`. `Solution.lean` re-exports the sorry-free
`Yellow17.lean` proofs.

```bash
bash scripts/palomar_preflight.sh
bash scripts/build_arxiv_pdf.sh
```

Narrative inventory: `arxiv.md`. Palomar metadata: `comparator.json`,
`formalization.yaml`. Session resume: `HANDOFF.md`.

## License

The Mizar article is © 2000–2012 Association of Mizar Users and is
distributed under **GPL-3.0-or-later** or **CC-BY-SA-3.0-or-later**.
This Lean translation is a derivative work under the same dual
license. Full texts: `doc/COPYING.GPL`, `doc/COPYING.CC-BY-SA`,
`doc/COPYING.interpretation`.
