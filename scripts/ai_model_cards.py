"""Model-card registry for the AI-assisted development acknowledgements block."""

from __future__ import annotations

import re
from dataclasses import dataclass

TOOL_BULLETS_BEGIN = "<!-- AI_MODEL_TOOL_BULLETS -->"
TOOL_BULLETS_END = "<!-- /AI_MODEL_TOOL_BULLETS -->"
REFERENCES_BEGIN = "<!-- AI_MODEL_REFERENCES -->"
REFERENCES_END = "<!-- /AI_MODEL_REFERENCES -->"


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    reference: str


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="Cursor",
        cite_key="Cur26",
        tool_note=(
            "agent-assisted editing in the Cursor IDE: Lean 4 translation of "
            "Mizar YELLOW_17, Palomar Challenge/Solution packaging, and this "
            "narrative (`arxiv.md`). Generated Lean was provisional until it "
            "compiled under Lean / mathlib v4.33.0."
        ),
        reference=(
            "Anysphere, Inc. *Cursor: AI-native code editor and agent environment*. "
            "https://cursor.com/ (2026)."
        ),
    ),
    ModelCard(
        label="Cursor Grok 4.6",
        cite_key="Grk26",
        tool_note=(
            "primary agent (SpaceXAI / Cursor) for Yellow17.lean and the Palomar kit."
        ),
        reference=(
            "xAI / SpaceXAI and Cursor. *Grok 4.6* conversational coding model, "
            "used via the Cursor agent (2026)."
        ),
    ),
)

ACKNOWLEDGMENTS_MARKDOWN = """## Acknowledgments

The human author retains sole responsibility for the mathematical content.
No large language model is listed as a co-author.

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

The development is at
[`github.com/catskillsresearch/yellow17`](https://github.com/catskillsresearch/yellow17).

"""


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** **[{card.cite_key}]** — {card.tool_note}" for card in MODEL_CARDS
    )


def render_model_references() -> str:
    return "\n".join(f"- **[{card.cite_key}]** {card.reference}" for card in MODEL_CARDS)


def inject_acknowledgments(text: str) -> str:
    if re.search(r"^##\s+Acknowledgments\s*$", text, re.MULTILINE):
        return text
    m = re.search(r"^##\s+References\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError("missing ## References in narrative")
    return text[: m.start()] + ACKNOWLEDGMENTS_MARKDOWN + "\n" + text[m.start() :]


def inject_model_cards(text: str) -> str:
    text = inject_acknowledgments(text)
    if REFERENCES_BEGIN not in text:
        text = text.replace(
            "## References\n",
            "## References\n\n" + REFERENCES_BEGIN + "\n" + REFERENCES_END + "\n",
        )
    if TOOL_BULLETS_BEGIN not in text:
        raise RuntimeError(f"missing {TOOL_BULLETS_BEGIN}")
    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, render_model_references())
    return text


def _replace_between(text: str, begin: str, end: str, body: str) -> str:
    start = text.index(begin)
    stop = text.index(end, start)
    stop_end = stop + len(end)
    inner_start = start + len(begin)
    if inner_start < stop and text[inner_start : inner_start + 1] == "\n":
        inner_start += 1
    if inner_start < stop and text[stop - 1 : stop] == "\n":
        stop -= 1
    return text[:start] + begin + "\n" + body + "\n" + end + text[stop_end:]
