# Contributing to This Repository

Thank you for your interest in this research! This document outlines how to engage, provide feedback, and potentially contribute.

---

## For Formal Verification Experts

### Code Review

If you're a Lean expert or formal verification researcher:

1. **Start with `/proofs/`** — Review the 177 declarations for:
   - Correctness of formal statements
   - Elegance and conciseness of proofs
   - Alignment with Lean best practices
   - Potential for mathlib integration

2. **Open an issue** with feedback:
   - Tag: `review-requested`
   - Include: Line numbers, suggestions, references
   - Be constructive; this is learning research

3. **Example feedback:**
   ```
   File: proofs/lattice_points/visible_density.lean
   Line: 42
   Issue: Type annotation could be simplified using `simp`
   Suggestion: Replace `by rfl` with `by simp [definition]`
   ```

---

## For PhD Researchers & Methodologists

### Methodological Critique

If you're evaluating the research design:

1. **Read `RESEARCH_NOTES.md`** — Pay special attention to:
   - Limitations section
   - n=1 caveat
   - Open questions

2. **Open an issue** with methodological questions:
   - Tag: `methodology`
   - Example: "How would you design the n=2 replication?"

3. **Suggest improvements:**
   - Study design
   - Bias mitigation
   - Semantic drift quantification

---

## For LLM & AI Researchers

### Multi-Agent Architecture Analysis

If you're studying LLM agents, multi-model systems, or semantic drift:

1. **Explore `/agent_prompts/`** — Review:
   - Claude's decomposition strategy
   - Gemini's refinement loops
   - Aristotle's error patterns

2. **Open an issue** with analysis:
   - Tag: `llm-research`
   - Focus on: Failure modes, efficiency, alignment

3. **Questions to explore:**
   - Where does semantic drift occur?
   - Can it be measured quantitatively?
   - What mitigations work best?

---

## For LEAN Community Members

### Proof Discussion & Questions

If you're using or interested in Lean:

1. **Ask questions** about any proof
   - Open an issue: `tag: question`
   - Example: "In visible_density.lean, why use type class instead of structure?"

2. **Suggest alternative proofs**
   - Open an issue: `tag: alternative-proof`
   - Include your proof sketch (no need for full Lean code initially)

3. **Identify bugs**
   - Open an issue: `tag: bug`
   - Include: Expected behavior, actual behavior, minimal example

---

## For Educators

### Educational Use

If you're teaching formal verification, theorem proving, or LLMs:

1. **Use this repo as a case study:**
   - Complexity inversion phenomenon
   - Semantic-gestalt mismatch
   - Multi-agent coordination

2. **Suggest pedagogical improvements:**
   - Open an issue: `tag: education`
   - Propose: Comments, explanations, examples

3. **Create derivatives:**
   - Fork this repo
   - Add educational materials
   - Link back (attribution appreciated)

---

## For General Public

### Interest in Formal Verification or Innovation?

1. **Start here:**
   - Read the main `README.md`
   - Read `RESEARCH_NOTES.md` (section 1: Error Detection)
   - Explore `/proofs/lattice_points/` for intuition

2. **Ask questions without assuming expertise:**
   - Open an issue: `tag: question`
   - Example: "What does 'semantic drift' mean in plain English?"

3. **Share this research:**
   - Link to the repository
   - Discuss on forums (LEAN forum, r/Lean, LessWrong, etc.)
   - Attribution appreciated

---

## Issue Templates

### Bug Report

```markdown
## Description
[What's wrong?]

## Location
File: [path/to/file.lean]
Line: [#]

## Expected Behavior
[What should happen?]

## Actual Behavior
[What actually happens?]

## Minimal Example
[If applicable, a small code snippet]

## Context
[Your background: Lean expert / researcher / curious / other]
```

### Methodological Question

```markdown
## Research Design Question
[Your question about the study methodology]

## Context
[What prompted this question?]

## Relevant Sections
[Links to README.md or RESEARCH_NOTES.md sections]

## Why It Matters
[Why does this question matter to your work?]
```

### Code Review

```markdown
## Review Feedback

### Location
File: [path/to/file.lean]
Lines: [#-#]

### Issue Type
[ ] Correctness  [ ] Style  [ ] Efficiency  [ ] Alignment with mathlib

### Feedback
[What needs improvement?]

### Suggestion
[How to improve it?]

### Rationale
[Why is this suggestion better?]

### References
[Links to relevant resources: papers, mathlib docs, etc.]
```

---

## Code of Conduct

- ✅ **Be constructive** — Offer improvements, not just criticism
- ✅ **Be respectful** — This is learning research; the researcher is learning too
- ✅ **Be clear** — Explain your reasoning, provide examples
- ✅ **Be helpful** — If you spot a bug, suggest a fix

- ❌ **Don't be dismissive** — "This is obvious" isn't feedback
- ❌ **Don't assume bad faith** — Assume the researcher tried their best
- ❌ **Don't derail** — Stay on topic; create separate issues for unrelated topics

---

## Pull Requests

### What We Accept

- ✅ Bug fixes (with issue reference)
- ✅ Improved proofs (with explanation)
- ✅ Documentation clarifications
- ✅ Educational materials
- ✅ Additional examples or test cases

### What We Don't Accept (Yet)

- ❌ New mathematical domains (discuss first via issue)
- ❌ Major architectural changes (discuss first via issue)
- ❌ Breaking changes to proofs (needs rationale)

### PR Process

1. Open an issue first (describe the change)
2. Wait for feedback from the researcher
3. Fork the repo and create a branch: `fix/issue-123`
4. Make your changes
5. Submit PR with:
   - Reference to the issue
   - Clear explanation of changes
   - Any relevant documentation updates
6. Respond to review feedback

---

## Attribution & Reuse

### Citation

If you use this research:

```bibtex
@report{wabnig2026lean,
  title={Accessibility of Formal Theorem Proving via LLM Agents},
  author={Wabnig, Thomas},
  year={2026},
  month={May},
  url={https://github.com/wabnigt-byte/LEAN}
}
```

### License

This work is licensed under the MIT License. You are free to:
- Use for research and education
- Modify and extend
- Publish derivatives

Simply attribute the original work.

---

## Getting Help

### Questions

- 🤔 **General question?** Open an issue with `tag: question`
- 💬 **Community discussion?** Post on [LEAN Forum](https://leanprover.zulipchat.com/)
- 📧 **Private question?** Email: wabnig@gmail.com

### Resources

- **LEAN documentation:** https://lean-lang.org/
- **mathlib4 docs:** https://docs.lean-lang.org/
- **LEAN community:** https://leanprover.zulipchat.com/

---

## Recognition

Contributors will be acknowledged in:
1. The repository `CONTRIBUTORS.md` file
2. Relevant PR/issue comments
3. Future publications (if applicable)

---

**Thank you for your interest in advancing formal verification and LLM-assisted proof development!**

Last Updated: May 17, 2026
