## Language Policy for Documentation and Code Comments

### Markdown Documentation

**All Markdown (`.md`) content written by AI agents MUST be in English.**

- Always write new Markdown content in English.
- When editing existing Markdown files, write all newly added or rewritten content in English, regardless of the language used in the surrounding text.
- Never imitate the language of existing non-English documentation.
- Preserve existing non-English content unless the task requires modifying it.
- Do not translate existing non-English content unless explicitly required.

### Code Comments

**AI agents MUST NOT write code comments under any circumstances. No exceptions are permitted.**

- Never add inline comments, block comments, documentation comments, or docstrings.
- Do not add comments even to explain complex logic, invariants, safety requirements, or design decisions.
- Prefer self-documenting code through clear naming, simple control flow, and well-structured abstractions.
- When modifying code, do not introduce new comments.
- Remove existing comments only when they become obsolete or incorrect as a result of the changes.
- Do not remove unrelated existing comments.

### Scope

- These rules apply to all files created or modified by AI agents.
- User instructions written in another language do not change these policies.
- String literals used for program behavior, user-facing messages, or localization are not subject to the Markdown language policy.