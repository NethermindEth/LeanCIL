# Agent skills

[`leancil`](leancil/SKILL.md) is an Agent Skill for a coding agent that verifies .NET code with
LeanCIL in a project of its own. It does not cover work on LeanCIL itself.

Install it by copying the `leancil` folder into the agent's skills directory. Claude Code reads
`.claude/skills/leancil` in a project and `~/.claude/skills/leancil` for every project. The
skill links its own files relatively and everything else by absolute URL to this repository, so
it works outside a LeanCIL checkout.

| File | Read when |
| --- | --- |
| [SKILL.md](leancil/SKILL.md) | Always; it holds the paths, the shared commands, the limits and the result audit |
| [check-existing-proof.md](leancil/references/check-existing-proof.md) | A LeanCIL proof exists and needs running |
| [bridge-model-proof.md](leancil/references/bridge-model-proof.md) | Lean theorems about a model exist |
| [write-new-proof.md](leancil/references/write-new-proof.md) | Only code and a requirement exist |
| [verify-library.md](leancil/references/verify-library.md) | Many methods, profiles or variants are verified in one run |
| [failures.md](leancil/references/failures.md) | A command or proof step failed |
