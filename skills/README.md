# Agent skills

[`leancil`](leancil/SKILL.md) teaches a coding agent to check compiled .NET code against Lean
proofs with LeanCIL: running an existing proof, connecting theorems about a Lean model to the
compiled method, and writing a new proof. It is for people verifying their own libraries, not for
work on LeanCIL itself.

Install it by copying the `leancil` folder into the agent's skills directory, for example
`.claude/skills/leancil` in a project or `~/.claude/skills/leancil` for every project in Claude
Code. Agents that read the Agent Skills format load the same folder from their own skills
directory.
