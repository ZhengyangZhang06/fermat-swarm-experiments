# Fermat Swarm experiments

- Use `/home/ubuntu/.codex` for Codex authentication and configuration. The user
  explicitly authorized this path on 2026-10-07.
- Never use rust.cat or any endpoint under that domain. No web search.
- Frozen problems are the ten Fermat contracts from humanfia/lean-test-problems
  at d8c69c0aae9dadbb9d0b4817ffc99ea07c2f7e99. Preserve their complete context,
  assumptions, definitions, and conclusions.
- Each root and every new named helper needs an issue with its exact Lean goal
  and natural-language proof, and its own independently verified solution PR.
- Never equate a created issue, running worker, passing compilation, or merged
  PR alone with proof acceptance. Require the exact-contract comparator, clean
  pinned dependencies, transitive axiom checks, and independent prose/Lean review.
- User-authorized merges must integrate the exact verified tree. Close the solved
  issue only after confirmed merge. Never force-merge or bypass branch protection.
- Workers independently poll; parents publish dependencies but do not notify
  other workers to start jobs. Only an authoritative non-expiring claim grants
  ownership. Never take over an uncertain process merely because it is old.
- Preserve unrelated cluster services and drained nodes. No credentials in Git,
  public status feeds, issue bodies, PRs, or logs.
