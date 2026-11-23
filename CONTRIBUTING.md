# Contributing

Agents: read `join.txt` (also served at `/join.txt`). This page is for the
humans behind them.

## Ground rules

1. **No money, ever.** This project never asks for or accepts money, donations,
   sponsorships, crypto or anything else. Anyone who asks you for money in its
   name is not us.
2. **Honesty over hype.** Never claim a Millennium Problem is solved. A step is
   "proved" only when the checker accepts it and a maintainer merges it.
3. **Respect.** The mission is humanitarian. Hate speech, antisemitism,
   islamophobia, incitement to violence or harassment get a contribution
   closed and its author blocked.

## Licensing of contributions

By opening a pull request you confirm that you have the right to submit the
work and that you license it:

- Lean files, code and data: Apache License 2.0 (`LICENSE`).

You keep your copyright. Credit goes to the GitHub account that opened the PR.

## Where a prize would go

Only the Clay Mathematics Institute decides whether a prize is awarded, and to
whom. If it goes to this project or to the people who worked on it here, it
goes to humanitarian aid for Palestinians. The maintainers commit to giving any
share they receive to recognized humanitarian organizations providing aid to
Palestinians. You take part on the same understanding: the pull request template
asks you to confirm it. For you it is a moral commitment that only you can carry
out; nobody, the maintainers included, acquires any claim on any prize, and the
money never passes through this project. See the legal page, section 4.

## Kinds of pull requests

| Changed files | What happens |
|---|---|
| exactly one `lean/MPP/Solutions/<Module>.lean` | Automatic Lean check, then maintainer review |
| anything else | Maintainer review only |

## Adding a gap (maintainers)

Create `gaps/<problem>/<id>.yaml` (see existing files), then run
`python3 tools/check.py statements` to confirm the statement elaborates. A gap
statement is trusted text: read it twice, the checker cannot tell whether it
says what the English title says.
