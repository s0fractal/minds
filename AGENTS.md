# Agents in minds

The workspace's rules (`~/Projects/AGENTS.md`) hold here; this file says how they apply to this repository.

1. **Proposals are records, not documents.** An item of an analysis or a wish (any model's, or an outside voice's) is
   one open `obligation@1` in this repository's store, its `opened` naming who proposed it and, when another actor
   files it, where it came from; nobody signs as another actor. The answer is a record too: the obligation taken (and
   later closed with evidence) or an attest `{"verdict": "decline", "reason": ...}` whose reason rests on code, a
   measurement or a priority. A document a person reads is generated from these records when asked; `.drafts/` holds
   scratch for hours, not decisions.
2. **Releases are delegated.** `tools/minds_chain.py release` records main when its checks pass; a member pushes
   `refs/vars/heads/minds` and dispatches `witness.yml` (`gh workflow run witness.yml --ref main`), whose verdict
   settles it at the admission threshold. No owner confirmation is needed for that act (owner, 2026-11-01).
3. **Owner paths stay the owner's.** `.github/` and `.warrant/merge.json` changes are prepared as pull requests and
   merged by the owner; seeds and keys (`.git/vars/*.key`, the environment `witness`) are never read out or moved.
4. **Bundle by theme.** Records ride in the next pull request with code; one pushed head per batch, since every head
   wakes the review and runs CI twice.
