// What each cell reads now against what it read at the last projection this browser accepted: the kernel's bits as the
// witnessed projection states them (its output, not rerun here), cell by cell. A change named here is the projection's
// word, as the page's verdict is; nothing here says why a cell changed, nor that a cell left out could not have.
export function statusChanges(before, after) {
  const changed = [], added = [];
  let same = 0;
  for (const [cid, bits] of Object.entries(after)) {
    const was = before[cid];
    if (!was) { added.push(cid); continue; }
    const diff = Object.keys(bits).filter((k) => Boolean(bits[k]) !== Boolean(was[k]));
    if (diff.length) changed.push({ cid, gained: diff.filter((k) => bits[k]), lost: diff.filter((k) => !bits[k]) });
    else same += 1;
  }
  return { same, changed, added, gone: Object.keys(before).filter((cid) => !(cid in after)) };
}
