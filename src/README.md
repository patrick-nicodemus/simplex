- Do not use Prop. Prefer Type and SProp.
- Prefer canonical structures for building algebraic hierarchies, but typeclasses are permitted.

Design space:
- Consistency with univalence? (Cannot use Prop, or it will generate nonsensical OCaml code during extraction.)
- Assume Univalence?
- Assume Funext?
- Draw on the usual standard library or stdpp?