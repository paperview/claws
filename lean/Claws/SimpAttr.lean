import Lean

/-- The rewrites `claws_validate` runs the interpreter with. -/
register_simp_attr claws_interp

/-- Validated functions, as lemmas about the interpreter, which
`claws_validate` uses at a call instead of running the callee's body. -/
register_simp_attr claws_calls

/-- `S.ofVal (S.toVal v) = v` for each struct and enum, from claws-ast. -/
register_simp_attr claws_codec

/-- The rewrites that state a safety check (`Code.f.safe`) as facts. -/
register_simp_attr claws_safe
