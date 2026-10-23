import Claws.Sem

/-!
# The semantics is deterministic

A program in the subset has at most one meaning: if `Exec` derives two
outcomes for the same statement, names and objects, they are the same. So a
validation law, which derives one run, says what the C++ does, not just
something it might do.
-/

namespace Claws.Sem

-- Compiling the matches of seven mutual relations takes a while.
set_option maxHeartbeats 4000000

mutual

theorem Eval.det {P : Prog} {e : Env} {m : Mem} {a : Expr} {r₁ r₂ : Res}
    (h₁ : Eval P e m a r₁) (h₂ : Eval P e m a r₂) : r₁ = r₂ :=
  match h₁, h₂ with
  | .lit h₁, .lit h₂ => by rw [h₁] at h₂; cases h₂; rfl
  | .boolLit, .boolLit => rfl
  | .enumLit, .enumLit => rfl
  | .var h₁, .var h₂ => by rw [h₁] at h₂; cases h₂; rfl
  | .memberLoc a, .memberLoc b => by cases Eval.det a b; rfl
  | .memberLoc a, .memberVal b _ => by cases Eval.det a b
  | .memberVal a _, .memberLoc b => by cases Eval.det a b
  | .memberVal a h₁, .memberVal b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .memberGlob a, .memberGlob b => by cases Eval.det a b; rfl
  | .memberGlob a, .memberLoc b => by cases Eval.det a b
  | .memberLoc a, .memberGlob b => by cases Eval.det a b
  | .memberGlob a, .memberVal b _ => by cases Eval.det a b
  | .memberVal a _, .memberGlob b => by cases Eval.det a b
  | .global _, .global _ => rfl
  | .subscript a c k₁ g₁ _, .subscript b d k₂ g₂ _ => by
      cases Eval.det a b; cases Eval.det c d; rw [k₁] at k₂; cases k₂; rfl
  | .loadGlob a h₁, .loadGlob b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .load a _, .loadGlob b _ => by cases Eval.det a b
  | .loadGlob a _, .load b _ => by cases Eval.det a b
  | .copyGlob a h₁, .copyGlob b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .copyGlob a _, .copy b _ => by cases Eval.det a b
  | .copy a _, .copyGlob b _ => by cases Eval.det a b
  | .copyGlob a _, .copyVal b => by cases Eval.det a b
  | .copyVal a, .copyGlob b _ => by cases Eval.det a b
  | .load a h₁, .load b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .integral a h₁, .integral b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .toBool a h₁, .toBool b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .noOp a, .noOp b => Eval.det a b
  | .unary a h₁, .unary b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .binary a c h₁, .binary b d h₂ => by
      cases Eval.det a b; cases Eval.det c d; rw [h₁] at h₂; cases h₂; rfl
  | .landF _, .landF _ => rfl
  | .landF a, .landT b _ => by cases Eval.det a b
  | .landT a _, .landF b => by cases Eval.det a b
  | .landT _ c, .landT _ d => by cases Eval.det c d; rfl
  | .lorT _, .lorT _ => rfl
  | .lorT a, .lorF b _ => by cases Eval.det a b
  | .lorF a _, .lorT b => by cases Eval.det a b
  | .lorF _ c, .lorF _ d => by cases Eval.det c d; rfl
  | .condT _ c, .condT _ d => Eval.det c d
  | .condT a _, .condF b _ => by cases Eval.det a b
  | .condF a _, .condT b _ => by cases Eval.det a b
  | .condF _ c, .condF _ d => Eval.det c d
  | .call a c, .call b d => by
      cases EvalArgs.det a b; cases (Call.det c d).1; rfl
  | .copy a h₁, .copy b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .copy a _, .copyVal b => by cases Eval.det a b
  | .copyVal a, .copy b _ => by cases Eval.det a b
  | .copyVal a, .copyVal b => by cases Eval.det a b; rfl
  | .initList a h₁, .initList b h₂ => by cases EvalList.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .paren a, .paren b => Eval.det a b
  | .size a h₁, .size b h₂ => by cases Eval.det a b; rw [h₁] at h₂; cases h₂; rfl
  | .index a c h₁ _, .index b d h₂ _ => by
      cases Eval.det a b; cases Eval.det c d; rfl
  | .vecEmpty, .vecEmpty => rfl
  | .vecFill a c h₁, .vecFill b d h₂ => by
      cases Eval.det a b; cases Eval.det c d; rw [h₁] at h₂; cases h₂; rfl
  | .listNil, .listNil => rfl
  | .cons a h₁ c k₁, .cons b h₂ d k₂ => by
      cases Eval.det a b; rw [h₁] at h₂; cases h₂; cases Eval.det c d; rw [k₁] at k₂; cases k₂; rfl
  | .matchNil a _ f₁ b₁ x₁ r₁, .matchNil b _ f₂ b₂ x₂ r₂ => by
      cases Eval.det a b; rw [f₁] at f₂; cases f₂; rw [b₁] at b₂; cases b₂
      cases Exec.det x₁ x₂; rw [r₁] at r₂; cases r₂; rfl
  | .matchNil a h₁ _ _ _ _, .matchCons b h₂ _ _ _ _ => by
      cases Eval.det a b; rw [h₁] at h₂; cases h₂
  | .matchCons a h₁ _ _ _ _, .matchNil b h₂ _ _ _ _ => by
      cases Eval.det a b; rw [h₁] at h₂; cases h₂
  | .matchCons a h₁ f₁ b₁ x₁ r₁, .matchCons b h₂ f₂ b₂ x₂ r₂ => by
      cases Eval.det a b; rw [h₁] at h₂; cases h₂; rw [f₁] at f₂; cases f₂; rw [b₁] at b₂; cases b₂
      cases Exec.det x₁ x₂; rw [r₁] at r₂; cases r₂; rfl
termination_by structural h₁

theorem EvalList.det {P : Prog} {e : Env} {m : Mem} {as : List Expr} {vs₁ vs₂ : List Val}
    (h₁ : EvalList P e m as vs₁) (h₂ : EvalList P e m as vs₂) : vs₁ = vs₂ :=
  match h₁, h₂ with
  | .nil, .nil => rfl
  | .cons a c, .cons b d => by cases Eval.det a b; cases EvalList.det c d; rfl
termination_by structural h₁

theorem EvalArgs.det {P : Prog} {e : Env} {m : Mem} {as : List Expr} {rs₁ rs₂ : List Res}
    (h₁ : EvalArgs P e m as rs₁) (h₂ : EvalArgs P e m as rs₂) : rs₁ = rs₂ :=
  match h₁, h₂ with
  | .nil, .nil => rfl
  | .cons a c, .cons b d => by cases Eval.det a b; cases EvalArgs.det c d; rfl
termination_by structural h₁

theorem EvalTop.det {P : Prog} {e : Env} {m : Mem} {a : Expr} {r₁ r₂ : Res} {m₁ m₂ : Mem}
    (h₁ : EvalTop P e m a r₁ m₁) (h₂ : EvalTop P e m a r₂ m₂) : r₁ = r₂ ∧ m₁ = m₂ :=
  match h₁, h₂ with
  | .pure a, .pure b => by cases Eval.det a b; exact ⟨rfl, rfl⟩
  | .pure (.call a c), .call b d => by
      cases EvalArgs.det a b; obtain ⟨h, h'⟩ := Call.det c d; cases h; exact ⟨rfl, h'⟩
  | .call a c, .pure (.call b d) => by
      cases EvalArgs.det a b; obtain ⟨h, h'⟩ := Call.det c d; cases h; exact ⟨rfl, h'⟩
  | .call a c, .call b d => by
      cases EvalArgs.det a b; obtain ⟨h, h'⟩ := Call.det c d; cases h; exact ⟨rfl, h'⟩
termination_by structural h₁

theorem Call.det {P : Prog} {m : Mem} {f : String} {rs : List Res} {res₁ res₂ : Option Val}
    {m₁ m₂ : Mem} (h₁ : Call P m f rs res₁ m₁) (h₂ : Call P m f rs res₂ m₂) :
    res₁ = res₂ ∧ m₁ = m₂ :=
  match h₁, h₂ with
  | .mk hf₁ hb₁ x₁ f₁, .mk hf₂ hb₂ x₂ f₂ => by
      rw [hf₁] at hf₂; cases hf₂; rw [hb₁] at hb₂; cases hb₂
      cases Exec.det x₁ x₂; rw [f₁] at f₂; cases f₂; exact ⟨rfl, rfl⟩
termination_by structural h₁

theorem Exec.det {P : Prog} {e : Env} {m : Mem} {st : Stmt} {o₁ o₂ : Outcome}
    (h₁ : Exec P e m st o₁) (h₂ : Exec P e m st o₂) : o₁ = o₂ :=
  match h₁, h₂ with
  | .decl a, .decl b => by obtain ⟨h, h'⟩ := EvalTop.det a b; cases h; cases h'; rfl
  | .expr _, .expr _ => rfl
  | .expr (.call a c), .exprCall b d => by
      cases EvalArgs.det a b; obtain ⟨_, h'⟩ := Call.det c d; cases h'; rfl
  | .exprCall a c, .expr (.call b d) => by
      cases EvalArgs.det a b; obtain ⟨_, h'⟩ := Call.det c d; cases h'; rfl
  | .exprCall a c, .exprCall b d => by
      cases EvalArgs.det a b; obtain ⟨_, h'⟩ := Call.det c d; cases h'; rfl
  | .expr h, .assign .. => nomatch h
  | .assign .., .expr h => nomatch h
  | .expr h, .compound .. => nomatch h
  | .compound .., .expr h => nomatch h
  | .expr h, .incdec .. => nomatch h
  | .incdec .., .expr h => nomatch h
  | .expr h, .expects _ => nomatch h
  | .expects _, .expr h => nomatch h
  | .assign a c w₁, .assign b d w₂ => by
      obtain ⟨h, h'⟩ := EvalTop.det a b; cases h; cases h'
      cases Eval.det c d; rw [w₁] at w₂; cases w₂; rfl
  | .compound a c r₁ v₁ o₁ t₁ w₁, .compound b d r₂ v₂ o₂ t₂ w₂ => by
      cases Eval.det a b; cases Eval.det c d
      rw [r₁] at r₂; cases r₂; rw [v₁] at v₂; cases v₂; rw [o₁] at o₂; cases o₂
      rw [t₁] at t₂; cases t₂; rw [w₁] at w₂; cases w₂; rfl
  | .incdec a r₁ o₁ t₁ w₁, .incdec b r₂ o₂ t₂ w₂ => by
      cases Eval.det a b; rw [r₁] at r₂; cases r₂; rw [o₁] at o₂; cases o₂
      rw [t₁] at t₂; cases t₂; rw [w₁] at w₂; cases w₂; rfl
  | .expects _, .expects _ => rfl
  | .expr h, .decreases _ => nomatch h
  | .decreases _, .expr h => nomatch h
  | .decreases _, .decreases _ => rfl
  | .push a c v₁ r₁ _ w₁, .push b d v₂ r₂ _ w₂ => by
      cases Eval.det a b; cases Eval.det c d; rw [v₁] at v₂; cases v₂
      rw [r₁] at r₂; cases r₂; rw [w₁] at w₂; cases w₂; rfl
  | .ret a, .ret b => by obtain ⟨h, h'⟩ := EvalTop.det a b; cases h; cases h'; rfl
  | .retVoid, .retVoid => rfl
  | .iteT _ c, .iteT _ d => Exec.det c d
  | .iteT a _, .iteF b _ => by cases Eval.det a b
  | .iteF a _, .iteT b _ => by cases Eval.det a b
  | .iteF _ c, .iteF _ d => Exec.det c d
  | .blockNormal a, .blockNormal b => by cases ExecList.det a b; rfl
  | .blockNormal a, .blockBrk b => by cases ExecList.det a b
  | .blockNormal a, .blockCont b => by cases ExecList.det a b
  | .blockNormal a, .blockRet b => by cases ExecList.det a b
  | .blockBrk a, .blockNormal b => by cases ExecList.det a b
  | .blockBrk a, .blockBrk b => by cases ExecList.det a b; rfl
  | .blockBrk a, .blockCont b => by cases ExecList.det a b
  | .blockBrk a, .blockRet b => by cases ExecList.det a b
  | .blockCont a, .blockNormal b => by cases ExecList.det a b
  | .blockCont a, .blockBrk b => by cases ExecList.det a b
  | .blockCont a, .blockCont b => by cases ExecList.det a b; rfl
  | .blockCont a, .blockRet b => by cases ExecList.det a b
  | .blockRet a, .blockNormal b => by cases ExecList.det a b
  | .blockRet a, .blockBrk b => by cases ExecList.det a b
  | .blockRet a, .blockCont b => by cases ExecList.det a b
  | .blockRet a, .blockRet b => by cases ExecList.det a b; rfl
  | .switchNormal a p₁ x₁, .switchNormal b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂; rfl
  | .switchNormal a p₁ x₁, .switchBrk b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchNormal a p₁ x₁, .switchCont b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchNormal a p₁ x₁, .switchRet b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchNormal a p₁ _, .switchNone b p₂ => by cases Eval.det a b; rw [p₁] at p₂; cases p₂
  | .switchNone a p₁, .switchNormal b p₂ _ => by cases Eval.det a b; rw [p₁] at p₂; cases p₂
  | .switchBrk a p₁ x₁, .switchNormal b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchBrk a p₁ x₁, .switchBrk b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂; rfl
  | .switchBrk a p₁ x₁, .switchCont b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchBrk a p₁ x₁, .switchRet b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchBrk a p₁ _, .switchNone b p₂ => by cases Eval.det a b; rw [p₁] at p₂; cases p₂
  | .switchNone a p₁, .switchBrk b p₂ _ => by cases Eval.det a b; rw [p₁] at p₂; cases p₂
  | .switchCont a p₁ x₁, .switchNormal b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchCont a p₁ x₁, .switchBrk b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchCont a p₁ x₁, .switchCont b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂; rfl
  | .switchCont a p₁ x₁, .switchRet b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchCont a p₁ _, .switchNone b p₂ => by cases Eval.det a b; rw [p₁] at p₂; cases p₂
  | .switchNone a p₁, .switchCont b p₂ _ => by cases Eval.det a b; rw [p₁] at p₂; cases p₂
  | .switchRet a p₁ x₁, .switchNormal b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchRet a p₁ x₁, .switchBrk b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchRet a p₁ x₁, .switchCont b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂
  | .switchRet a p₁ x₁, .switchRet b p₂ x₂ => by
      cases Eval.det a b; rw [p₁] at p₂; cases p₂; cases ExecList.det x₁ x₂; rfl
  | .switchRet a p₁ _, .switchNone b p₂ => by cases Eval.det a b; rw [p₁] at p₂; cases p₂
  | .switchNone a p₁, .switchRet b p₂ _ => by cases Eval.det a b; rw [p₁] at p₂; cases p₂
  | .switchNone _ _, .switchNone _ _ => rfl
  | .caseLabel, .caseLabel => rfl
  | .defaultLabel, .defaultLabel => rfl
  | .brk, .brk => rfl
  | .cont, .cont => rfl
  | .loopF _, .loopF _ => rfl
  | .loopF a, .loopNext b _ _ _ => by cases Eval.det a b
  | .loopF a, .loopCont b _ _ _ => by cases Eval.det a b
  | .loopF a, .loopBrk b _ => by cases Eval.det a b
  | .loopF a, .loopRet b _ => by cases Eval.det a b
  | .loopNext a _ _ _, .loopF b => by cases Eval.det a b
  | .loopCont a _ _ _, .loopF b => by cases Eval.det a b
  | .loopBrk a _, .loopF b => by cases Eval.det a b
  | .loopRet a _, .loopF b => by cases Eval.det a b
  | .loopNext _ x₁ y₁ z₁, .loopNext _ x₂ y₂ z₂ => by
      cases Exec.det x₁ x₂; cases Exec.det y₁ y₂; exact Exec.det z₁ z₂
  | .loopCont _ x₁ y₁ z₁, .loopCont _ x₂ y₂ z₂ => by
      cases Exec.det x₁ x₂; cases Exec.det y₁ y₂; exact Exec.det z₁ z₂
  | .loopNext _ x₁ _ _, .loopCont _ x₂ _ _ => by cases Exec.det x₁ x₂
  | .loopCont _ x₁ _ _, .loopNext _ x₂ _ _ => by cases Exec.det x₁ x₂
  | .loopNext _ x₁ _ _, .loopBrk _ x₂ => by cases Exec.det x₁ x₂
  | .loopBrk _ x₁, .loopNext _ x₂ _ _ => by cases Exec.det x₁ x₂
  | .loopNext _ x₁ _ _, .loopRet _ x₂ => by cases Exec.det x₁ x₂
  | .loopRet _ x₁, .loopNext _ x₂ _ _ => by cases Exec.det x₁ x₂
  | .loopCont _ x₁ _ _, .loopBrk _ x₂ => by cases Exec.det x₁ x₂
  | .loopBrk _ x₁, .loopCont _ x₂ _ _ => by cases Exec.det x₁ x₂
  | .loopCont _ x₁ _ _, .loopRet _ x₂ => by cases Exec.det x₁ x₂
  | .loopRet _ x₁, .loopCont _ x₂ _ _ => by cases Exec.det x₁ x₂
  | .loopBrk _ x₁, .loopBrk _ x₂ => by cases Exec.det x₁ x₂; rfl
  | .loopBrk _ x₁, .loopRet _ x₂ => by cases Exec.det x₁ x₂
  | .loopRet _ x₁, .loopBrk _ x₂ => by cases Exec.det x₁ x₂
  | .loopRet _ x₁, .loopRet _ x₂ => by cases Exec.det x₁ x₂; rfl
termination_by structural h₁

theorem ExecList.det {P : Prog} {e : Env} {m : Mem} {ss : List Stmt} {o₁ o₂ : Outcome}
    (h₁ : ExecList P e m ss o₁) (h₂ : ExecList P e m ss o₂) : o₁ = o₂ :=
  match h₁, h₂ with
  | .nil, .nil => rfl
  | .next a c, .next b d => by cases Exec.det a b; exact ExecList.det c d
  | .next a _, .brk b => by cases Exec.det a b
  | .brk a, .next b _ => by cases Exec.det a b
  | .brk a, .brk b => by cases Exec.det a b; rfl
  | .brk a, .cont b => by cases Exec.det a b
  | .brk a, .ret b => by cases Exec.det a b
  | .next a _, .cont b => by cases Exec.det a b
  | .cont a, .next b _ => by cases Exec.det a b
  | .cont a, .brk b => by cases Exec.det a b
  | .cont a, .cont b => by cases Exec.det a b; rfl
  | .cont a, .ret b => by cases Exec.det a b
  | .next a _, .ret b => by cases Exec.det a b
  | .ret a, .next b _ => by cases Exec.det a b
  | .ret a, .brk b => by cases Exec.det a b
  | .ret a, .cont b => by cases Exec.det a b
  | .ret a, .ret b => by cases Exec.det a b; rfl
termination_by structural h₁

end

end Claws.Sem
