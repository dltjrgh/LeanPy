def State : Type := String -> Nat

inductive Stmt : Type where
  | skip : Stmt
  | assign : String -> (State -> Nat) -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | ifThenElse : (State -> Prop) -> Stmt -> Stmt -> Stmt
  | whileDo : (State -> Prop) -> Stmt -> Stmt

infixr:90 "; " => Stmt.seq

def State.update (name : String) (val : Nat) (s : State) : State :=
  fun name' ↦ if name' = name then val else s name'

macro s:term "[" name:term "↦" val:term "]" : term =>
  `(State.update $name $val $s)

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s => s "x" > s "y")
    (Stmt.skip;
     Stmt.assign "x" (fun s => s "x" - 1))

inductive BigStep : Stmt × State -> State -> Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep

@[simp] theorem update_apply (name : String) (val : Nat) (s : State) :
    (s[name ↦ val]) name = val :=
  by
    apply if_pos
    rfl

@[simp] theorem update_apply_neq (name name' : String) (val : Nat) (s : State)
      (hneq : name' ≠ name) :
    (s[name ↦ val]) name' = s name' :=
  by
    apply if_neg
    assumption

@[simp] theorem update_override (name : String) (val1 val2 : Nat) (s : State) :
    s[name ↦ val2][name ↦ val1] = s[name ↦ val1] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h => simp [h]
    | inr h => simp [h]

@[simp] theorem update_same_const (name : String) (val : Nat) :
    (fun _ => val)[name ↦ val] = (fun _ => val) :=
  by
    apply funext
    simp [State.update]

theorem sillyLoop_from_1_BigStep :
    (sillyLoop, (fun _ => 0)["x" ↦ 1]) ⟹  (fun _ => 0) :=
  by
    rw[sillyLoop]
    apply BigStep.while_true
    { simp }
    { apply BigStep.seq
      { apply BigStep.skip }
      { apply BigStep.assign } }
    { simp
      apply BigStep.while_false 
      simp }


