Inductive SObj : Set :=
  ST
with SMor : Set :=
  Sid : SObj -> SMor
with SPrf : Set :=
    SREFL  : SMor -> SPrf
  | SSYMM  : SPrf -> SPrf
  | STRANS : SPrf -> SPrf -> SPrf.

Fixpoint source (f : SMor) : SObj :=
  match f with
  | Sid x => x
  end.

Fixpoint target (f : SMor) : SObj :=
  match f with
  | Sid x => x
  end.

Fixpoint lhs (p : SPrf) : SMor :=
  match p with
  | SREFL f    => f
  | SSYMM p    => rhs p
  | STRANS p _ => lhs p
  end
with rhs (p : SPrf) : SMor :=
  match p with
  | SREFL f    => f
  | SSYMM p    => lhs p
  | STRANS _ p => rhs p
  end.

Inductive sobj_valid  : SObj -> Prop :=
| T_valid : sobj_valid ST
with smor_valid : SMor -> Prop :=
| id_valid : forall x, sobj_valid x -> smor_valid (Sid x)
with sprf_valid : SPrf -> Prop :=
| REFL_valid   : forall f, smor_valid f -> sprf_valid (SREFL f)
| SYMM_valid   : forall p, sprf_valid p -> sprf_valid (SSYMM p)
| TRANS_valid : forall p q, sprf_valid p -> sprf_valid q -> rhs p = lhs q -> sprf_valid (STRANS p q).

Hint Constructors sobj_valid smor_valid sprf_valid.

Definition Object : Set := {x : SObj | sobj_valid x}.

Definition obj_in_sobj (x : Object) : SObj := proj1_sig x.

Coercion obj_in_sobj : Object >-> SObj.

Lemma obj_valid (x : Object) : sobj_valid x.
  exact (proj2_sig x).
Qed.

Hint Extern 0 => apply obj_valid.

Definition Morphism (x y : Object) : Set := 
  {f : SMor | smor_valid f /\ source f = x /\ target f = y}.

Definition mor_in_smor {x y : Object} (f : Morphism x y) : SMor := proj1_sig f.

Coercion mor_in_smor : Morphism >-> SMor.

Lemma mor_valid {x y : Object} (f : Morphism x y) : smor_valid f /\ source f = x /\ target f = y.
  exact (proj2_sig f).
Qed.

Hint Extern 0 => apply mor_valid.

Lemma mor_source {x y : Object} (f : Morphism x y) : source f = x.
  auto.
Qed.

Lemma mor_target {x y : Object} (f : Morphism x y) : target f = x.
  auto.
Qed.

Definition Proof {x y : Object} (f g : Morphism x y) : Set :=
  {p : SPrf | sprf_valid p /\ lhs p = f /\ rhs p = g}.

Definition proof_in_sprf {x y : Object} {f g : Morphism x y} (p : Proof f g) : SPrf := proj1_sig p.

Coercion proof_in_sprf : Proof >-> SPrf.

Lemma proof_valid {x y : Object} {f g : Morphism x y} (p : Proof f g) : sprf_valid p /\ lhs p = f /\ rhs p = g.
  exact (proj2_sig p).
Qed.

Hint Extern 0 => apply proof_valid.

Lemma proof_lhs {x y : Object} {f g : Morphism x y} (p : Proof f g) : lhs p = f.
  auto.
Qed.

Lemma proof_rhs {x y : Object} {f g : Morphism x y} (p : Proof f g) : rhs p = g.
  auto.
Qed.

Definition REFL {x y : Object} (f : Morphism x y) : Proof f f.
  exists (SREFL f).
  auto.
Defined.

Definition SYMM {x y : Object} {f g : Morphism x y} (p : Proof f g) : Proof g f.
  exists (SSYMM p).
  auto.
Defined.

Definition TRANS {x y : Object} {f g h : Morphism x y} (p : Proof f g) (q : Proof g h) : Proof f h.
  exists (STRANS p q).
  auto.
  split.
  apply TRANS_valid; auto.
  rewrite (proof_rhs p).
  rewrite (proof_lhs q).
  reflexivity.
  auto.
Defined.

Definition id (x : Object) : Morphism x x.
  exists (Sid x).
  auto.
Defined.

Definition T : Object.
  exists ST.
  auto.
Defined.

