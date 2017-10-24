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

Definition Object : Set := {x : SObj | sobj_valid x}.

Definition Morphism (x y : Object) : Set := 
  {f : SMor | smor_valid f /\ proj1_sig x = source f /\ proj1_sig y = target f}.

Lemma mor_source {x y : Object} (f : Morphism x y) : source (proj1_sig f) = proj1_sig x.
  symmetry.
  apply (proj2_sig f).
Qed.

Lemma mor_target {x y : Object} (f : Morphism x y) : target (proj1_sig f) = proj1_sig y.
  symmetry.
  apply (proj2_sig f).
Qed.

Definition Proof {x y : Object} (f g : Morphism x y) : Set :=
  {p : SPrf | sprf_valid p /\ proj1_sig f = lhs p /\ proj1_sig g = rhs p}.

Lemma proof_lhs {x y : Object} {f g : Morphism x y} (p : Proof f g) : lhs (proj1_sig p) = proj1_sig f.
  symmetry.
  apply (proj2_sig p).
Qed.

Lemma proof_rhs {x y : Object} {f g : Morphism x y} (p : Proof f g) : rhs (proj1_sig p) = proj1_sig g.
  symmetry.
  apply (proj2_sig p).
Qed.

Definition REFL {x y : Object} (f : Morphism x y) : Proof f f.
  exists (SREFL (proj1_sig f)).
  split.
  apply REFL_valid.
  apply (proj2_sig f).
  auto.
Defined.

Definition SYMM {x y : Object} {f g : Morphism x y} (p : Proof f g) : Proof g f.
  exists (SSYMM (proj1_sig p)).
  split.
  apply SYMM_valid.
  apply (proj2_sig p).
  split; apply (proj2_sig p).
Defined.

Definition TRANS {x y : Object} {f g h : Morphism x y} (p : Proof f g) (q : Proof g h) : Proof f h.
  exists (STRANS (proj1_sig p) (proj1_sig q)).
  split.
  apply TRANS_valid.
  apply (proj2_sig p).
  apply (proj2_sig q).
  rewrite proof_rhs.
  rewrite proof_lhs.
  reflexivity.
  split.
  simpl.
  symmetry.
  apply proof_lhs.
  symmetry.
  apply proof_rhs.
Defined.

Definition id (x : Object) : Morphism x x.
  exists (Sid (proj1_sig x)).
  split.
  apply id_valid.
  apply (proj2_sig x).
  split; simpl; reflexivity.
Defined.

Definition T : Object.
  exists ST.
  exact T_valid.
Defined.

