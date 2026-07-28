(*
  Checked with Rocq 9.0.0.

  This file contains the Rocq definitions corresponding to
  NestedPain.lean.
*)

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.

Inductive Term : Type :=
  | var : string -> Term
  | lam : string -> Term -> Term
  | app : Term -> list Term -> Term.

Inductive Ty : Type :=
  | tbase : string -> Ty
  | arrow : list Ty -> Ty -> Ty.

Definition Ctx := list (string * Ty).

(* The generated Term induction principle has no hypotheses for list elements. *)

Fixpoint Term_rect_strong (P : Term -> Type) (Pl : list Term -> Type)
  (Hvar : forall name, P (var name))
  (Hlam : forall name body, P body -> P (lam name body))
  (Happ : forall fn args, P fn -> Pl args -> P (app fn args))
  (Hnil : Pl nil)
  (Hcons : forall term terms, P term -> Pl terms -> Pl (term :: terms))
  (term : Term) : P term :=
  match term with
  | var name => Hvar name
  | lam name body =>
      Hlam name body
        (Term_rect_strong P Pl Hvar Hlam Happ Hnil Hcons body)
  | app fn args =>
      Happ fn args
        (Term_rect_strong P Pl Hvar Hlam Happ Hnil Hcons fn)
        ((fix terms_rect (terms : list Term) : Pl terms :=
            match terms with
            | nil => Hnil
            | term :: terms =>
                Hcons term terms
                  (Term_rect_strong
                    P Pl Hvar Hlam Happ Hnil Hcons term)
                  (terms_rect terms)
            end) args)
  end.

(* Rocq and Lean both accept these direct Forall2 occurrences. *)

Inductive ParRed : Term -> Term -> Prop :=
  | par_var : forall name, ParRed (var name) (var name)
  | par_lam : forall name body body',
      ParRed body body' ->
      ParRed (lam name body) (lam name body')
  | par_app : forall fn fn' args args',
      ParRed fn fn' ->
      Forall2 ParRed args args' ->
      ParRed (app fn args) (app fn' args').

Lemma ParRed_refl : forall term, ParRed term term.
Proof.
  apply (Term_rect_strong _ (fun terms => Forall2 ParRed terms terms));
    intros; constructor; assumption.
Qed.

Lemma ParRed_app_inv : forall fn args result,
  ParRed (app fn args) result ->
  exists fn' args', result = app fn' args' /\
    ParRed fn fn' /\ Forall2 ParRed args args'.
Proof.
  intros fn args result H. inversion H; subst.
  eauto.
Qed.

Inductive Subty : Ty -> Ty -> Prop :=
  | sub_refl : forall ty, Subty ty ty
  | sub_arrow : forall argsA argsB retA retB,
      Forall2 Subty argsB argsA ->
      Subty retA retB ->
      Subty (arrow argsA retA) (arrow argsB retB).

Lemma Forall2_Subty_trans : forall xs ys zs,
  Forall2 Subty xs ys ->
  Forall2 Subty ys zs ->
  (forall a b c, Subty a b -> Subty b c -> Subty a c) ->
  Forall2 Subty xs zs.
Proof.
  intros xs ys zs Hxy Hyz Htrans.
  generalize dependent zs.
  induction Hxy as [| x y xs ys Hsub Hrest IH]; intros.
  - inversion Hyz. constructor.
  - inversion Hyz; subst. constructor.
    + eapply Htrans; eauto.
    + eapply IH; eauto.
Qed.

(* Rocq accepts the constructor-local environment captured by Forall2. *)

Inductive Val : Type :=
  | vnum : nat -> Val
  | vclosure : string -> Term -> list (string * Val) -> Val.

Definition Env := list (string * Val).

Inductive Eval : Env -> Term -> Val -> Prop :=
  | eval_var : forall env name value,
      In (name, value) env ->
      Eval env (var name) value
  | eval_lam : forall env name body,
      Eval env (lam name body) (vclosure name body env)
  | eval_app : forall env fn param body cenv args values result,
      Eval env fn (vclosure param body cenv) ->
      Forall2 (Eval env) args values ->
      Eval cenv body result ->
      Eval env (app fn args) result.

Lemma Forall2_Eval_det : forall env args values1 values2,
  Forall2 (Eval env) args values1 ->
  Forall2 (Eval env) args values2 ->
  (forall term value1 value2,
    Eval env term value1 -> Eval env term value2 -> value1 = value2) ->
  values1 = values2.
Proof.
  intros env args values1 values2 H1 H2 Hdet.
  generalize dependent values2.
  induction H1 as [| term value terms values Heval Hrest IH]; intros.
  - inversion H2. reflexivity.
  - inversion H2; subst. f_equal.
    + eapply Hdet; eauto.
    + eapply IH; eauto.
Qed.

(* Rocq accepts And inside the relation passed to Forall2. *)

Inductive JSON : Type :=
  | jnull : JSON
  | jstr : string -> JSON
  | jnum : nat -> JSON
  | jarr : list JSON -> JSON
  | jobj : list (string * JSON) -> JSON.

Inductive Schema : Type :=
  | sany : Schema
  | sstr : Schema
  | snum : Schema
  | sarr : Schema -> Schema
  | sobj : list (string * Schema) -> Schema.

Inductive Valid : Schema -> JSON -> Prop :=
  | valid_any : forall json, Valid sany json
  | valid_str : forall value, Valid sstr (jstr value)
  | valid_num : forall value, Valid snum (jnum value)
  | valid_arr : forall elemSchema values,
      Forall (fun json => Valid elemSchema json) values ->
      Valid (sarr elemSchema) (jarr values)
  | valid_obj : forall schemaFields jsonFields,
      Forall2
        (fun (sf : string * Schema) (jf : string * JSON) =>
          fst sf = fst jf /\ Valid (snd sf) (snd jf))
        schemaFields jsonFields ->
      Valid (sobj schemaFields) (jobj jsonFields).

Lemma valid_field_lookup : forall schemaFields jsonFields sf jf,
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    schemaFields jsonFields ->
  In (sf, jf) (combine schemaFields jsonFields) ->
  fst sf = fst jf /\ Valid (snd sf) (snd jf).
Proof.
  intros schemaFields jsonFields sf jf Hfields Hin.
  induction Hfields as [| sf' jf' schemaFields' jsonFields' Hhead Htail IH].
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. assumption.
    + apply IH. assumption.
Qed.

Lemma valid_drop_head : forall sf jf schemaFields jsonFields,
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    (sf :: schemaFields) (jf :: jsonFields) ->
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    schemaFields jsonFields.
Proof.
  intros. inversion H. assumption.
Qed.

Lemma valid_head_field : forall sf jf schemaFields jsonFields,
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    (sf :: schemaFields) (jf :: jsonFields) ->
  fst sf = fst jf /\ Valid (snd sf) (snd jf).
Proof.
  intros. inversion H. assumption.
Qed.

Lemma valid_obj_field_count : forall schemaFields jsonFields,
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    schemaFields jsonFields ->
  List.length schemaFields = List.length jsonFields.
Proof.
  intros. now apply Forall2_length in H.
Qed.

Lemma valid_prefix : forall prefix extra jsonPrefix jsonSuffix,
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    (prefix ++ extra) (jsonPrefix ++ jsonSuffix) ->
  List.length prefix = List.length jsonPrefix ->
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    prefix jsonPrefix.
Proof.
  induction prefix as [| sf prefix IH]; intros.
  - destruct jsonPrefix; [constructor | discriminate].
  - destruct jsonPrefix as [| jf jsonPrefix]; [discriminate |].
    simpl in H. inversion H; subst.
    constructor; auto.
    apply IH with extra jsonSuffix; [assumption |].
    simpl in H0. injection H0. auto.
Qed.

Lemma valid_obj_names : forall schemaFields jsonFields,
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    schemaFields jsonFields ->
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf)
    schemaFields jsonFields.
Proof.
  intros. induction H; constructor; tauto.
Qed.

Lemma valid_obj_values : forall schemaFields jsonFields,
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      fst sf = fst jf /\ Valid (snd sf) (snd jf))
    schemaFields jsonFields ->
  Forall2
    (fun (sf : string * Schema) (jf : string * JSON) =>
      Valid (snd sf) (snd jf))
    schemaFields jsonFields.
Proof.
  intros. induction H; constructor; tauto.
Qed.

(* Scheme generates a combined principle for the mutual typing relations. *)

Fixpoint ctx_lookup (ctx : Ctx) (name : string) : option Ty :=
  match ctx with
  | nil => None
  | (key, ty) :: rest =>
      if String.eqb name key then Some ty else ctx_lookup rest name
  end.

Inductive Synth : Ctx -> Term -> Ty -> Prop :=
  | synth_var : forall ctx name ty,
      ctx_lookup ctx name = Some ty ->
      Synth ctx (var name) ty
  | synth_app : forall ctx fn args argTys retTy,
      Synth ctx fn (arrow argTys retTy) ->
      CheckList ctx args argTys ->
      Synth ctx (app fn args) retTy

with Check : Ctx -> Term -> Ty -> Prop :=
  | check_lam : forall ctx name body argTy retTy,
      Check ((name, argTy) :: ctx) body retTy ->
      Check ctx (lam name body) (arrow (argTy :: nil) retTy)
  | check_sub : forall ctx term ty,
      Synth ctx term ty ->
      Check ctx term ty

with CheckList : Ctx -> list Term -> list Ty -> Prop :=
  | checklist_nil : forall ctx,
      CheckList ctx nil nil
  | checklist_cons : forall ctx term ty terms tys,
      Check ctx term ty ->
      CheckList ctx terms tys ->
      CheckList ctx (term :: terms) (ty :: tys).

Scheme Synth_ind' := Induction for Synth Sort Prop
  with Check_ind' := Induction for Check Sort Prop
  with CheckList_ind' := Induction for CheckList Sort Prop.

Lemma Synth_ctx_nonempty : forall ctx term ty,
  Synth ctx term ty ->
  (exists name ty', In (name, ty') ctx) \/
  (exists fn args, term = app fn args).
Proof.
  intros ctx term ty H.
  induction H using Synth_ind'
    with (P0 := fun _ _ _ _ => True)
         (P1 := fun _ _ _ _ => True);
    auto; intros.
  - left. exists name, ty.
    induction ctx as [| [key value] rest].
    + discriminate.
    + simpl in e. destruct (String.eqb name key) eqn:E.
      * left. apply String.eqb_eq in E. subst.
        injection e. intros; subst. auto.
      * right. apply IHrest. exact e.
  - right. eauto.
Qed.
