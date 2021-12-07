From Coq Require Import Bool List Program Lia.
From MetaCoq.Template Require Import config utils.
Require Import MetaCoq.Template.Universes.
From MetaCoq.PCUIC Require Import PCUICAst PCUICValidity PCUICGeneration
     PCUICTyping PCUICWeakeningEnv PCUICWeakening.

From MetaCoq.PCUIC Require Import PCUICSigmaCalculus.
Set Printing All.

Definition universes_decl_extends (u v: universes_decl) : Type :=
  match (u,v) with
  | (Monomorphic_ctx u', Monomorphic_ctx v') => LevelSet.Subset (fst u') (fst v') * ConstraintSet.Subset (snd u') (snd v')
  | (Polymorphic_ctx u', Polymorphic_ctx v') => True
  | _ => False
  end.

Lemma universes_decl_extends_wf_local `{checker_flags} Σ Γ (wfΓ : wf_local Σ Γ):
  All_local_env_over typing
         (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ)
            (t T : term) (_ : Σ;;; Γ |- t : T) =>
          forall u : ContextSet.t,
          (*satisfiable_udecl Σ.1 (Monomorphic_ctx u) ->*)
          universes_decl_extends Σ.2 (Monomorphic_ctx u) ->
          (Σ.1, Monomorphic_ctx u);;; Γ |- t : T) Σ Γ wfΓ ->
  forall u, (*satisfiable_udecl Σ.1 (Monomorphic_ctx u) ->*)
            universes_decl_extends Σ.2 (Monomorphic_ctx u) ->
            wf_local (Σ.1, Monomorphic_ctx u) Γ.
Proof.
  intros. induction X; econstructor; pose (X1 := X0);
    specialize p with u; apply p in X1;
    pose (X2 := X1);
    try (apply typing_wf_local in X2; specialize p0 with u; apply p0 in X0);
    try solve [eauto|eassumption]; exists (tu.π1); eassumption.
Qed.

Lemma weakening_universe_decl_cumul `{CF:checker_flags} Σ u Γ M N :
  (*satisfiable_udecl Σ.1 (Monomorphic_ctx u) ->*)
  universes_decl_extends Σ.2 (Monomorphic_ctx u) ->
  cumul Σ Γ M N -> cumul (Σ.1, (Monomorphic_ctx u)) Γ M N.
Proof.
  intros (*st*) univ;
    destruct (Σ.2) eqn: Σ_eq; revgoals; first exfalso; subst; auto.
  induction 1; simpl.
  - econstructor. eapply (PCUICWeakeningEnv.leq_term_subset); revgoals. eassumption.
    unfold global_ext_constraints, ConstraintSet.Subset; intros.
    rewrite ConstraintSet.union_spec.
    rewrite ConstraintSet.union_spec in H.
    cbn in univ. destruct H; eauto using univ, H.
    left. simpl. apply (snd univ). rewrite Σ_eq in H.
    eassumption.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
Qed.

Lemma global_ext_univ_ext Sigma v u:
  universes_decl_extends v u ->
  LevelSet.Subset (global_ext_levels (Sigma, v)) (global_ext_levels (Sigma, u)).
Proof.
  intros.
  destruct v eqn: v_eq; destruct u eqn: u_eq; revgoals; try solve[(exfalso; auto)].
  1: admit.
  unfold global_ext_levels, levels_of_udecl, LevelSet.Subset.
  simpl. intros.
  apply LevelSet.union_spec. apply LevelSet.union_spec in H.
  destruct H; auto; left. now apply (fst X).
Admitted.

Lemma weakening_universe_decl_consist `{checker_flags} Σ phi t u:
  (*satisfiable_udecl Σ.1 (Monomorphic_ctx u) ->*)
  universes_decl_extends Σ.2 (Monomorphic_ctx u) ->
  consistent_instance_ext Σ phi t ->
  consistent_instance_ext (Σ.1, Monomorphic_ctx u) phi t.
Proof.
  intros univ.
  unfold consistent_instance_ext, consistent_instance. destruct phi.
  - trivial.
  - destruct 1 as [prop [mem [eq vc]]]. split; auto. split.
    + apply forallb_forall. intros x. intros IN. eapply forallb_forall in mem.
      apply LevelSet.mem_spec. apply LevelSet.mem_spec in mem.
      eapply global_ext_univ_ext; eauto. eassumption.
    + split; eauto.
      unfold valid_constraints. unfold valid_constraints in vc.
      destruct check_univs; eauto.
      unfold valid_constraints0.  unfold valid_constraints0 in vc.
      intros. apply vc.
      unfold satisfies. unfold satisfies in H0.
      unfold ConstraintSet.For_all. unfold ConstraintSet.For_all in H0.
      intros x ins. apply H0.
      unfold global_ext_constraints. unfold global_ext_constraints in ins.
      apply ConstraintSet.union_spec. apply ConstraintSet.union_spec in ins.
      destruct ins; auto. left. simpl.
      destruct (Σ.2) eqn: Σ_eq; revgoals. exfalso. auto.
      apply (snd univ). eassumption.
Qed.


Lemma weakening_env_univ `{checker_flags}:
  env_prop (fun Σ Γ t T =>
              forall u, universes_decl_extends Σ.2 (Monomorphic_ctx u) -> (Σ.1, (Monomorphic_ctx u)) ;;; Γ |- t : T).
Proof.
  apply typing_ind_env; intros; rename_all_hyps.
    all: (destruct (Σ.2) eqn: Σ_eq; revgoals; first exfalso; auto;
          try solve[(econstructor; eauto)|eassumption]).
  - econstructor.
    + eapply universes_decl_extends_wf_local; eauto; rewrite Σ_eq; eassumption.
    + eauto.
  - econstructor.
    + eapply universes_decl_extends_wf_local; eauto; rewrite Σ_eq; eassumption.
    + unfold global_ext_levels, levels_of_udecl.
      unfold global_ext_levels, levels_of_udecl in H0.
      apply LevelSet.union_spec. apply LevelSet.union_spec in H0.
      destruct H0; eauto using H0, X0.
      left. apply (fst X0). rewrite Σ_eq in H0. eassumption.
  - econstructor; eauto.
    + eapply universes_decl_extends_wf_local; eauto; rewrite Σ_eq; eassumption.
    + unfold consistent_instance_ext. unfold consistent_instance_ext in H1.
      eapply weakening_universe_decl_consist; try (rewrite Σ_eq); eauto.
  - econstructor; eauto.
    + eapply universes_decl_extends_wf_local; eauto; rewrite Σ_eq; eassumption.
    + eapply weakening_universe_decl_consist; try (rewrite Σ_eq); eauto.
  - econstructor; eauto using X, X0.
    + eapply universes_decl_extends_wf_local; eauto. rewrite Σ_eq. eassumption.
    + eapply weakening_universe_decl_consist; try (rewrite Σ_eq); eauto.
  - econstructor; eauto using X, X0.
    close_Forall. intros; intuition.
  - econstructor; eauto.
    eapply All_local_env_impl. eapply X. simpl; intros.
    unfold lift_typing in *; destruct T; intuition eauto.
    apply b; try rewrite Σ_eq; eauto.
    destruct X2 as [s [tyu Hu]]. exists s. eapply Hu; try rewrite Σ_eq; eauto.
    eapply All_impl; eauto; simpl; intuition eauto.
  - econstructor; eauto.
    eapply All_local_env_impl. eapply X.
    simpl; intros.
    unfold lift_typing in *; destruct T; intuition eauto.
    eapply b; try rewrite Σ_eq; eauto.
    destruct X2 as [s [tyu Hu]]. exists s. eapply Hu; try rewrite Σ_eq; eauto.
    eapply All_impl; eauto; simpl; intuition eauto.
  - econstructor. eauto.
    destruct X2 as [isB|[s [Hu Ps]]].
    + left; auto. destruct isB. destruct x as [ctx' [s' [Heq Hu]]].
      exists ctx', s'. split; eauto.
      eapply universes_decl_extends_wf_local; eauto. rewrite Σ_eq. eassumption.
    + right. exists s. eapply Ps; auto.
    + destruct Σ as [Σ φ].
      eapply weakening_universe_decl_cumul; try rewrite Σ_eq; cbn in wfΓ; eassumption.
Qed.

Definition weaken_decl_univ_prop `{checker_flags}
           (P : global_env_ext -> context -> term -> option term -> Type) :=
  forall Σ v u, wf Σ -> universes_decl_extends v (Monomorphic_ctx u) -> forall Γ t T, P (Σ, v) Γ t T -> P (Σ, (Monomorphic_ctx u)) Γ t T.

Lemma weaken_decl_univ_prop_typing `{checker_flags}:
  weaken_decl_univ_prop (lift_typing typing).
Proof.
  red. intros * * * * *.
  destruct T; simpl.
  - intros Ht.
    eapply (weakening_env_univ (_, _)); eauto.
    eapply typing_wf_local in Ht; eauto.
  - intros [s Ht]. exists s.
    eapply (weakening_env_univ (_, _)); eauto. eapply typing_wf_local in Ht; eauto.
Qed.

Lemma from_validity `{checker_flags} Sigma u Gamma T:
  isWfArity_or_Type (Sigma, u) Gamma T ->
  {u' & (universes_decl_extends u u') × {s & ((Sigma, u') ;;; Gamma |- T : tSort s)}}.
Proof.
  intros.
  destruct X as [isWf | isT];
  revgoals.
  - exists u. split.
    1: {unfold universes_decl_extends, LevelSet.Subset, ConstraintSet.Subset; destruct u; auto. }
    exact isT.
  - destruct isWf as [ctx [s [desteq all_ctx]]].
    dependent induction all_ctx. (*as [all_nil | all_ass | all_def].*)
    + unfold app_context in x.
      symmetry in x.
      apply List.app_eq_nil in x. destruct x as [ctxnil gammanil]. subst.
      assert (T = tSort s). {
        induction T; unfold destArity in desteq; try inversion desteq; auto.
        1-2: rewrite destArity_app in desteq.
        1: destruct (destArity nil T2). 3: destruct (destArity nil T3).
        1-4:cbn in desteq; try destruct p; inversion desteq;
            unfold snoc, app_context in H2; symmetry in H2;
            contradict H2; apply List.app_cons_not_nil. } clear desteq.
      subst.
      eexists. split; revgoals.
      eexists.
    + admit. (*eexists. split; revgoals. eexists.*)
    + admit.
Admitted.
