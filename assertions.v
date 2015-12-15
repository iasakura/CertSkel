Require Export assertion_lemmas.
Require Import PHeap.
Require Import Lang.
Ltac last_slist :=
  let H := fresh "H" in
  match goal with
    | [ |- (?P ** ?R) ?s ?h ] =>
      eapply scRw; [clear; intros ? ? H; exact H | clear; intros ? ? H; last_slist; exact H | idtac];
      apply scA'
    | _ => idtac
  end.

Ltac append_slist :=
  let H := fresh "H" in
  match goal with
    | [ |- ((?P ** ?Q) ** ?R) ?s ?h ] =>
      eapply scRw; [clear; intros ? ? H; last_slist; exact H | clear; intros ? ? H; exact H | idtac];
      apply scA; append_slist
    | [ |- _ ] => idtac
  end.

Ltac test_ex :=
  match goal with
    | [ |- exists x, ?P] => idtac P
  end.

Goal exists x, x + 1 = 10.
test_ex.
Abort.

Ltac sep_normal :=
  let H := fresh "H" in
  match goal with
    | [ |- (emp ** ?P) ?s ?h ] => apply sc_emp1; sep_normal 
    | [ |- (?P ** emp) ?s ?h ] => apply sc_emp2; sep_normal
(*    | [ |- (?P ** !(?Q)) ?s ?h ] => apply scban_r; [sep_normal | ]
    | [ |- (!(?P) ** ?Q) ?s ?h ] => apply scban_l; [ | sep_normal ]*)
    | [ |- (Ex _, _) ?s ?h ] => eapply scEx; [clear; intros ? ? ? H; sep_normal; exact H | idtac ]
    | [ |- (?P ** ?Q) ?s ?h] => 
      eapply scRw; [clear; intros ? ? H; sep_normal; exact H |
                    clear; intros ? ? H; sep_normal; exact H | idtac];
      append_slist
    | _ => idtac
  end.

Goal forall (P : nat -> assn) s h, (Ex x, P x) s h -> False.
Proof.
  intros P s h H. eapply scEx in H.
Abort.

Goal forall (P Q : assn) s h, (P ** Q) s h -> False.
Proof.
  intros P Q s h H. eapply scRw in H.
Abort.


Ltac last_slist_in H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : (?P ** ?R) ?s ?h |- _ ] => match H with H' =>
        eapply scRw in H; [ idtac |
                            clear; intros ? ? Hf; exact Hf |
                            clear; intros ? ? Hf; last_slist_in Hf; exact Hf ];
        apply scA in H
      end
    | _ => idtac
  end.

Ltac append_slist_in H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : ((?P ** ?Q) ** ?R) ?s ?h |- _ ] => match H with H' =>
        eapply scRw in H; [ idtac |
                            clear; intros ? ? Hf; last_slist_in Hf; exact Hf |
                            clear; intros ? ? Hf; exact Hf ];
        apply scA' in H; append_slist_in H
      end
    | [ |- _ ] => idtac
  end.

Ltac sep_normal_in H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : (emp ** ?P) ?s ?h |- _ ] => match H with H' =>
        apply sc_emp1' in H; sep_normal_in H
      end
    | [ H' : (?P ** emp) ?s ?h |- _ ] => match H with H' =>
        apply sc_emp2' in H; sep_normal_in H
      end
    | [ H' : (Ex _, _) ?s ?h |- _ ] => match H with H' => 
        eapply scEx in H; [ idtac | clear; intros ? ? ? Hf; sep_normal_in Hf; exact Hf ]
      end
    | [ H' : (?P ** ?Q) ?s ?h |- _ ] => match H with H' => 
        eapply scRw in H; [ idtac |
                            clear; intros ? ? Hf; sep_normal_in Hf; exact Hf |
                            clear; intros ? ? Hf; sep_normal_in Hf; exact Hf ];
        append_slist_in H
      end
    | _ => idtac
  end.

Ltac sep_lift_in H n :=
  idtac "called";
  match goal with
    | [ H' : (Ex _, _) ?s ?h |- _ ] => match H' with H =>
      idtac "match first case";
      match n with
        | O => fail 2
        | S ?n => 
          let Hf := fresh "H" in
          eapply scEx in H; [idtac | clear; intros ? ? ? Hf; sep_lift_in Hf n; exact Hf] 
      end end
    | [ H' : (_ ** _ ** _) ?s ?h |- _ ] => match H' with H =>
      idtac "match second case";
      match n with
        | 0 => idtac
        | S ?n => 
          let Hf := fresh "H" in
          eapply scRw in H; [idtac |
                        clear; intros ? ? Hf; exact Hf | 
                        clear; intros ? ? Hf; sep_lift_in Hf n; exact Hf];
          apply scCA in H
      end end
    | [ H' : (_ ** _) ?s ?h |- _] => match H' with H =>
      idtac "match third case";
      match n with
        | 0 => idtac
        | S ?n => apply scC in H
      end end
    | _ => idtac
  end.

Ltac find_ban Ps k :=
  match Ps with
    | !(?P) => k (Some 0)
    | !(?P) ** _ => k (Some 0)
    | _ ** ?Ps => find_ban Ps ltac:(fun n =>
        idtac "debug:" n;
        match n with false => k false | Some ?n => k (Some (S n)) end)
    | _ => k false
  end.

Ltac sep_lift n :=
  let pred_n n k :=
    match n with
      | S ?n => k n
      | 0 => fail 2; k 0
    end in
  match goal with
    | [ |- (Ex _, _) ?s ?h ] => 
      pred_n n ltac:(fun n =>
        let H := fresh "H" in
        eapply scEx; [clear; intros ? ? ? H; sep_lift n; exact H| idtac] )
    | [ |- (_ ** _ ** _) ?s ?h ] =>
      match n with
        | 0 => idtac
        | S ?n => 
          let H := fresh "H" in
          eapply scRw; [clear; intros ? ? H; exact H | 
                        clear; intros ? ? H; sep_lift n; exact H|
                        idtac];
          apply scCA
      end
    | [ |- (_ ** _) ?s ?h ] =>
      match n with
        | 0 => idtac
        | S ?n => apply scC
      end
    | _ => idtac
  end.

Ltac sep_split :=
  let H := fresh "H" in
  match goal with
    | [ |- !(?P) ?s ?h] => apply pure_emp
    | [ |- ?P ?s ?h ] => 
      find_ban P ltac:(fun n =>
      match n with
        | false => idtac
        | Some ?n => sep_lift n; apply scban_l; [ idtac | sep_split ]
      end)
  end.

Goal forall (P Q R : assn) s h, (!(P) ** Q ** !(R)) s h.
Proof.
  intros; sep_split.
Abort.

Example sep_split_in_test1 (P Q R S : assn) s h :
  ((P ** !(Q)) ** (R ** S)) s h -> (P ** !(Q) ** R ** S) s h.
Proof.
  intros. 
  sep_split.
Abort.

Lemma pure_emp_in (P : assn) (s : stack) (h : pheap) :
  !(P) s h -> P s (emp_ph loc) /\ emp s h.
Proof.
  unfold_conn; simpl; destruct 1.
  apply emp_emp_ph_eq in H; subst; split; auto.
Qed.

Ltac sep_split_in H :=
  repeat (match goal with
    | [ H' : !(?P) ?s ?h |- _] => match H' with H =>
      let HP := fresh "HP" in
      apply pure_emp_in in H'; destruct H' as [HP H]
      end
    | [ H' : ?P ?s ?h |- _ ] => match H' with H =>
      find_ban P ltac:(fun n =>
      idtac "debug" n;
      match n with
        | false => idtac
        | Some ?n =>
          let HP := fresh "HP" in
          sep_lift_in H n; apply scban_l' in H as [HP H]
      end)
  end end).


Goal forall P Q R, (Ex x : nat, (P ** Q ** R)) |= P ** Q ** R.
Proof.
  intros P Q R s h H.
  eapply scEx in H.
Abort.

Goal forall P Q R, (P ** Q ** R) |= P ** Q ** R.
Proof.
  intros P Q R s h H.
  eapply scRw in H;
    [ idtac |
      intros ? ? Hf; exact Hf |
      intros ? ? Hf; apply scC in Hf; exact Hf ];
  apply scCA in H.
Abort.

Ltac find_assn P Qs k :=
  match Qs with
    | P => k (Some 0)
    | P ** _ => k (Some 0)
    | _ ** ?Qs => find_assn P Qs ltac:(fun n => 
       match n with false => k false | Some ?n => k (Some (S n)) end)
    | _ => k false
  end.

Ltac search_match P Q k :=
  match Q with
    | ?R ** ?Q => find_assn R P ltac:(fun n =>
      match n with
        | Some ?n => k (Some (n, 0))
        | false => search_match P Q ltac:(fun p =>
          match p with
            | Some (?n, ?m) => k (Some (n, S m))
            | false => k false
          end)
      end)
    | _ => k false
  end.

Ltac simplify_loc :=
  lazymatch goal with
    | [|- GLoc _ = GLoc _] => f_equal
    | [|- SLoc _ = SLoc _] => f_equal
    | _ => idtac
  end.

Ltac find_enough_resource E H :=
  match goal with _ => idtac end;
  match type of H with ?P => idtac "debug" P end;
  match type of H with
    | ((?E0 -->p (_, ?E1)) ?s ?h) => 
      let Hf := fresh in
      assert (Hf : ((E0 ===l E) s (emp_ph loc))) by
          (unfold_conn_all; simpl in *; unfold lt in *; simplify_loc;
           first [congruence | omega | eauto with zarith]);
      apply (mapsto_rewrite1 Hf) in H
    | ((?E0 -->p (_, ?E1) ** _) ?s _) =>
      let Hf := fresh in
      assert (Hf : (E0 ===l E) s (emp_ph loc)) by
          (unfold_conn_all; simpl in *; unfold lt in *; simplify_loc;
           first [congruence | omega | eauto with zarith]);
      let hf := fresh in let Hf' := fresh in 
      idtac "found: " E0 E;
      eapply scRw_stack in H;
      [idtac |
       intros hf Hf'; eapply (mapsto_rewrite1 Hf) in Hf'; exact Hf' |
       clear; intros ? Hf'; exact Hf'];
      clear Hf
    | ((_ ** _) _ _) =>
      let Hf := fresh in
      eapply scRw_stack in H; [idtac | clear; intros ? Hf; exact Hf |
                               intros ? Hf; find_enough_resource E Hf; exact Hf];
      match goal with _ => idtac  end;
(*      match goal with [ H' : ?P |- _ ] => match H with H' => match P with*)
      match type of H with
        | ((_ ** _ ** _) _ _) => apply scCA in H
        | ((_ ** _) _ _) => apply scC in H
      end 
    | _ => idtac
  end.

Ltac search_addr E0 E1 H :=
  find_enough_resource E0 H;
  match type of H with
    | (?E0' -->p (_, ?E1')) ?s ?h =>
      let Hf := fresh in
      assert (Hf : ((E1' === E1) s (emp_ph loc))) by (unfold_conn_all; simpl in *; unfold lt in *;
                                           first [congruence | omega | eauto with earith]);
      apply (mapsto_rewrite2 Hf) in H
    | ((?E0' -->p (_, ?E1') ** _) ?s _) =>
      let Hf := fresh in
      assert (Hf : (E1' === E1) s (emp_ph loc)) by (unfold_conn_all; simpl in *; unfold lt in *;
                                           first [congruence | omega | eauto with earith]);
      let hf := fresh in let Hf' := fresh in 
      eapply scRw_stack in H;
      [idtac |
       intros hf Hf'; eapply (mapsto_rewrite2 Hf) in Hf'; exact Hf' |
       clear; intros ? Hf'; exact Hf'];
      clear Hf
  end.

Ltac search_same_maps H :=
  match goal with
    | [ |- ((?E0 -->p (_, ?E1)) ** ?Q) _ _ ] => search_addr E0 E1 H
    | [ |- ((?E0 -->p (_, ?E1))) _ _ ] => search_addr E0 E1 H
    | [ |- (_ ** ?Q) _ _ ] =>
      let Hf := fresh in
      eapply scRw_stack; [clear; intros ? Hf; exact Hf |
                          clear; intros ? Hf; search_same_maps H; exact Hf | idtac ]
  end.  

(* Ltac sep_cancel2 := *)
(*   match goal with *)
(*     | [H : ?P ?s ?h |- ?Q ?s ?h ] => *)
(*       idtac "cancel2:" P Q; *)
(*       search_same_maps H; *)
(*       let Hf := fresh in *)
(*       exact H || *)
(*       (eapply scRw_stack; [intros ? Hf; exact Hf | clear H; intros ? H | exact H ]) || *)
(*       (eapply (@sc_emp2 _ s h) in H; eapply scRw_stack; [intros ? Hf; exact Hf | clear H; intros ? H | exact H ]) *)
(*     | _ => idtac *)
(*   end. *)

(* Ltac sep_cancel := *)
(*   match goal with *)
(*     | [ H : ?P ?s ?h |- ?P ?s ?h] => exact H *)
(*     | [ H : (?P ** ?Q) ?s ?h |- (?P ** ?R) ?s ?h] => *)
(*       let Hf := fresh "H" in *)
(*       eapply scRw; [ intros ? ? Hf; exact Hf |  *)
(*                      clear s h H; intros s h H | *)
(*                      exact H] *)
(*     | [ H : ?P ?s ?h |- ?Q ?s ?h ] => *)
(*       search_match P Q ltac:(fun p =>  *)
(*       match p with *)
(*         | Some (?n, ?m) => *)
(*           sep_lift m; sep_lift_in H n; *)
(*           let Hf := fresh "H" in *)
(*           eapply scRw_stack; [ intros ? Hf; exact Hf |  *)
(*                                intros ? ? | *)
(*                                exact H ] *)
(*       end) *)
(*     | [ H : ?P ?s (emp_ph loc), H' : emp ?s ?h |- !(?P) ?s ?h ] => *)
(*       eapply pure_emp; eauto *)
(*     | _ => sep_cancel2 *)
(*   end. *)

Ltac sep_cancel :=
  auto;
  match goal with
    | [ H : ?P ?s ?h |- ?Q ?s ?h ] =>
      search_match P Q ltac:(fun p => 
      match p with
        | Some (?n, ?m) =>
          sep_lift m; sep_lift_in H n;
          let Hf := fresh "H" in
          eapply scRw_stack; [ clear; intros ? Hf; exact Hf | 
                               intros ? ? |
                               exact H ]
      end)
    | [H : ?P ?s ?h |- ?Q ?s ?h ] =>
      search_same_maps H;
      let Hf := fresh in
      exact H ||
      (eapply scRw_stack; [clear; intros ? Hf; exact Hf | clear H; intros ? H | exact H ]) (*||*)
    | _ => idtac
  end.

Ltac sep_combine_in H :=
  repeat match type of H with
    | ?P ?s ?h =>
      match goal with
        | [ H' : ?Q ?s (emp_ph loc) |- _ ] =>
          apply (scban_l H') in H; sep_lift_in H 1; clear H'
      end
  end.
