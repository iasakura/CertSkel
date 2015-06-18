Require Export assertion_lemmas.
Require Import PHeap.

Ltac last_slist :=
  let H := fresh "H" in
  match goal with
    | [ |- (?P ** ?R) ?s ?h ] =>
      eapply scRw; [intros ? ? H; exact H | intros ? ? H; last_slist; exact H | idtac];
      apply scA
    | _ => idtac
  end.

Ltac append_slist :=
  let H := fresh "H" in
  match goal with
    | [ |- ((?P ** ?Q) ** ?R) ?s ?h ] =>
      eapply scRw; [intros ? ? H; last_slist; exact H | intros ? ? H; exact H | idtac];
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
    | [ |- (?P ** !(?Q)) ?s ?h ] => apply scban_r; [sep_normal | ]
    | [ |- (!(?P) ** ?Q) ?s ?h ] => apply scban_l; [ | sep_normal ]
    | [ |- (Ex _, _) ?s ?h ] => eapply scEx; [intros ? ? ? H; sep_normal; exact H | idtac ]
    | [ |- (?P ** ?Q) ?s ?h] => 
      eapply scRw; [intros ? ? H; sep_normal; exact H |
                    intros ? ? H; sep_normal; exact H | idtac];
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

Goal forall (P Q R : assn) s h, ((P ** Q) ** R) s h -> False.
Proof.
  intros P Q R s h H. eapply scRw in H.
Abort.

Ltac last_slist_in H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : (?P ** ?R) ?s ?h |- _ ] => match H with H' =>
        eapply scRw in H; [ idtac |
                            intros ? ? Hf; exact Hf |
                            intros ? ? Hf; last_slist_in Hf; exact Hf ];
        apply scA in H
      end
    | _ => idtac
  end.

Ltac append_slist_in H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : ((?P ** ?Q) ** ?R) ?s ?h |- _ ] => match H with H' =>
        eapply scRw in H; [ idtac |
                            intros ? ? Hf; last_slist_in Hf; exact Hf |
                            intros ? ? Hf; exact Hf ];
        apply scA' in H; append_slist_in H
      end
    | [ |- _ ] => idtac
  end.

Ltac sep_normal_in' H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : (emp ** ?P) ?s ?h |- _ ] => match H with H' =>
        apply sc_emp1' in H; sep_normal_in' H
      end
    | [ H' : (?P ** emp) ?s ?h |- _ ] => match H with H' =>
        apply sc_emp2' in H; sep_normal_in' H
      end
    | [ H' : (Ex _, _) ?s ?h |- _ ] => match H with H' => 
        eapply scEx in H; [ idtac | intros ? ? ? Hf; sep_normal_in' Hf; exact Hf ]
      end
    | [ H' : (?P ** ?Q) ?s ?h |- _ ] => match H with H' => 
        eapply scRw in H; [ idtac |
                            intros ? ? Hf; sep_normal_in' Hf; exact Hf |
                            intros ? ? Hf; sep_normal_in' Hf; exact Hf ];
        append_slist_in H
      end
    | _ => idtac
  end.

Ltac sep_lift_in H n :=
  match goal with
    | [ H' : (Ex _, _) ?s ?h |- _ ] => match H' with H =>
      match n with
        | O => fail 2
        | S ?n => 
          let Hf := fresh "H" in
          eapply scEx in H; [idtac | intros ? ? ? Hf; sep_lift_in Hf n; exact Hf] 
      end end
    | [ H' : (_ ** _ ** _) ?s ?h |- _ ] => match H' with H =>
      match n with
        | 0 => idtac
        | S ?n => 
          let Hf := fresh "H" in
          eapply scRw in H; [idtac |
                        intros ? ? Hf; exact Hf | 
                        intros ? ? Hf; sep_lift_in Hf n; exact Hf];
          apply scCA in H
      end end
    | [ H' : (_ ** _) ?s ?h |- _] => match H' with H =>
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

Ltac sep_normal_in H :=
  sep_normal_in' H;
  repeat (match goal with
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
        eapply scEx; [intros ? ? ? H; sep_lift n; exact H| idtac] )
    | [ |- (_ ** _ ** _) ?s ?h ] =>
      match n with
        | 0 => idtac
        | S ?n => 
          let H := fresh "H" in
          eapply scRw; [intros ? ? H; exact H | 
                       intros ? ? H; sep_lift n; exact H|
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

Ltac sep_cancel :=
  match goal with
    | [ H : ?P ?s ?h |- ?P ?s ?h] => exact H
    | [ H : (?P ** ?Q) ?s ?h |- (?P ** ?R) ?s ?h] =>
      let Hf := fresh "H" in
      eapply scRw; [ intros ? ? Hf; exact Hf | 
                     clear s h H; intros s h H |
                     exact H]
    | [ H : ?P ?s ?h |- ?Q ?s ?h ] =>
      search_match P Q ltac:(fun p => 
      match p with
        | Some (?n, ?m) =>
          sep_lift m; sep_lift_in H n;
          sep_cancel
        | None => idtac
      end)
  end.