(* In order to run this code you must have iris-coq installed,
 * available via [opam]
 *)
From iris.program_logic Require Export weakestpre. (* Get the definition of weakest preconditions *)
From iris.heap_lang Require Export lang. (* Get the Coq definition of the ML like language *)
From iris.proofmode Require Import tactics. (* Tools for manipulating Iris Predicates *)
From iris.heap_lang Require Import proofmode notation. (* Tactics/notation specific to ML-like language *)
From iris.algebra Require Import frac. (* We need the fractional monoid *)
From iris.heap_lang.lib Require Import spawn par. (* Gives us the parallel execution operator *)
Set Default Proof Using "Type".

(* First we define the program we actually wish to verify
 * as a Gallina term. The notation makes this look a little
 * bit more
 *)
Definition parallel_increment : val :=
  λ: "_",
  let: "x" := ref #0 in
  ("x" <- ! "x" + #1) ||| ("x" <- ! "x" + #1);;
  !"x".

(* Now that we have the code, we need to verify it. *)
Section proofs.
  (* We need to specify what ghost state is available in Σ,
   * our list of cameras. We specify that the fraction & auth CMRAs
   * is available along with the ghost state needed to represent
   * the heap (↦ and similar). spawnG includes all the ghost
   * state needed for par and its proof We also include a
   * namespace for our invariants in case someone wants to use
   * this code somwhere else.
   *)
  Context `{inG Σ fracR, spawnG Σ, heapG Σ} (N : namespace).

  (* These shorthands are not really necessary but it's
   * helpful to make the lemmas we need about manipulating
   * this ghost state explicit.
   *)
  Definition half γ : iProp Σ := own γ (1 / 2)%Qp.
  Definition one γ : iProp Σ := own γ 1%Qp.
  Definition epsilon γ : iProp Σ := (∃ q, own γ q)%I.

  Lemma split_one γ :
    (one γ -∗ half γ ∗ half γ)%I.
  Proof.
    (* Intros tactic automatically knows about splitting ghost
     * state for many of the cases. Makes this quite simple.
     *)
    iIntros "[Hown1 Hown2]".
    iFrame.
  Qed.

  Lemma split_epsilon γ :
    (epsilon γ -∗ epsilon γ ∗ epsilon γ)%I.
  Proof.
    (* Intros tactic automatically knows about splitting ghost
     * state for many of the cases. Makes this quite simple.
     *)
    iIntros "H".
    iDestruct "H" as (q) "[Hown1 Hown2]".
    iSplitL "Hown1"; iExists (q / 2)%Qp; eauto.
  Qed.

  Lemma combine_half γ :
    (half γ ∗ half γ -∗ one γ)%I.
  Proof.
    iIntros "Hown".
    rewrite -own_op.
    rewrite frac_op' Qp_div_2.
    eauto.
  Qed.

  Lemma combine_contra γ (P : iProp Σ) :
    (epsilon γ ∗ one γ -∗ P)%I.
  Proof.
    iIntros "[Hown1 Hown2]".
    iDestruct "Hown1" as (q) "Hown1".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hvalid.
    erewrite frac_valid', frac_op' in Hvalid.
    destruct Qp_not_plus_q_ge_1 with q.
    rewrite comm; eauto.
  Qed.

  (* Finally, let us write down the invariant we intend to use
   * for "r" in our program.
   *)
  Definition inc_inv (γ γ' : gname) (ℓ : loc) :=
    ((ℓ ↦ #0 ∗ one γ) ∨
     (ℓ ↦ #1 ∗ epsilon γ ∗ half γ') ∨
     ((ℓ ↦ #1 ∨ ℓ ↦ #2) ∗ one γ'))%I.

  (* Let us prove the branches of the par satisfy the spec
   * we expect them to. By factoring this out we avoid some
   * code duplication
   *)
  Lemma branch_spec γ γ' ℓ :
    ∀ n : nat, (inv N (inc_inv γ γ' ℓ) ∗ half γ' -∗
         WP (#ℓ <- !(#ℓ) + #1) {{ _, epsilon γ }})%I.
  Proof.
    wp_load.
    iIntros "[#Hinv Hhalfγ']".
    wp_bind (Load _).
    iInv N as "Hinc" "Hclose".
    iDestruct "Hinc" as "[Hisone | [Histwo | Histhree]]".
    * iDestruct "Hisone" as "[Hl Hγ]".
      wp_load.
      iMod ("Hclose" with "[Hl Hγ]") as "_".
      { iNext; iLeft; iFrame. }
      iModIntro.
      wp_op; rewrite Z.add_0_l.
      iInv N as "Hinc" "Hclose".
      iDestruct "Hinc" as "[Hisone | [Histwo | Histhree]]".
      + iDestruct "Hisone" as "[Hl Hγ]".
        wp_store.
        iDestruct (split_one with "Hγ") as "[Hγ1 Hγ2]".
        iMod ("Hclose" with "[Hl Hγ1 Hhalfγ']") as "_".
        { iNext; iRight; iLeft; iFrame.
          by iExists (1/2)%Qp. }
        by iExists (1/2)%Qp.
      + iDestruct "Histwo" as "[Hl [Hγ Hhalfγ'']]".
        wp_store.
        iMod ("Hclose" with "[Hl Hhalfγ' Hhalfγ'']") as "_".
        { iNext; iRight; iRight; iFrame.
          iApply combine_half; iFrame. }
        eauto.
      + iDestruct "Histhree" as "[Hl Hγ']".
        (* Doesn't naively work *)
        (* iApply (combine_contra with "[Hhalfγ' Hγ']").
         * iFrame.
         *)
        iDestruct "Hl" as "[Hl | Hl]";
          wp_store;
          iApply (combine_contra with "[Hγ' Hhalfγ']");
          iFrame;
          by iExists (1/2)%Qp.
    * iDestruct "Histwo" as "[Hl [Hhalfγ'' Hγ]]".
      wp_load.
      iDestruct (split_epsilon with "Hhalfγ''") as "[Hhalfγ'' Heps]".

      iMod ("Hclose" with "[Hl Hγ Hhalfγ'']") as "_".
      { iNext; iRight; iLeft; iFrame. }
      iModIntro.
      wp_op.
      replace (1 + 1) with 2; last by eauto.
      iInv N as "Hinc" "Hclose".
      iDestruct "Hinc" as "[Hisone | [Histwo | Histhree]]".
      + iDestruct "Hisone" as "[Hl Hγ]".
        wp_store.
        iApply (combine_contra with "[Hγ Heps]"); iFrame.
      + iDestruct "Histwo" as "[Hl [Hγ1 Hhalfγ'']]".
        wp_store.
        iMod ("Hclose" with "[Hl Hhalfγ' Hhalfγ'']") as "_".
        { iNext; iRight; iRight; iFrame.
          iApply combine_half; iFrame. }
        eauto.
      + iDestruct "Histhree" as "[Hl Hγ']".
        iDestruct "Hl" as "[Hl | Hl]";
          wp_store;
          iApply (combine_contra with "[Hγ' Hhalfγ']");
          iFrame;
          by iExists (1/2)%Qp.
   * iDestruct "Histhree" as "[Hl Hγ']".
     iDestruct "Hl" as "[Hl | Hl]";
       wp_load;
       iApply (combine_contra with "[Hγ' Hhalfγ']");
       iFrame;
         by iExists (1/2)%Qp.
  Qed.

  (* Now we can actually do the proof, with these lemmas in
   * hand
   *)
  Theorem parallel_increment_spec :
    (WP parallel_increment #() {{ v, ⌜v = #1⌝ ∨ ⌜v = #2⌝ }})%I.
  Proof using H H0 H1 N Σ.
    wp_lam.
    wp_alloc ℓ as "Hl".
    wp_let.
    wp_bind (par _).
    iMod (own_alloc 1%Qp) as (γ) "Hγ"; first done.
    iMod (own_alloc 1%Qp) as (γ') "Hγ'"; first done.
    iMod (inv_alloc N _ (inc_inv γ γ' ℓ) with "[Hl Hγ]") as "#?".
    { iNext; iLeft; iFrame. }

    iDestruct (split_one with "Hγ'") as "[Hγ'1 Hγ'2]".
    iApply (wp_par with "[Hγ'1] [Hγ'2] []").
    - iApply (branch_spec γ γ' with "[Hγ'1]").
      by iFrame.
    - iApply (branch_spec γ γ' with "[Hγ'2]").
      by iFrame.
    - iIntros (v1 v2) "[Heps1 Heps2]".
      iNext.
      wp_let.
      iInv N as "Hinc" "Hclose".
      iDestruct "Hinc" as "[Hisone | [Histwo | Histhree]]".
      + iDestruct "Hisone" as "[Hl Hγ]".
        wp_load.
        iApply (combine_contra with "[Hγ Heps1]");
          by iFrame.
      + iDestruct "Histwo" as "[Hl [Hγ1 Hhalfγ'']]".
        wp_load.
        iMod ("Hclose" with "[Hl Hγ1 Hhalfγ'']").
        { iNext; iRight; iLeft; iFrame. }
        eauto.
      + iDestruct "Histhree" as "[Hl Hγ']".
        iDestruct "Hl" as "[Hl | Hl]";
          wp_load;
          iMod ("Hclose" with "[Hl Hγ']");
          try (iNext; iRight; iRight; iFrame);
          eauto.
  Qed.
End proofs.
