(* A reimplementation of the Iris proof to inline dependencies.
 * It exists purely so that all the proofs of programs are contained
 * in this repo.
 *)
From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl. (* We need the fractional monoid *)
Set Default Proof Using "Type".

(* The parallel composition operator *)
Definition wait : val :=
  rec: "wait" "x" :=
    match: ! "x" with
      SOME "a" => "a"
    | NONE => "wait" "x"
    end.
Definition par : val :=
  λ: "p",
    let: "r" := ref NONE in
    Fork ("r" <- SOME (Fst "p" #()));;
    let: "y" := Snd "p" #() in
    let: "x" := wait "r" in
    ("x", "y").

(* Largely boiler plate to express that we want exclusive monoid
 * available to us. The details are not interesting unelss one is
 * particularly interested how iris-coq handles gfunctors.
 *)
Class parG Σ := ParG { par_tokG :> inG Σ (exclR unitC) }.
Definition parΣ : gFunctors := #[GFunctor (exclR unitC)].

Instance subG_parΣ {Σ} : subG parΣ Σ → parG Σ.
Proof. solve_inG. Qed.

Section proofs.
  Context `{!heapG Σ, !parG Σ} (N : namespace).

  (* The invariant features 3 cases, either
   *  - no write has happened
   *  - no read has happened
   *  - both have happened
   * Each of these is handled by a case of the theorem.
   *)
  Definition cell_inv γ (ℓ : loc) P : iProp Σ :=
    (ℓ ↦ NONEV ∨
     (∃ v, ℓ ↦ SOMEV v ∗ P v) ∨
     (∃ v, ℓ ↦ SOMEV v ∗ own γ (Excl ())))%I.

  Lemma wait_spec (ℓ : loc) P γ :
    (own γ (Excl ()) ∗ inv N (cell_inv γ ℓ P)
         -∗ WP wait #ℓ {{ v, P v }})%I.
  Proof.
    iIntros "[Hexcl #Hinv]".
    iLöb as "IH".
    wp_lam.
    wp_bind (Load _).
    iInv N as "Hcell" "Hclose".
    iDestruct "Hcell" as "[Hfirst | [Hsecond | Hthird]]".
    - wp_load.
      iMod ("Hclose" with "[Hfirst]").
      { iNext; iLeft; eauto. }
      iModIntro.
      wp_match.
      by iApply "IH".
    - iDestruct "Hsecond" as (v) "[Hl HP]".
      wp_load.
      iMod ("Hclose" with "[Hl Hexcl]").
      { iNext; iRight; iRight; iFrame.
        iExists v; eauto. }
      iModIntro.
      by wp_match.
    - iDestruct "Hthird" as (v) "[Hl Hexcl']".
      wp_load.
      iDestruct (own_valid_2 with "Hexcl Hexcl'") as %[].
  Qed.

  Theorem par_spec P Q (f g : val) `{Hef : !IntoVal e (f, g)} :
    (∀ Φ, WP f #() {{ v, P v }}
       -∗ WP g #() {{ v, Q v }}
       -∗ (∀ p, (∃ v₁ v₂, ⌜p = (v₁, v₂)%V⌝ ∗ P v₁ ∗ Q v₂) -∗ Φ p)
        -∗ WP par e {{ p, Φ p}})%I.
  Proof using N heapG0 parG0 Σ.
    apply of_to_val in Hef as <-.
    iIntros (Φ) "Hwp1 Hwp2 HΦ".
    wp_lam.
    wp_alloc ℓ as "Hl".
    wp_let.
    iMod (own_alloc (Excl ())) as (γ) "Hown"; first done.
    iMod (inv_alloc N _ (cell_inv γ ℓ P) with "[Hl]" ) as "#Hinv".
    { iNext; iLeft; eauto. }
    wp_apply wp_fork; iSplitR "Hwp1".
    - wp_let.
      wp_proj.
      wp_bind (g _).
      iApply (wp_strong_mono with "Hwp2 [Hown HΦ]"); eauto.
      iIntros (v) "HQ".
      iModIntro.
      wp_let.
      wp_bind (wait _).
      iApply (wp_strong_mono _ _ ⊤ _ _ P with "[Hown Hinv] [HΦ HQ]"); eauto.
      { iDestruct (wait_spec with "[Hown Hinv]") as "H"; eauto. }
      iIntros (v') "HP".
      iModIntro.
      wp_let.
      iApply "HΦ".
      iExists _, _; iFrame; eauto.
    - wp_proj.
      wp_bind (f _).
      iApply (wp_strong_mono _ _ ⊤ _ _ P with "Hwp1"); eauto.
      iIntros (v) "HP".
      iModIntro.
      iInv N as "Hopen" "Hclose".
      iDestruct "Hopen" as "[Hfirst | [Hsecond | Hthird]]".
      * wp_store.
        iMod ("Hclose" with "[Hfirst HP]") as "_".
        { iNext; iRight; iLeft. iExists _; iFrame. }
        eauto.
      * iDestruct "Hsecond" as (v') "[Hl HP']".
        wp_store.
        iMod ("Hclose" with "[Hl HP]") as "_".
        { iNext; iRight; iLeft. iExists _; iFrame. }
        eauto.
      * iDestruct "Hthird" as (v') "[Hl Hown]".
        wp_store.
        iMod ("Hclose" with "[Hl HP]") as "_".
        { iNext; iRight; iLeft. iExists _; iFrame. }
        eauto.
  Qed.
End proofs.

Notation "e1 ||| e2" := (par (Pair (λ: <>, e1) (λ: <>, e2)))%E : expr_scope.
