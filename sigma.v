Set Implicit Arguments.

Require Import Classical Program Reals.
Require Import Logic.ClassicalDescription.
Require Import Sets.Ensembles.

Require Import PropExtensionality PropExtensionalityFacts.

From sflib Require Import sflib.

Theorem ProvPropExt : 
    forall A : Prop,
    A -> A=True.
Proof.
    apply PropExt_imp_ProvPropExt.
    apply propositional_extensionality.
Qed.

Theorem RefutPropExt :
    forall A : Prop,
        ~A -> A=False.
Proof.
    apply PropExt_imp_RefutPropExt.
    apply propositional_extensionality.
Qed.

Theorem NNP_iff_P : 
    forall P, ~~ P <-> P.
Proof.
    i. split.
    apply NNPP.
    intuition.
Qed.

(* Power Set *)
Definition PS (U: Type) := Ensemble (Ensemble U).

Arguments In {U}.
Arguments Complement {U}.

(* Countable Sequence of subset *)
Definition ESeq (U: Type) := nat -> Ensemble U.

Definition CompSeq {U:Type} : (ESeq U) -> (ESeq U) :=
    fun seq : ESeq U => 
        fun n:nat => Complement (seq n).

Definition ESeqUnion {U:Type} (seq : ESeq U) : Ensemble U.
Proof.
    ii.
    rename X into u.
    destruct (excluded_middle_informative (exists n, In (seq n) u)).
    { exact True. }
    { exact False. }
Defined.

Definition ESeqIntersect {U:Type} (seq : ESeq U) : Ensemble U.
Proof.
    ii.
    rename X into u.
    destruct (excluded_middle_informative (forall n, In (seq n) u)).
    { exact True. }
    { exact False. }
Defined.

Theorem ESeqDeMorgan {U:Type}: forall
    (seq : nat -> Ensemble U),
    ESeqIntersect seq = Complement (ESeqUnion (CompSeq seq)).
Proof.
    i. 
    apply functional_extensionality. i.
    unfold ESeqIntersect.
    (* destruct (excluded_middle_informative (forall n : nat, In (seq n) x)). *)
    des_ifs.
    {
        symmetry.
        apply ProvPropExt.
        unfold Complement.
        unfold not.
        unfold In.
        unfold ESeqUnion.
        des_ifs.
        unfold CompSeq in *.
        unfold Complement in *. 
        unfold In in *.
        apply ex_not_not_all in e.
        congruence.
    }
    {
        symmetry.
        apply RefutPropExt.
        unfold Complement.
        unfold In.
        apply NNP_iff_P.
        
        unfold ESeqUnion. des_ifs.
        apply not_all_ex_not in n.
        unfold CompSeq in n0.
        unfold Complement in n0.
        ss.
    }
Qed.


(* Sigma Algebra *)
Class SigAlg {Omega : Type} (F : PS Omega) := {
    comp : forall A : Ensemble Omega, F A -> F (Complement A); 
    conuntalbe_seq : forall 
        (seq : nat -> Ensemble Omega)
        (seq_in : forall n, In F (seq n)),
        In F (ESeqUnion seq); 
}.

Lemma Sig_intersection_closed {Omega : Type}: forall
    (F : PS Omega)
    (sig : SigAlg F)
    (seq : nat -> Ensemble Omega)
    (seq_in : forall n, In F (seq n)),
    In F (ESeqIntersect seq).
Proof.
    i.
    rewrite ESeqDeMorgan.
    apply comp.
    apply conuntalbe_seq.
    i.
    pose proof (seq_in n).
    unfold CompSeq.
    apply comp.
    apply H.
Qed.

(* Mesaure *)
Class Measure {Omega : Type} (F: PS Omega) {F_Sig : SigAlg F} (mu : Ensemble Omega -> R) := {
    positive : forall A, (R0 <=mu A)%R; 
    empty_zero : mu (Empty_set Omega) = R0;
    
}.