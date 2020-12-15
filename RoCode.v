Require Import Strings.String.
Require Import Lists.List.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.
Scheme Equality for list.
Require Import ZArith.


(* Constructor pentru numere naturale *)
Inductive TipNat :=
  | error_nat : TipNat
  | numar : nat -> TipNat.

(* Constructor pentru termeni de tip boolean *)
Inductive TipBool :=
  | error_bool : TipBool
  | boolean : bool -> TipBool.

Inductive TipString :=
  | error_string : TipString
  | sirchar : string -> TipString.

Inductive TipVector :=
  | error_vector : TipVector
  | vector : TipNat -> TipVector -> TipVector.

Coercion numar: nat >-> TipNat.
Coercion boolean: bool >-> TipBool.

(* Constructor pentru toate tipurile posibile ale unei variabile*)
Inductive Rezultat :=
  | nondecl : Rezultat
  | noninit : Rezultat
  | default : Rezultat
  | rez_nat : TipNat -> Rezultat
  | rez_bool : TipBool -> Rezultat
  | rez_string : TipString -> Rezultat
  | rez_vect : TipVector -> Rezultat.

Scheme Equality for Rezultat.

(*Variabilele vor fi de tip string, initial fiind nedeclarate*)
Definition Env := string -> Rezultat.
Definition env : Env := fun x => nondecl.

Compute (env "x").


(*Functie care verifica daca doi termeni au acelasi tip*)

Definition check_type_eq (t1 : Rezultat) (t2 : Rezultat) : bool :=
  match t1 with
    | nondecl => match t2 with 
                     | nondecl => true
                     | _ => false
                     end
    | noninit => match t2 with 
                     | noninit => true
                     | _ => false
                     end
    | default => match t2 with 
                     | default => true
                     | _ => false
                     end
    | rez_nat t1 => match t2 with 
                     | rez_nat t1 => true
                     | _ => false
                     end
    | rez_bool t1 => match t2 with 
                     | rez_bool t1 => true
                     | _ => false
                     end
    | rez_string t1 => match t2 with 
                     | rez_string t1 => true
                     | _ => false
                     end
    | rez_vect t1 => match t2 with 
                     | rez_vect t1 => true
                     | _ => false
                     end
  end.


Compute (check_type_eq (rez_nat 3) (rez_nat 5)). (* true *)
Compute (check_type_eq noninit (rez_nat 17)). (* false *)
Compute (check_type_eq (rez_bool false) (rez_bool true)). (* true *)

Definition update (env : Env) (x : string) (v : Rezultat) : Env :=
  fun y =>
    if (andb (eqb x y ) (check_type_eq (env x) (env y)))
    then v
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Compute (env "y").
Compute (update (update env "y" (default)) "y" (rez_nat 3) "y").
Compute ((update (update (update env "y" default) "y" (rez_nat 10)) "y" (rez_bool true)) "y").


(* Sintaxa aritmetica *)

Inductive AExp :=
| avar: string -> AExp 
| anum: TipNat -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp 
| adiv: AExp -> AExp -> AExp 
| amod: AExp -> AExp -> AExp
| apower: AExp -> AExp -> AExp
| amin: AExp -> AExp -> AExp
| amax: AExp -> AExp -> AExp.

Coercion anum: TipNat >-> AExp.
Coercion avar: string >-> AExp.

(* Notatii operatii aritmetice *)
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "A ^' B" := (apower A B)(at level 44, left associativity).
Notation "A <?> B" := (amin A B)(at level 55, left associativity).
Notation "A >?< B" := (amax A B)(at level 55, left associativity).

Definition plus_TipNat (n1 n2 : TipNat) : TipNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | numar v1, numar v2 => numar (v1 + v2)
    end.

Definition sub_TipNat (n1 n2 : TipNat) : TipNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | numar v1, numar v2 => if Nat.ltb v1 v2
                        then error_nat
                        else numar (v1 - v2)
    end.

Definition mul_TipNat (n1 n2 : TipNat) : TipNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | numar v1, numar v2 => numar (v1 * v2)
    end.

Definition div_TipNat (n1 n2 : TipNat) : TipNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, numar 0 => error_nat
    | numar v1, numar v2 => numar (Nat.div v1 v2)
    end.

Definition mod_TipNat (n1 n2 : TipNat) : TipNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, numar 0 => error_nat
    | numar v1, numar v2 => numar (v1 - v2 * (Nat.div v1 v2))
    end.

Definition power_TipNat (n1 n2 : TipNat) : TipNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | numar v1, numar v2 => numar (v1 ^ v2) 
    end.

Definition max_TipNat (n1 n2 : TipNat) : TipNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | numar v1, numar v2 => numar (max v1 v2) 
    end.

Definition min_TipNat (n1 n2 : TipNat) : TipNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | numar v1, numar v2 => numar (min v1 v2) 
    end.

(* Semantica recursiva pentru operatii aritmetice *)

Fixpoint aeval_r (a : AExp) (env : Env) : TipNat :=
  match a with
  | avar v => match (env v) with
                | rez_nat n => n
                | _ => error_nat
                end
  | anum v => v
  | aplus a1 a2 => (plus_TipNat (aeval_r a1 env) (aeval_r a2 env))
  | amul a1 a2 => (mul_TipNat (aeval_r a1 env) (aeval_r a2 env))
  | asub a1 a2 => (sub_TipNat (aeval_r a1 env) (aeval_r a2 env))
  | adiv a1 a2 => (div_TipNat  (aeval_r a1 env) (aeval_r a2 env))
  | amod a1 a2 => (mod_TipNat (aeval_r a1 env) (aeval_r a2 env))
  | apower a1 a2 => (power_TipNat (aeval_r a1 env) (aeval_r a2 env))
  | amin a1 a2 => (min_TipNat (aeval_r a1 env) (aeval_r a2 env))
  | amax a1 a2 => (max_TipNat (aeval_r a1 env) (aeval_r a2 env))
  end.

(* Semantica Big-Step pentru operatii artimetice *)

Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aeval : AExp -> Env -> TipNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | rez_nat x => x
                                              | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_TipNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_TipNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| minus : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (sub_TipNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_TipNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_TipNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
| power : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (power_TipNat i1 i2) ->
    a1 ^' a2 =[sigma]=> n
| minimum : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (power_TipNat i1 i2) ->
    a1 <?> a2 =[sigma]=> n
| maximum : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (power_TipNat i1 i2) ->
    a1 >?< a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Example minus_error : 1 -' 5 =[ env ]=> error_nat.
Proof.
  eapply minus.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example division_error : 3 /' 0 =[ env ]=> error_nat.
Proof.
  eapply division.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example modulo_error : 3 %' 0 =[ env ]=> error_nat.
Proof.
  eapply modulo.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.


Require Import Ascii.
(* Sintaxa siruri de caractere *)
Inductive CExp :=
| cvar: string -> CExp 
| csir: TipString -> CExp
| char: (option ascii) -> CExp
| concat: CExp -> CExp -> CExp
(*| clength: CExp -> AExp*)
(*| containsn: CExp -> AExp*)
| nth_char: CExp -> AExp -> CExp 
| substringNM: CExp -> AExp -> AExp -> CExp.

Coercion csir: TipString >-> CExp.
Coercion cvar: string >-> CExp.


(* Notatii operatii aritmetice *)
Notation "A +&+ B" := (concat A B)(at level 50, left associativity).
Notation "A 'caracterul' B" := (nth_char A B)(at level 50, left associativity).
Notation "A 'incepand' B 'lungime' C" := (substringNM A B C)(at level 50, left associativity).

Definition concat_TipString (n1 n2 : TipString) : TipString :=
  match n1, n2 with
    | error_string, _ => error_string
    | _, error_string => error_string
    | sirchar v1, sirchar v2 => sirchar (v1 ++ v2)
    end.

Definition nth_char_TipString (n1 : TipString) (n2 : TipNat) : CExp :=
  match n1, n2 with
    | error_string, _ => error_string
    | sirchar v1, error_nat => error_string
    | sirchar v1, numar v2 => (char (get v2 v1))
    end.

Definition substringNM_TipString (n1 : TipString) (N M : TipNat) : TipString :=
  match n1, N, M with
    | error_string, _, _ => error_string
    | _, error_nat, _ => error_string
    | _, _, error_nat => error_string
    | sirchar v1, numar N, numar M => sirchar (substring N M v1)
    end.

(* Sintaxa vectori *)
Inductive VExp :=
| vvar: string -> VExp 
| vect: TipVector -> VExp
| vplus: VExp -> VExp -> VExp (*concatenare*)
| nth_elem: AExp -> VExp -> VExp (*returneaza al n-lea element al vectorului*)
| head: VExp -> VExp 
| tail: VExp -> VExp 
| vlength: VExp -> VExp
| reverse: VExp -> VExp
| extractn: AExp -> VExp -> VExp. (*returneaza primele n elemente ale vectorului*)

Coercion vect: TipVector >-> VExp.
Coercion vvar: string >-> VExp.

(* Notatii vectori *)
Notation "A |+| B" := (vplus A B)(at level 50, left associativity).
(*
Definition plusV (v1 v2 : TipVector) : TipVector :=
  match v1, v2 with
    | error_vect, vector v2 => vector v2
    | vector v1, error_vect => vector v1
    | vector v1, vector v2 => elem (v1 ++ v2)
    end. *)

(* Sintaxa booleana *)

Inductive BExp :=
| berror
| btrue
| bfalse
| bvar: string -> BExp
| blt : AExp -> AExp -> BExp
| blte : AExp -> AExp -> BExp
| bgt : AExp -> AExp -> BExp
| bgte : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.
(*| bxor : BExp -> BExp -> BExp
| bnand : BExp -> BExp -> BExp
| bimply : BExp -> BExp -> BExp.
*)
(* Notatii pentru operatii boolene *)
Notation "A <' B" := (blt A B) (at level 70).
Notation "A <e' B" := (blte A B) (at level 70).
Notation "A >' B" := (bgt A B) (at level 70).
Notation "A >e' B" := (bgte A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Definition lt_TipBool (n1 n2 : TipNat) : TipBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | numar v1, numar v2 => boolean (Nat.ltb v1 v2)
    end.

Definition lte_TipBool (n1 n2 : TipNat) : TipBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | numar v1, numar v2 => boolean (Nat.leb v1 v2)
    end.

Definition gt_TipBool (n1 n2 : TipNat) : TipBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | numar v1, numar v2 => boolean (Nat.ltb v2 v1)
    end.

Definition gte_TipBool (n1 n2 : TipNat) : TipBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | numar v1, numar v2 => boolean (Nat.leb v2 v1)
    end.

Definition not_TipBool (n :TipBool) : TipBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_TipBool (n1 n2 : TipBool) : TipBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_TipBool (n1 n2 : TipBool) : TipBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

(* Semantica recursiva pentru operatii boolene *)

Fixpoint beval_r (a : BExp) (envnat : Env) : TipBool :=
  match a with
  | btrue => true
  | bfalse => false
  | berror => error_bool
  | bvar v => match (env v) with
               | rez_bool n => n
               | _ => error_bool
               end
  | blt a1 a2 => (lt_TipBool (aeval_r a1 envnat) (aeval_r a2 envnat))
  | blte a1 a2 => (lte_TipBool (aeval_r a1 envnat) (aeval_r a2 envnat))
  | bgt a1 a2 => (gt_TipBool (aeval_r a1 envnat) (aeval_r a2 envnat))
  | bgte a1 a2 => (gte_TipBool (aeval_r a1 envnat) (aeval_r a2 envnat))
  | bnot b1 => (not_TipBool (beval_r b1 envnat))
  | band b1 b2 => (and_TipBool (beval_r b1 envnat) (beval_r b2 envnat))
  | bor b1 b2 => (or_TipBool (beval_r b1 envnat) (beval_r b2 envnat))
  end.

(* Semantica Big-Step pentru operatii boolene *)

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> TipBool -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> error_bool
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | rez_bool x => x
                                                | _ => error_bool
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lt_TipBool i1 i2) ->
    a1 <' a2 ={ sigma }=> b
| b_lessorequalthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lte_TipBool i1 i2) ->
    a1 <e' a2 ={ sigma }=> b
| b_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (gt_TipBool i1 i2) ->
    a1 >' a2 ={ sigma }=> b
| b_greaterorequalthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (gte_TipBool i1 i2) ->
    a1 >e' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_TipBool i1) ->
    !'a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_TipBool i1 i2) ->
    (a1 &&' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_TipBool i1 i2) ->
    (a1 ||' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').

(* Because "n" is not declared *)
Example boolean_operation : bnot (100 <' "n") ={ env }=> error_bool.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply var.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Sintaxa pentru statements *)
Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt 
  | bool_decl: string -> BExp -> Stmt 
  | char_decl: string -> CExp -> Stmt     
  | nat_assign : string -> AExp -> Stmt
  | bool_assign : string -> BExp -> Stmt 
  | char_assign : string -> CExp -> Stmt 
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | skip : Stmt -> Stmt.
  (*| switch : BExp -> Stmt
  | break : Stmt.
  *)
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (char_assign X A)(at level 90).
Notation "'iNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'iBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "'iSir' X ::= A" := (char_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'daca' ( A ) 'atunci' { B }" := (ifthen A B) (at level 97).
Notation "'daca' ( A ) 'atunci' { B } 'altfel' { C }" := (ifthenelse A B C) (at level 97).
Notation " A '?' B ':' C " := (ifthenelse A B C) (at level 97).
Notation "'cat_timp' ( A ) { B }" := (while A B) (at level 97).
Notation "'pentru' ( A # B # C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'sari_peste' A " := (skip A) (at level 97).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

(* Semantica tip Big-Step pentru statements *)

Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (rez_nat i)) ->
   (x :n= a) -{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (rez_nat i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (update sigma x (rez_bool i)) ->
   (x :b= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (rez_bool i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_char_decl: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (update sigma x (rez_string i)) ->
   (x :s= a) -{ sigma }-> sigma'
| e_char_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (rez_string i)) ->
    (x :s= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

(* Semantica recursiva pentru statements *)

Fixpoint eval_r (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
    | 0 => env
    | S gas' => match s with
                | sequence S1 S2 => eval_r S2 (eval_r S1 env gas') gas'
                | nat_decl a aexp => update (update env a default) a (rez_nat (aeval_r aexp env))
                | bool_decl b bexp => update (update env b default) b (rez_bool (beval_r bexp env))
                | char_decl b cexp => update (update env c default) c (rez_string (ceval_r cexp env))
                | nat_assign a aexp => update env a (rez_nat (aeval_r aexp env))
                | bool_assign b bexp => update env b (rez_bool (beval_r bexp env))
                | char_assign c cexp => update env c (rez_string (ceval_r cexp env))
                | ifthen cond s' => 
                    match (beval_r cond env) with
                    | error_bool => env
                    | boolean v => match v with
                                 | true => eval_r s' env gas'
                                 | false => env
                                 end
                    end
                | ifthenelse cond S1 S2 => 
                    match (beval_r cond env) with
                        | error_bool => env
                        | boolean v  => match v with
                                 | true => eval_r S1 env gas'
                                 | false => eval_r S2 env gas'
                                 end
                         end
                | while cond s' => 
                    match (beval_r cond env) with
                        | error_bool => env
                        | boolean v => match v with
                                     | true => eval_r (s' ;; (while cond s')) env gas'
                                     | false => env
                                     end
                        end
                end
    end.


(*Exemple functionalitate*)

Definition while_stmt :=
    iNat "i" ::= 0 ;;
    iNat "sum" ::= 0 ;;
    cat_timp 
        ("i" <' 6) 
        {
           "sum" :n= "sum" +' "i" ;;
           "i" :n= "i" +' 1
        }
    .

Compute (eval_r while_stmt env 100) "sum".

Definition for_stmt :=
    iNat "sum" ::= 0 ;;
    pentru ( iNat "i" ::= 0 # "i" <e' 6 # "i" :n= "i" +' 1 ) {
      "sum" :n= "sum" +' "i"
    }.

Compute (eval_r for_stmt env 100) "sum".

