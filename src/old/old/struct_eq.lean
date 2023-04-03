/-
An example of why eq and heq for structures is not completely unreasonable.
-/

/-
We want equality of foo's to mean:
* equivalent predicates P, and
* functions f which agree on the subset defined by P.
-/
structure foo : Type :=
  (P : nat → Prop)
  (f : subtype P → bool)

lemma foo.congr_P (A B : foo) :
  (A = B) → forall (n : nat),
  A.P n ↔ B.P n :=
fun (h : A = B) n, eq.to_iff (congr_fun (congr_arg foo.P h) n)

lemma foo.congr_f (A B : foo) :
  (A = B) → forall (n : nat) (hA : A.P n) (hB : B.P n),
  A.f ⟨n, hA⟩ = B.f ⟨n, hB⟩ :=
fun (h : A = B) n hA hB,
  @eq.rec foo A
  (fun C, forall hC : C.P n, A.f ⟨n, hA⟩ = C.f ⟨n, hC⟩)
  (fun _, eq.refl (A.f ⟨n, hA⟩))
  B h hB

lemma foo.ext : forall (A B : foo),
  (forall (n : nat), A.P n ↔ B.P n) →
  (forall (n : nat) (hA : A.P n) (hB : B.P n), A.f ⟨n, hA⟩ = B.f ⟨n, hB⟩) →
  (A = B) :=
@foo.rec
(fun A, forall (B : foo),
  (forall (n : nat), A.P n ↔ B.P n) →
  (forall (n : nat) (hA : A.P n) (hB : B.P n), A.f ⟨n, hA⟩ = B.f ⟨n, hB⟩) →
  (A = B))
(fun A_P A_f, @foo.rec
  (fun B,
    (forall (n : nat), A_P n ↔ B.P n) →
    (forall (n : nat) (hA : A_P n) (hB : B.P n), A_f ⟨n, hA⟩ = B.f ⟨n, hB⟩) →
    (foo.mk A_P A_f = B))
  (fun B_P B_f,
    fun (hP_iff : forall (n : nat), A_P n ↔ B_P n),
    let hP_eq : A_P = B_P := funext (fun n, propext (hP_iff n)) in
    @eq.rec (nat → Prop) A_P
    (fun C_P, forall (C_f : subtype C_P → bool),
      (forall (n : nat) (hA : A_P n) (hC : C_P n), A_f ⟨n, hA⟩ = C_f ⟨n, hC⟩) →
      (foo.mk A_P A_f = foo.mk C_P C_f))
    (fun C_f,
      fun (hf_ext : forall (n : nat) (hA hC : A_P n), A_f ⟨n, hA⟩ = C_f ⟨n, hC⟩),
      let hf_eq : A_f = C_f := funext (@subtype.rec nat A_P (fun nhA, A_f nhA = C_f nhA) (fun n hA, hf_ext n hA hA)) in
      @eq.rec (subtype A_P → bool) A_f
      (fun f, foo.mk A_P A_f = foo.mk A_P f)
      (eq.refl (foo.mk A_P A_f))
      C_f hf_eq)
    B_P hP_eq B_f))
