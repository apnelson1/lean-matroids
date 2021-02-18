import prelim.collections prelim.size prelim.induction prelim.minmax
import .rankfun
import tactic data.setoid.partition

noncomputable theory 
open_locale classical 

open set 
namespace matroid 

variables {U : Type}[fintype U]

section parallel_nl 

/-- equivalence relation of being parallel for nonloops  -/
def parallel_nl (M : matroid U) (e f : nonloop M) : Prop := 
  M.r ({e,f}) = 1 

/-- relation of being both nonloops and having a rank-one union. Irreflexive at loops; 
    an equivalence relation when restricted to nonloops -/
def parallel (M : matroid U)(e f : U): Prop := 
  M.is_nonloop e ∧ M.is_nonloop f ∧ M.r {e,f} = 1 

lemma parallel_nl_of_parallel {M : matroid U}{e f : U}(h : M.parallel e f ):
  ∃ (he : M.is_nonloop e)(hf : M.is_nonloop f), M.parallel_nl ⟨e,he⟩ ⟨f,hf⟩ :=
⟨h.1,h.2.1,h.2.2⟩

lemma parallel_of_parallel_nl {M : matroid U}{e f : M.nonloop}(h : M.parallel_nl e f): 
  M.parallel e.1 f.1 :=
⟨e.2,f.2,h⟩

lemma parallel_iff_parallel_nl {M : matroid U}{e f : U}:
  M.parallel e f ↔ ∃ (he : M.is_nonloop e)(hf : M.is_nonloop f), M.parallel_nl ⟨e,he⟩ ⟨f,hf⟩:= 
by tidy

/-- parallel_nl in dual -/
def series (M : matroid U) (e f : nonloop (dual M)): Prop := 
  (dual M).parallel_nl e f 

lemma parallel_nl_refl (M : matroid U): 
  reflexive M.parallel_nl:= 
λ e, by {unfold parallel_nl, rw pair_eq_singleton, exact e.property}

lemma parallel_nl_symm (M : matroid U) : 
  symmetric M.parallel_nl:= 
λ x y, by {simp_rw [parallel_nl, pair_comm], tauto,}

lemma parallel_nl_iff_dep {M: matroid U}{e f : nonloop M} : 
  M.parallel_nl e f ↔ (e = f ∨ M.is_dep {e,f}) :=
begin
  unfold parallel_nl, rw dep_iff_r,  refine ⟨λ h, ((or_iff_not_imp_left.mpr (λ hne, _))), λ h, _ ⟩,
  have := size_union_distinct_singles (λ h', hne (subtype.ext h')) , 
  rw h, unfold_coes at *, linarith,  
  cases h, rw [h, pair_eq_singleton], exact f.property, 
  have := rank_two_nonloops_lb e f, 
  have := size_union_singles_ub e.1 f.1,
  unfold_coes at *, rw ←int.le_sub_one_iff at h, linarith, 
end

lemma parallel_nl_iff_cct {M: matroid U}{e f : nonloop M} : 
  M.parallel_nl e f ↔ (e = f ∨ M.is_circuit {e,f}) :=
begin
  refine ⟨λ h, _, λ h, (parallel_nl_iff_dep.mpr (or.imp_right _ h : (e = f) ∨ is_dep M ({e,f})))⟩, 
  replace h := parallel_nl_iff_dep.mp h, cases h, exact or.inl h, apply or_iff_not_imp_left.mpr, intro h', 
  refine ⟨h,λ Y hY, _⟩, rcases ssubset_pair hY, 
  rw h_1, exact empty_indep M,  unfold_coes at h_1,  cases h_1; 
  {rw h_1, apply coe_nonloop_indep,},
  apply circuit_dep, 
end

lemma parallel_nl_trans (M : matroid U) :
  transitive M.parallel_nl :=
begin
  intros e f g hef hfg, unfold parallel_nl at *, 
  have := M.rank_submod ({e,f}) ({f,g}), rw [hef, hfg] at this, 
  have h1 : 1 ≤ M.r (({e,f}) ∩ ({f,g})),  
  {rw ←rank_coe_nonloop f, refine M.rank_mono (subset_inter _ _ ); simp, },
  have h2 := M.rank_mono (_ : ({e,g} : set U)  ⊆ {e,f} ∪ {f,g}), swap, 
  {intro x, simp, tauto,  }, 
  linarith [(rank_two_nonloops_lb e g)],  
end

lemma parallel_refl_nonloop (M : matroid U){e : U}(h : M.is_nonloop e): 
  M.parallel e e :=
⟨h,h,by rwa [pair_eq_singleton]⟩

lemma parallel_trans (M : matroid U): 
  transitive M.parallel :=
begin
  rintros e f g ⟨he,hf,hef⟩ ⟨-,hg,hfg⟩,-- unfold parallel at *, 
  refine ⟨he,hg,_⟩, 
  have hef' : M.parallel_nl ⟨e,he⟩ ⟨f,hf⟩:= hef, 
  have hfg' : M.parallel_nl ⟨f,hf⟩ ⟨g,hg⟩ := hfg, 
  exact parallel_nl_trans M hef' hfg', 
end

lemma parallel_symm (M : matroid U): 
  symmetric M.parallel :=
by {rintros e f ⟨he,hf,hef⟩, refine ⟨hf,he,_⟩, rwa pair_comm}

@[symm] lemma parallel_symm' {M : matroid U}{e f : U}(hef : M.parallel e f):
  M.parallel f e := 
parallel_symm M hef

lemma parallel_symm_iff {M : matroid U}{e f : U}:
  M.parallel e f ↔ M.parallel f e :=
⟨λ h, by {symmetry, exact h}, λ h, by {symmetry, exact h}⟩

@[trans] lemma parallel_trans' {M : matroid U}{e f g : U}(hef : M.parallel e f)(hfg : M.parallel f g): 
  M.parallel e g := 
parallel_trans M hef hfg

lemma parallel_nl_is_equivalence (M : matroid U) : 
  equivalence M.parallel_nl := 
  ⟨M.parallel_nl_refl, M.parallel_nl_symm, M.parallel_nl_trans⟩

lemma series_is_equivalence (M : matroid U): 
  equivalence M.series :=
parallel_nl_is_equivalence M.dual 

/-- the parallel class containing e -/
def parallel_cl (M : matroid U)(e : U) := 
  {a : U | M.parallel a e}

lemma mem_parallel_cl {M : matroid U}{e f : U}: 
  e ∈ M.parallel_cl f ↔ M.parallel e f := 
by simp_rw [parallel_cl, mem_set_of_eq]

def is_parallel_class (M : matroid U)(P : set U)  := 
  ∃ e,  M.is_nonloop e ∧ P = M.parallel_cl e 

def parallel_class (M : matroid U): Type := {X : set U // M.is_parallel_class X}

instance coe_parallel_class_to_set {M : matroid U}: has_coe (M.parallel_class) (set U) := ⟨subtype.val⟩ 
instance parallel_class_fintype {M : matroid U}: fintype M.parallel_class := by {unfold parallel_class, apply_instance} 

lemma nonloop_of_mem_parallel_class {M : matroid U}{P : set U}{e : U}(heP : e ∈ P)(h : M.is_parallel_class P) :
  M.is_nonloop e := 
by {rcases h with ⟨f, ⟨hf,rfl⟩⟩, rw mem_parallel_cl at heP, exact heP.1} 

lemma parallel_cl_eq_cl_minus_loops (M : matroid U)(e : U): 
  M.parallel_cl e = M.cl {e} \ M.loops :=
begin
  by_cases he: M.is_nonloop e, swap, 
  { ext x, rw [mem_diff, mem_parallel_cl],
    refine ⟨λ h, false.elim (he h.2.1), λ h, false.elim _⟩,
    rw [←loop_iff_not_nonloop, loop_iff_r] at he, 
    rw [mem_cl_iff_r,he, ←nonloop_iff_not_elem_loops, nonloop_iff_r] at h,
    linarith[h.1, h.2, M.rank_mono_union_right {e} {x}], },
  ext x, 
  simp only [mem_diff, mem_set_of_eq, mem_cl_iff_r, rank_nonloop he, union_singleton, ←nonloop_iff_not_elem_loops], 
  split, { rintros ⟨hx,he,hxe⟩, split; assumption,  }, 
  rintros ⟨hxe,hx⟩, exact ⟨hx,he,hxe⟩, 
end

lemma parallel_class_eq_cl_nonloop_diff_loops {M : matroid U}{P : set U}: 
  M.is_parallel_class P ↔ (nonempty P) ∧ (∀ e ∈ P, P = M.cl {e} \ M.loops ):= 
begin
  simp_rw [←parallel_cl_eq_cl_minus_loops, is_parallel_class],  
  split,
  { rintros ⟨e,he,rfl⟩, refine ⟨nonempty.intro ⟨e,_⟩, _⟩, apply parallel_refl_nonloop, assumption, 
    intros f hf, ext x, simp only [mem_parallel_cl] at *, have := parallel_symm' hf, 
    split; {intro h, transitivity; assumption}, },
  rintros ⟨⟨⟨e,he⟩⟩,hP⟩, 
  specialize hP e he, rw [hP, mem_parallel_cl] at he, 
  exact ⟨e, he.1, hP⟩, 
end

lemma parallel_class_is_cl_diff_loops {M : matroid U}(P : M.parallel_class): 
  ∃ e ∈ (P : set U), M.is_nonloop e ∧ (P : set U) = M.cl {e} \ M.loops :=
begin
  rcases parallel_class_eq_cl_nonloop_diff_loops.mp P.property with ⟨⟨⟨e,he⟩⟩,hP⟩, 
  exact ⟨e,he,nonloop_of_mem_parallel_class he P.property, hP e he⟩, 
end

lemma parallel_class_is_parallel_cl {M : matroid U}(P : M.parallel_class):
  ∃ e ∈ (P : set U), M.is_nonloop e ∧ (P : set U) = M.parallel_cl e :=
by {have := parallel_class_is_cl_diff_loops P, simp_rw ←parallel_cl_eq_cl_minus_loops at this, assumption}

lemma parallel_class_eq_of_nonempty_inter {M : matroid U}{P₁ P₂ : M.parallel_class}(h : set.nonempty (P₁ ∩ P₂ : set U)): 
  P₁ = P₂ :=
begin
  rcases h with ⟨x,hx⟩, 
  rcases parallel_class_is_parallel_cl P₁ with ⟨e₁,he₁P,⟨he₁,h₁⟩⟩,  
  rcases parallel_class_is_parallel_cl P₂ with ⟨e₂,he₂P,⟨he₂,h₂⟩⟩,  
  
  rw [mem_inter_iff, h₁,h₂] at hx, 
  have h₁₂ : M.parallel e₁ e₂, {transitivity x, symmetry, exact hx.1, exact hx.2},
  have h₂₁ := parallel_symm' h₁₂, 
  rcases P₁ with ⟨P₁, hP₁⟩, rcases P₂ with ⟨P₂, hP₂⟩, rw subtype.mk_eq_mk, 
  rw subtype.coe_mk at *, subst h₁, subst h₂, 
  ext y, simp only [mem_parallel_cl],
  split; {intro h, symmetry, transitivity, assumption, symmetry, assumption,}, 
end


  
  
  -- P = { a : U | ∃ (h : M.is_nonloop a), ⟦(⟨a,h⟩ : M.nonloop)⟧ = ⟦e⟧ }



/-
instance parallel_nl_class_fin (M : matroid U) : fintype M.parallel_nl_class := 
by {unfold parallel_nl_class, apply_instance  }


lemma parallel_nl_class_has_rep {M : matroid U}(P : M.parallel_nl_class): 
  ∃ (e : nonloop M), ⟦e⟧ = P :=
quotient.exists_rep P 

/- a parallel_nl class of M, viewed as a set U -/
def as_set {M : matroid U}(C : M.parallel_nl_class) : set U := 
  λ a, (∃ (h : M.is_nonloop a), ⟦(⟨a,h⟩ : M.nonloop)⟧ = C)


instance coe_parallel_nl_class_to_set {M : matroid U}: has_coe (M.parallel_nl_class) (set U) := ⟨@as_set _ _ M⟩ 

instance coe_parallel_nl_quot_to_set {M : matroid U}: 
  has_coe (@quotient M.nonloop (@matroid.parallel_nl_setoid _ _ M)) (set U) := ⟨@as_set _ _ M⟩ 

def as_set_mem_iff {M : matroid U}{a b : M.nonloop}: 
  ↑b ∈ (⟦a⟧ : set U) ↔ a ≈ b := 
by {unfold_coes, simp only [as_set, quotient.eq, subtype.val_eq_coe], tidy}

def as_set_mem_iff' {M : matroid U}{a : M.nonloop}{b : U}: 
  b ∈ (⟦a⟧ : set U) ↔ ∃ (h : M.is_nonloop b), a ≈ ⟨b,h⟩ := 
by {unfold_coes, simp only [as_set, quotient.eq, subtype.val_eq_coe], tidy}
  
lemma as_set_inj {M : matroid U} {P P' : M.parallel_nl_class} (h : (P : set U) = (P' : set U)):
  P = P' := 
begin 
  rw ext_iff at h, 
  rcases quotient.exists_rep P with ⟨⟨a,ha⟩,rfl⟩,
  rcases (h a).mp ⟨ha,rfl⟩ with ⟨h',h''⟩, 
  rw ←h'', 
end

lemma parallel_iff {M : matroid U}{e f : U}: 
  M.parallel e f ↔ ∃ (P : M.parallel_nl_class), e ∈ (P : set U) ∧ f ∈ (P : set U) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨he,hf, hef⟩ := h, 
    use ⟦⟨e,he⟩⟧, 
    rw [as_set_mem_iff', as_set_mem_iff'],  
    refine ⟨⟨he, quotient.eq.mp rfl⟩, ⟨hf,hef⟩⟩},
  rcases h with ⟨P,he,hf⟩, 
  rcases P.exists_rep with ⟨a,rfl⟩, 
  rw as_set_mem_iff' at *, 
  rcases he with ⟨he, hae⟩, rcases hf with ⟨hf, haf⟩, 
  exact ⟨he,hf,setoid.trans (setoid.symm hae) haf,⟩, 
end 

def parallel_nl_class_of {M : matroid U}{e : U}(he : M.is_nonloop e) : set U := 
  ⟦@id M.nonloop ⟨e,he⟩⟧

lemma cl_nonloop_eq_parallel_nl_class_and_loops {M : matroid U}(e : M.nonloop) : 
  M.cl {(e : U)} = ⟦e⟧ ∪ M.loops := 
begin
  rcases e with ⟨e,he⟩,  dsimp only [subtype.coe_mk], ext, 
  rw [mem_cl_iff_r, mem_union, union_singletons_eq_pair, as_set_mem_iff', 
    rank_nonloop he, ←loop_iff_mem_loops], 
  refine ⟨λ h, _, λ h, _⟩,
  { by_cases hx : M.is_nonloop x, left, exact ⟨hx,h⟩,
    right, rwa [loop_iff_not_nonloop],  },
  rcases h with (⟨he, hpara⟩ | hl), exact hpara, 
  rwa [←union_singletons_eq_pair, rank_eq_rank_insert_loop _ hl], 
end

lemma point_iff_loops_and_parallel_nl_class {M : matroid U}{P : set U}:
  M.is_point P ↔ ∃ P₀ : M.parallel_nl_class, P = P₀ ∪ M.loops :=
begin
  rw [point_iff_cl_nonloop], 
  refine ⟨λ h, _, λ h, _⟩, 
  { rcases h with ⟨e,he,rfl⟩,  
    exact ⟨⟦⟨e,he⟩⟧, by rw [←cl_nonloop_eq_parallel_nl_class_and_loops, subtype.coe_mk]⟩}, 
  rcases h with ⟨P₀, rfl⟩, rcases parallel_nl_class_has_rep P₀ with ⟨⟨e,he⟩,rfl⟩,
  exact ⟨e,he, by {rw [←cl_nonloop_eq_parallel_nl_class_and_loops, subtype.coe_mk] }⟩,  
end

-/
end parallel_nl 

section simple 

def is_loopless (M : matroid U) := 
  ∀ X, size X ≤ 1 → M.is_indep X 

def is_simple (M : matroid U) :=
  ∀ X, size X ≤ 2 → M.is_indep X 

lemma loopless_iff_all_nonloops {M : matroid U} :
  M.is_loopless ↔ ∀ e, M.is_nonloop e :=
begin
  simp_rw [nonloop_iff_r, is_loopless, size_le_one_iff_empty_or_singleton, indep_iff_r],
  refine ⟨λ h, λ e, _, λ h, λ X hX, _⟩, 
  { rw ←size_singleton e, apply h, right, exact ⟨e,rfl⟩},
  rcases hX with (rfl | ⟨e,rfl⟩), simp, 
  rw [size_singleton, h e], 
end 

lemma simple_iff_no_loops_or_parallel_nl_pairs {M : matroid U}:
  M.is_simple ↔ (∀ e, M.is_nonloop e) ∧ ∀ (e f : nonloop M), M.parallel_nl e f → e = f :=
begin
  refine ⟨λ h, ⟨λ e, _, λ e f hef, _⟩,  λ h, λ X hX, _⟩, 
  
  { rw nonloop_iff_indep, apply h, rw size_singleton, norm_num}, 
  { rw [parallel_nl] at hef, 
    suffices : (e : U) = (f : U), cases e, cases f, simpa, 
    by_contra hn,
    have := h {coe e, coe f} (by rw size_union_distinct_singles hn),  
    rw [indep_iff_r, hef, size_union_distinct_singles hn] at this, 
    norm_num at this, },
  
  rcases int.nonneg_le_two_iff (size_nonneg X) hX with (h0 | h1 | h2), 
  { rw size_zero_iff_empty at h0, rw h0, apply M.I1, },
  { rcases size_one_iff_eq_singleton.mp h1 with ⟨e,rfl⟩, rw ←nonloop_iff_indep, apply h.1, },
  rcases size_eq_two_iff_pair.mp h2 with ⟨e,f,hef,rfl⟩,
  rw [eq_nonloop_coe (h.1 e), eq_nonloop_coe (h.1 f)], 
  
  rw [indep_iff_not_dep], by_contra hn, push_neg at hn, 
  have h' := h.2 ⟨e, h.1 e⟩ ⟨f, h.1 f⟩, rw parallel_nl_iff_dep at h',
  specialize h' (or.intro_right _ hn), rw [subtype.mk_eq_mk] at h',   
  exact hef h', 
end

lemma intersecting_parallel_nl_classes_eq {M : matroid U}(S : set M.parallel_nl_class) : set U :=

def union_parallel_nl_classes {M : matroid U}(S : set M.parallel_nl_class): set U := 
  set.Union (λ (P : S), (P : set U))


/- these next two lemmas are likely isomorphic to something in mathlib -/
lemma union_union_parallel_nl_classes {M : matroid U}(S₁ S₂ : set M.parallel_nl_class): 
  union_parallel_nl_classes (S₁ ∪ S₂) = union_parallel_nl_classes S₁ ∪ union_parallel_nl_classes S₂ :=
begin
  unfold union_parallel_nl_classes, ext x, 
  rw mem_union, repeat {rw mem_Union}, 
  refine ⟨λ h, _, λ h, _⟩, 
  { rcases h with ⟨⟨i,hi⟩, hix⟩, 
    rw mem_union at hi, 
    rcases hi with (h₁ | h₂), left, use ⟨i,h₁⟩, exact hix, 
    right, use ⟨i,h₂⟩, exact hix,  },    
  rcases h with (⟨⟨i,hi⟩,h⟩|⟨⟨i,hi⟩,h⟩); {refine ⟨⟨i,_⟩, h⟩, rw mem_union, tauto}, 
end

lemma inter_union_parallel_nl_classes {M : matroid U}(S₁ S₂ : set M.parallel_nl_class): 
  union_parallel_nl_classes (S₁ ∩ S₂) = union_parallel_nl_classes S₁ ∩ union_parallel_nl_classes S₂ :=
begin
  unfold union_parallel_nl_classes, ext x, 
  rw mem_inter_iff, repeat {rw mem_Union}, 
  split, 
  { rintros ⟨⟨i,hi⟩, hix⟩, 
    exact ⟨⟨⟨i,mem_of_mem_inter_left hi⟩,hix⟩,⟨⟨i,mem_of_mem_inter_right hi⟩,hix⟩⟩},
  rintros ⟨⟨⟨i₁,hi₁⟩,hi₁x⟩,⟨⟨i₂,hi₂⟩,hi₂x⟩⟩, 
  refine ⟨⟨i₁, _⟩, hi₁x⟩, 

end

def si (M : matroid U): matroid (M.parallel_nl_class) := 
{ r := λ X, M.r (set.Union (λ (P : X), (P : set U))),
  R0 := λ X, by {apply M.R0 },
  R1 := λ X, by {},
  R2 := _,
  R3 := _ }


end simple 
end matroid 

