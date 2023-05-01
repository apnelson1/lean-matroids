import .rank
import ..mathlib.finsum_ncard

noncomputable theory
open_locale classical
open_locale big_operators

open set
namespace matroid

variables {E E' : Type*} {N M : matroid E} {e f g : E} {X Y Z S T : set E}

section simple

/-- A matroid is loopless on a set if that set doesn't contain a loop. -/
def loopless_on (M : matroid E) (X : set E) : Prop := ∀ ⦃e⦄, e ∈ X → M.nonloop e

/-- A matroid is loopless if it has no loop -/
def loopless (M : matroid E) : Prop := ∀ e, M.nonloop e

protected lemma loopless.loopless_on (hM : M.loopless) : M.loopless_on X := λ e _, hM _

@[simp] lemma loopless_on_univ : M.loopless_on univ ↔ M.loopless := by simp [loopless_on, loopless]

lemma loopless_on.subset (h : M.loopless_on Y) (hXY : X ⊆ Y) : M.loopless_on X :=
subset_trans hXY h

lemma loopless_on.indep_of_mem (h : M.loopless_on X) (he : e ∈ X) : M.indep {e} :=
indep_singleton.2 $ h he

def loopless.nonloop (hM : M.loopless) (e : E) : M.nonloop e := hM e

lemma loopless.loops (hM : M.loopless) : M.cl ∅ = ∅ := eq_empty_iff_forall_not_mem.mpr hM

lemma loopless_iff_loops_eq_empty : M.loopless ↔ M.cl ∅ = ∅ :=
⟨loopless.loops, λ h e he, not_mem_empty e (by rwa ←h)⟩
  
/-- the property of a set containing no loops or para pairs -/
def simple_on (M : matroid E) (X : set E) : Prop := ∀ ⦃e⦄, e ∈ X → ∀ ⦃f⦄, f ∈ X → M.indep {e, f}

/-- the property of a matroid having no loops or para pairs -/
def simple (M : matroid E) : Prop := ∀ e f, M.indep {e, f}

protected lemma simple.simple_on (hM : M.simple) : M.simple_on X := λ e _ f _, hM e f

@[simp] lemma simple_on_univ : M.simple_on univ ↔ M.simple := by simp [simple_on, simple]

lemma simple_on.subset (h : M.simple_on Y) (hXY : X ⊆ Y) : M.simple_on X :=
λ e he f hf, h (hXY he) (hXY hf)

protected lemma simple_on.loopless_on (h : M.simple_on X) : M.loopless_on X :=
begin
  intros x hx,
  rw [←indep_singleton , ←pair_eq_singleton],
  exact h hx hx,
end

protected lemma simple.loopless (h : M.simple) : M.loopless :=
loopless_on_univ.1 h.simple_on.loopless_on

lemma simple.nonloop (h : M.simple) (e : E) : M.nonloop e := h.loopless e 

lemma simple_on.indep_of_card_le_two_of_finite (h : M.simple_on X) 
(hX : X.ncard ≤ 2) (hXfin : X.finite) :
  M.indep X :=
begin
  obtain (h2 | hlt2) := eq_or_lt_of_le hX,
  { obtain ⟨x,y,-,rfl⟩ := ncard_eq_two.mp h2,
    exact h (mem_insert _ _) (mem_insert_of_mem _ $ mem_singleton _) },
  obtain (h1 | hlt1) := eq_or_lt_of_le (nat.lt_succ_iff.mp hlt2),
  { obtain ⟨a,rfl⟩ := ncard_eq_one.mp h1,
    rw indep_singleton,
    exact h.loopless_on (mem_singleton _) },
  convert M.empty_indep,
  rwa [nat.lt_add_one_iff, le_zero_iff, ncard_eq_zero hXfin] at hlt1, 
end

lemma simple_on.indep_of_card_le_two [finite E] (h : M.simple_on X) (hX : X.ncard ≤ 2) : 
  M.indep X := 
h.indep_of_card_le_two_of_finite hX (to_finite _) 

lemma simple_on.eq_of_r_pair_eq_one (h : M.simple_on X) (he : e ∈ X) (hf : f ∈ X)
  (hef : M.r {e, f} = 1) :
  e = f :=
begin
  rw [(h he hf).r] at hef,
  exact ncard_le_one_iff.mp hef.le (by simp) (by simp),
end

end simple

section parallel 

/-- Two nonloops are parallel if they have the same closure -/
def para (M : matroid E) (e f : E) : Prop := M.nonloop e ∧ M.cl {e} = M.cl {f}

lemma para.cl_eq_cl (h : M.para e f) : M.cl {e} = M.cl {f} := h.2 

lemma para.nonloop_left (h : M.para e f) : M.nonloop e := h.1 

lemma para.nonloop_right (h : M.para e f) : M.nonloop f := 
h.nonloop_left.nonloop_of_mem_cl (h.cl_eq_cl.subset (mem_cl_self _ _))

lemma nonloop.para_self (he : M.nonloop e) : M.para e e := ⟨he,rfl⟩ 

lemma nonloop.nonloop_para_iff_mem_cl (he : M.nonloop e) (hf : M.nonloop f) : 
  M.para e f ↔ f ∈ M.cl {e} := 
⟨λ h, h.cl_eq_cl.symm.subset (mem_cl_self _ _), λ h, ⟨he, (hf.cl_eq_of_mem_cl h).symm⟩⟩

lemma nonloop.para_of_nonloop_mem_cl (he : M.nonloop e) (hf : M.nonloop f) (h : f ∈ M.cl {e}) : 
  M.para e f :=
(he.nonloop_para_iff_mem_cl hf).mpr h 

lemma para.symm (h : M.para e f) : M.para f e := ⟨h.nonloop_right, h.2.symm⟩ 

lemma para.comm : M.para e f ↔ M.para f e := ⟨para.symm, para.symm⟩ 

lemma para.trans (hef : M.para e f) (hfg : M.para f g) : M.para e g := ⟨hef.1, hef.2.trans hfg.2⟩ 

lemma loop.not_para (he : M.loop e) (f : E) : ¬ M.para e f := λ h, h.nonloop_left he 

lemma para_self_iff_nonloop : M.para e e ↔ M.nonloop e := ⟨para.nonloop_left, nonloop.para_self⟩  

lemma para.indep_iff_eq (hef : M.para e f) : M.indep {e,f} ↔ e = f :=
begin
  refine ⟨λ h, by_contra (λ hne, _), λ h, _⟩,
  { have h' := hef.nonloop_left.indep.mem_cl_iff_of_not_mem (ne.symm hne), 
    rw [iff_not_comm, pair_comm] at h', 
    rw [h', hef.cl_eq_cl] at h, 
    exact h (mem_cl_self _ _) },
  subst h, 
  rw [pair_eq_singleton], 
  exact hef.nonloop_left.indep, 
end 

lemma nonloop.para_iff_dep_of_ne (he : M.nonloop e) (hf : M.nonloop f) (hef : e ≠ f) :
  M.para e f ↔ ¬M.indep {e,f} :=
begin
  refine ⟨λ h h', hef (h.indep_iff_eq.mp h'), λ h, he.para_of_nonloop_mem_cl hf _⟩,
  rw [he.indep.mem_cl_iff, pair_comm], 
  exact false.elim ∘ h,   
end  

lemma simple.eq_of_para (h : M.simple) (hef : M.para e f) : e = f := hef.indep_iff_eq.mp (h e f)

lemma simple.para_iff_eq (h : M.simple) : M.para e f ↔ e = f := 
⟨h.eq_of_para, by { rintro rfl, exact (h.nonloop e).para_self }⟩ 

lemma simple_iff_para_iff_eq_forall : M.simple ↔ ∀ e f, (M.para e f ↔ e = f) :=
begin
  refine ⟨λ h e f, h.para_iff_eq, λ h e f, _⟩,
  have he : M.nonloop e, from λ hl, mt (h e e).mpr (hl.not_para _) rfl , 
  have hf : M.nonloop f, from λ hl, mt (h f f).mpr (hl.not_para _) rfl , 
  obtain (rfl | hef) :=  eq_or_ne e f, 
  { rwa [pair_eq_singleton, indep_singleton] },
  exact not_not.mp (by rwa [←he.para_iff_dep_of_ne hf hef, h]),  
end 

/-- Being parallel is a partial equivalence relation (irreflexive on precisely the loops) -/
instance (M : matroid E) : is_per E M.para := 
{ symm  := λ _ _, para.symm,
  trans :=  λ _ _ _, para.trans }

/-- The set of elements parallel to `e` -/
def pcl (M : matroid E) (e : E) := {f | M.para e f}

@[simp] lemma mem_pcl_iff : e ∈ M.pcl f ↔ M.para e f := para.comm

lemma nonloop.mem_pcl_self (he : M.nonloop e) : e ∈ M.pcl e := he.para_self 

lemma loop.pcl_eq_empty (he : M.loop e) : M.pcl e = ∅ :=  
eq_empty_of_forall_not_mem (λ f, he.not_para _)

lemma loop.not_mem_pcl (he : M.loop e) (f : E) : e ∉ M.pcl f := 
λ hef, he.not_para _ (mem_pcl_iff.mpr hef) 

lemma pcl_eq_cl_diff_loops (M : matroid E) (e : E) : M.pcl e = M.cl {e} \ M.cl ∅ :=
begin
  refine (M.loop_or_nonloop e).elim (λ he, by rw [he.pcl_eq_empty, he.cl, diff_self]) (λ he, _), 
  refine set.ext (λ f, (M.loop_or_nonloop f).elim (λ hf, _) (λ hf, _)), 
  { rw [mem_pcl_iff, ←hf.cl], 
    exact iff_of_false (hf.not_para _) (λ h, h.2 (mem_cl_self _ _)) },
  rw [pcl, mem_set_of, he.nonloop_para_iff_mem_cl hf, mem_diff, ←loop_iff_mem_cl_empty, 
    not_loop_iff, iff_true_intro hf, and_true],   
end 

lemma loopless.pcl_eq_cl (h : M.loopless) (e : E) : M.pcl e = M.cl {e} := 
by rw [pcl_eq_cl_diff_loops, h.loops, diff_empty]

lemma nonloop.point_of_pcl_union_loops (he : M.nonloop e) : M.point (M.pcl e ∪ M.cl ∅) :=
begin
  rw [pcl_eq_cl_diff_loops, diff_union_self, 
    union_eq_self_of_subset_right (M.cl_subset (empty_subset _))], 
  exact he.cl_point, 
end 

lemma loopless.point_of_pcl (h : M.loopless) (e : E) : M.point (M.pcl e) := 
begin
  convert (h.nonloop e).point_of_pcl_union_loops, 
  rw [h.loops, union_empty], 
end 

lemma para.pcl_eq_pcl (h : M.para e f) : M.pcl e = M.pcl f :=
begin
  simp_rw [set.ext_iff, mem_pcl_iff], 
  exact λ x, ⟨λ hxe, hxe.trans h, λ hxf, hxf.trans h.symm⟩, 
end 

lemma nonloop.para_iff_pcl_eq_pcl (he : M.nonloop e) : M.para e f ↔ M.pcl e = M.pcl f :=
⟨para.pcl_eq_pcl, λ h, para.symm (h.subset (he.mem_pcl_self))⟩

lemma simple.pcl_eq_singleton (h : M.simple) (e : E) : M.pcl e = {e} :=
eq_singleton_iff_unique_mem.mpr 
  ⟨(h.nonloop e).mem_pcl_self, λ f hf, h.eq_of_para (mem_pcl_iff.mpr hf)⟩

lemma simple.cl_eq_singleton (h : M.simple) (e : E) : M.cl {e} = {e} :=
by rw [←h.pcl_eq_singleton, pcl_eq_cl_diff_loops, h.loopless.loops, diff_empty, cl_cl]

lemma simple_iff_forall_pcl_eq_self : M.simple ↔ ∀ e, M.pcl e = {e} :=
begin
  refine ⟨simple.pcl_eq_singleton, λ h, simple_iff_para_iff_eq_forall.mpr (λ e f, _)⟩,   
  rw [nonloop.para_iff_pcl_eq_pcl, h, h, singleton_eq_singleton_iff], 
  refine λ hl, _, 
  have h' := hl.pcl_eq_empty, 
  rw h e at h', 
  exact singleton_ne_empty _ h', 
end 

lemma simple.singleton_point (hM : M.simple) (e : E) : M.point {e} :=
begin
  convert hM.loopless.point_of_pcl e,
  rw [hM.pcl_eq_singleton], 
end 

/-- In a `simple` matroid, points are equivalent to elements. -/
noncomputable def simple.elem_point_equiv (h : M.simple) : E ≃ {P // M.point P} := 
{ to_fun := λ e, 
    ⟨{e}, by { rw [←h.cl_eq_singleton], exact (h.nonloop e).cl_point }⟩,
  inv_fun := λ P, P.2.nonempty.some,
  left_inv := λ e, mem_singleton_iff.mp (nonempty.some_mem _), 
  right_inv := 
  begin
    rintro ⟨P, hP⟩, 
    obtain ⟨e, he, rfl⟩ := hP.exists_eq_cl_nonloop, 
    simp only [h.loopless.pcl_eq_cl],
    simp_rw [h.cl_eq_singleton, singleton_eq_singleton_iff, ←mem_singleton_iff ],
    exact nonempty.some_mem _, 
  end }

@[simp] lemma simple.elem_point_equiv_apply_coe (h : M.simple) (e : E) : 
  (h.elem_point_equiv e : set E) = {e} := rfl 

@[simp] lemma simple.elem_point_equiv_apply_symm (h : M.simple) (P : {P // M.point P}) : 
  {h.elem_point_equiv.symm P} = (P : set E) := 
begin
  obtain ⟨P, hP⟩ := P, 
  obtain ⟨e, he, rfl⟩ := hP.exists_eq_cl_nonloop, 
  simp_rw [h.cl_eq_singleton, simple.elem_point_equiv, subtype.val_eq_coe, subtype.coe_mk, 
    equiv.coe_fn_symm_mk, singleton_eq_singleton_iff, ←mem_singleton_iff], 
  apply nonempty.some_mem, 
end 

lemma simple.elem_point_equiv_apply_symm_mem (h : M.simple) (P : {P // M.point P}) : 
  h.elem_point_equiv.symm P ∈ (P : set E) := 
by simp [←singleton_subset_iff]

lemma pcl_pairwise_disjoint (M : matroid E) : pairwise_disjoint (range M.pcl) id := 
begin
  rw [pairwise_disjoint, set.pairwise], 
  simp only [mem_range, ne.def, function.on_fun_apply, id.def, 
    forall_exists_index, forall_apply_eq_imp_iff', disjoint_iff_forall_ne, mem_pcl_iff], 
  rintro e f hef x hex _ hey rfl, 
  rw ←hex.nonloop_right.para_iff_pcl_eq_pcl at hef, 
  exact hef (hex.symm.trans hey), 
end 

lemma sum_ncard_point_diff_loops [finite E] (M : matroid E) : 
  ∑ᶠ (P : {P // M.point P}), ((P : set E) \ M.cl ∅).ncard = (M.cl ∅)ᶜ.ncard :=
begin
  convert @finsum_subtype_eq_finsum_cond _ _ _ (λ P, (P \ M.cl ∅).ncard) M.point, 
  convert @ncard_eq_finsum_fiber _ _ (M.cl ∅)ᶜ (to_finite _) (λ e, M.cl {e}), 
  ext P,
  rw [finsum_eq_if], 
  split_ifs, 
  {  congr, ext e,  
    simp_rw [mem_diff, mem_inter_iff, mem_compl_iff, mem_preimage, mem_singleton_iff, and_comm, 
      and.congr_left_iff], 
    intro he, 
    rw [h.eq_cl_singleton_iff, nonloop_iff_not_mem_cl_empty, and_iff_left he] },
  rw [eq_comm, ncard_eq_zero, ←disjoint_iff_inter_eq_empty, disjoint_compl_left_iff_subset], 
  rintro e (rfl : M.cl {e} = P), 
  rw [←loop, ←not_nonloop_iff], 
  exact mt nonloop.cl_point h, 
end 

lemma loopless.sum_ncard_point [finite E] (h : M.loopless) : 
  ∑ᶠ (P : {P // M.point P}), (P : set E).ncard = (univ : set E).ncard :=
begin
  rw [←@diff_empty _ univ, ←h.loops, ←compl_eq_univ_diff, ←sum_ncard_point_diff_loops], 
  apply finsum_congr (λ P, _), 
  rw [h.loops, diff_empty], 
end 

end parallel

section point_count

def num_points (M : matroid E) := nat.card {P // M.point P}

lemma simple_iff_num_points_eq_card [finite E] (hnl : ¬M.base ∅) : 
  M.simple ↔ M.num_points = ncard (univ : set E) := 
begin
  rw num_points, 
  refine ⟨λ h, _, λ h, _⟩,
  { rw [ncard_univ ],
    exact nat.card_eq_of_bijective _ h.elem_point_equiv.symm.bijective },
  simp_rw [simple_iff_forall_pcl_eq_self, pcl_eq_cl_diff_loops],  
  rw [←finsum_one, ←union_compl_self (M.cl ∅), ncard_union_eq, 
    ←sum_ncard_point_diff_loops] at h,  swap , exact disjoint_compl_right,

  have hleP : ∀ P : {P // M.point P}, 1 ≤ ((P : set E) \ M.cl ∅).ncard, 
  { rintro ⟨P, hP⟩, 
    rw [nat.succ_le_iff, ncard_pos, subtype.coe_mk],
    exact hP.diff_loops_nonempty } ,
  
  have hnll : M.loopless, 
  { rw [loopless_iff_loops_eq_empty, ←ncard_eq_zero], 
    linarith [@finsum_le_finsum {P // M.point P} ℕ _ (λ P, 1) (λ P, ((P : set E) \ M.cl ∅).ncard)
      (to_finite _) (to_finite _) hleP] },

  simp_rw [loopless_iff_loops_eq_empty.mp hnll, diff_empty] at hleP h ⊢, 
  rw [ncard_empty, zero_add] at h, 
  
  have hsq := eq_of_finsum_ge_finsum_of_forall_le (to_finite _) (to_finite _) hleP h.symm.le,
  simp only [subtype.forall, subtype.coe_mk, @eq_comm _ 1, ncard_eq_one] at hsq, 

  intro e, 
  obtain ⟨f, hf⟩ := hsq _ (hnll e).cl_point,  
  have hef : e = f := (hf.subset (M.mem_cl_self e) : e = f),
  rwa hef at ⊢ hf, 
end 

end point_count


end matroid


