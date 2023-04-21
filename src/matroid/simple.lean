import .loop

noncomputable theory
open_locale classical

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

-- lemma simple_on_iff_cl_inj_on :
--   M.simple_on X ↔ M.loopless_on X ∧ inj_on (λ e, M.cl {e}) X :=
-- begin
--   refine ⟨λ h, ⟨h.loopless_on, λ e he f hf (hef : M.cl {e} = M.cl {f}), _⟩, λ h, _⟩,
--   { have he' := singleton_subset_iff.mp ((M.subset_cl {e}).trans hef.subset),
--     rw (h.loopless_on.indep_of_mem hf).mem_cl_iff at he',
--     exact he'.elim id (λ hi, (hi (h e he f hf)).elim) },

--   intros e he f hf,
--   have hcl : f ∉ M.cl {e},
--   { intro hfe, },
--   rw [pair_comm],
--   exact ((h.1.nonloop_of_mem he).indep.not_mem_cl_iff.mp hcl).2,

--   -- have := h.1.indep_of_mem he,
--   -- have := this.not_mem_cl_iff,
--   -- rw h.2 he hf,
--   -- { rw [pair_eq_singleton, ←nonloop_iff_indep],
--   --   exact h.1.nonloop_of_mem hf },

-- end

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


lemma para.pcl_eq_pcl (h : M.para e f) : M.pcl e = M.pcl f :=
begin
  simp_rw [set.ext_iff, mem_pcl_iff], 
  exact λ x, ⟨λ hxe, hxe.trans h, λ hxf, hxf.trans h.symm⟩, 
end 


lemma nonloop.pcl_eq_pcl_iff (he : M.nonloop e) : M.pcl e = M.pcl f ↔ M.para e f := 
begin
  refine ⟨λ h, he.para_of_nonloop_mem_cl _ _, para.pcl_eq_pcl⟩, 
  -- simp_rw [set.ext_iff, mem_pcl_iff], 
  -- exact ⟨λ h, by { rw ←h, exact he.para_self }, 
  --   λ h x, ⟨λ hxe, hxe.trans h, λ hxf, hxf.trans h.symm⟩⟩,  
end 

-- lemma para_iff :
--   M.para


end parallel

end matroid


