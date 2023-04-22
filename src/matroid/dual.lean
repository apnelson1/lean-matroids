import .indep

noncomputable theory

open_locale classical

variables {E : Type*} {M M₁ M₂ : matroid E} {B B₁ B₂ X Y Z : set E} {e f x y z : E}

open set
namespace matroid

section dual

@[class] structure has_matroid_dual (α : Type*) := (dual : α → α)

postfix `﹡`:(max+1) := has_matroid_dual.dual 

instance matroid_dual {E : Type*} : has_matroid_dual (matroid E) := ⟨matroid.dual⟩ 

@[simp] lemma dual_base_iff : M﹡.base B ↔ M.base Bᶜ := base_dual_iff' 

lemma base_iff_dual_base_compl : M.base B ↔ M﹡.base Bᶜ :=
by rw [←compl_compl B, dual_base_iff, compl_compl, compl_compl]

@[simp] lemma dual_dual (M : matroid E) : M﹡﹡ = M := dual_dual' M

@[simp] lemma dual_indep_iff_coindep : M﹡.indep X ↔ M.coindep X := dual_indep_iff_coindep'

lemma base.compl_base_dual (hB : M.base B) : M﹡.base Bᶜ := hB.compl_base_dual'

lemma base.compl_inter_basis_of_inter_basis (hB : M.base B) (hBX : M.basis (B ∩ X) X) :
  M﹡.basis (Bᶜ ∩ Xᶜ) Xᶜ := hB.compl_inter_basis_of_inter_basis' hBX

lemma base.inter_basis_iff_compl_inter_basis_dual (hB : M.base B) : 
  M.basis (B ∩ X) X ↔ M﹡.basis (Bᶜ ∩ Xᶜ) Xᶜ :=
hB.inter_basis_iff_compl_inter_basis_dual'
 
lemma dual_inj (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
by {ext B, rw [←compl_compl B, ←dual_base_iff, h, dual_base_iff]}

@[simp] lemma dual_inj_iff : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

end dual

lemma coindep_iff_disjoint_base : M.coindep X ↔ ∃ B, M.base B ∧ disjoint X B := iff.rfl 

lemma coindep.exists_disjoint_base (hX : M.coindep X) : ∃ B, M.base B ∧ disjoint X B := hX  

lemma coindep.base_of_basis_compl (hX : M.coindep X) (hB : M.basis B Xᶜ) : M.base B :=
begin
  obtain ⟨B',hB'⟩ := hX.exists_disjoint_base, 
  exact hB'.1.base_of_basis_supset (subset_compl_iff_disjoint_left.mpr hB'.2) hB, 
end 




end matroid 