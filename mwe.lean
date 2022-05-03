import algebra.big_operators.pi
import algebra.module.pi
import algebra.module.linear_map
import algebra.big_operators.ring
import algebra.star.basic
import data.fintype.card
import data.matrix.dmatrix
import linear_algebra.matrix.symmetric
import linear_algebra.matrix
import linear_algebra.matrix.trace
import linear_algebra.matrix.to_lin
import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic 
import linear_algebra.eigenspace 
import tactic.find
import analysis.normed.group.basic
import analysis.inner_product_space.pi_L2

run_cmd tactic.skip
set_option trace.simplify true
set_option trace.simplify.rewrite_failure false 
set_option trace.linarith true

universe u

variables {α n m R : Type*} [fintype n] [fintype m] [decidable_eq n]

namespace matrix

open_locale matrix

section definite
open_locale complex_order complex_conjugate

instance : has_coe (n → ℝ) (n → ℂ) := ⟨λ x, (λ i, ⟨x i, 0⟩)⟩
instance : has_coe (matrix m n ℝ) (matrix m n ℂ) := ⟨λ M, (λ i j, ⟨M i j, 0⟩)⟩

def vector_conj (v : n → ℂ) : n → ℂ := λ i : n, conj (v i)

def matrix_conj (M : matrix n n ℂ) : matrix n n ℂ := λ i : n, vector_conj (M i)

def is_hermitian (M : matrix n n ℂ) : Prop :=  matrix_conj Mᵀ  = M

def is_pos_def (M : matrix n n ℂ) := M.is_hermitian ∧ ∀ (v : n → ℂ), v ≠ 0 → 0 < dot_product (vector_conj v) (M.mul_vec v)

def is_neg_def (M : matrix n n ℂ) := M.is_hermitian ∧ ∀ (v : n → ℂ), v ≠ 0 → 0 > dot_product (vector_conj v) (M.mul_vec v) 

def is_pos_semidef (M : matrix n n ℂ) := M.is_hermitian ∧ ∀ (v : n → ℂ), v ≠ 0 → 0 ≤ dot_product (vector_conj v) (M.mul_vec v)

def is_neg_semidef (M : matrix n n ℂ) := M.is_hermitian ∧ ∀ (v : n → ℂ), v ≠ 0 → 0 ≥ dot_product (vector_conj v) (M.mul_vec v) 

def has_eigenpair (M : matrix n n ℂ) (e : ℂ) (x : n → ℂ ) := x ≠ 0 ∧ mul_vec M x = e • x 

def has_eigenvector (M : matrix n n ℂ) (x : n → ℂ ) := ∃ e : ℂ , has_eigenpair M e x

def has_eigenvalue (M : matrix n n ℂ) (e : ℂ) := ∃ x : n → ℂ , has_eigenpair M e x

def has_right_eigenpair (M : matrix n n ℂ) (e : ℂ) (x : n → ℂ ) := x ≠ 0 ∧ vec_mul x M = e • x 

def has_right_eigenvector (M : matrix n n ℂ) (x : n → ℂ ) := ∃ e : ℂ , has_right_eigenpair M e x

def has_right_eigenvalue (M : matrix n n ℂ) (e : ℂ) := ∃ x : n → ℂ , has_right_eigenpair M e x

def eigenspace (M : matrix n n ℂ) := set_of (has_eigenvalue M)

def is_skew_symmetric (M : matrix n n ℂ ) := Mᵀ = -M

noncomputable def vector_magnitude (v : n → ℂ) : ℂ := (dot_product (vector_conj v) v)

theorem vector_magnitude_geq_zero (v : n → ℂ) : vector_magnitude v ≥ 0 :=
begin
   rw vector_magnitude,
   rw dot_product,
   have h : ∀ (x : n), conj (v x) * (v x) ≥ 0 :=
   begin
     intro x,
     have h_im : (conj (v x) * (v x)).im = (0:ℂ).im :=
     begin
       rw complex.mul_im,
       rw complex.conj_re,
       rw complex.conj_im,
       rw complex.zero_im,
       nlinarith,
     end,
    have h_re : (conj (v x) * (v x)).re ≥ (0:ℂ).re :=
    begin
      rwa complex.mul_re,
      rwa complex.conj_re,
      rwa complex.conj_im,
      rw neg_mul,
      rw sub_neg_eq_add,
      rw complex.zero_re,
      nlinarith,
    end,
    rw [ge,complex.le_def],
    split,
    assumption,
    rw eq_comm,
    assumption,
   end,
  apply finset.sum_nonneg,
  intro x,
  intro _,
  specialize h x,
  rw ← ge,
  exact h,
end

theorem vector_magnitude_real (v : n → ℂ ) : vector_magnitude v = (vector_magnitude v).re :=
begin
  ext,
  rw complex.of_real_re,
  have h := vector_magnitude_geq_zero v,
  rw [ge,complex.le_def] at h,
  cases h with h_re h_im,
  rw complex.of_real_im,
  rw ← h_im,
  rw complex.zero_im,
end

lemma sum_re {v : n → ℂ} {f : ℂ → ℂ }: finset.univ.sum (λ i, (f (v i)).re) = (finset.univ.sum (λ i, f(v i))).re:=
begin
  rw ← complex.re_lm_coe,
  rw linear_map.map_sum,
end

lemma sum_im {v : n → ℂ} {f : ℂ → ℂ }: finset.univ.sum (λ i, (f (v i)).im) = (finset.univ.sum (λ i, f(v i))).im:=
begin
  rw ← complex.im_lm_coe,
  rw linear_map.map_sum,
end

lemma sum_conj {v : n → ℂ } {f : ℂ → ℂ }: conj (finset.univ.sum (λ i, f (v i))) = finset.univ.sum (λ i, conj (f (v i))) :=
begin
  ext,
  rw complex.conj_re,
  rw ← sum_re,
  change finset.univ.sum (λ (i : n), (conj (f (v i))).re) = (finset.univ.sum (λ (i : n), conj (f (v i)))).re,
  rw sum_re,
  rw ← sum_im,
  simp only [complex.conj_im, finset.sum_neg_distrib, neg_inj],
  rw sum_im, 
end

lemma conj_sum {v : n → ℂ} : conj (finset.univ.sum (λ i, (v i))) = finset.univ.sum (λ i, conj ((v i))) :=
begin
  have h : conj (finset.univ.sum (λ i, id (v i))) = finset.univ.sum (λ i, conj (id (v i))),
  exact sum_conj,
  dsimp at h,
  exact h,
end

lemma mul_conj (a : ℂ ) (b : ℂ ) : conj (a * b) = (conj a) * (conj b) :=
begin
  ext;
  simp only [complex.mul_re, complex.conj_re, complex.conj_im, mul_neg, neg_mul, neg_neg],
  simp only [complex.mul_im, neg_add_rev, complex.conj_re, complex.conj_im, mul_neg, neg_mul],
  rw add_comm,
end

lemma dot_product_conj (v : n → ℂ) (w : n → ℂ) : conj (dot_product v w) = dot_product (vector_conj v) (vector_conj w) :=
begin
  repeat {rw dot_product},
  repeat {rw vector_conj},
  dsimp only,
  rw conj_sum,
  apply finset.sum_congr,
  refl,
  intros _ _,
  rw mul_conj,
end

lemma vec_mul_conj (v : n → ℂ) (M : matrix n n ℂ) : vector_conj (vec_mul v M) = vec_mul (vector_conj v) (matrix_conj M):=
begin
  have vm : vec_mul (vector_conj v) M.matrix_conj = λ i , dot_product (vector_conj v) (λ j, conj (M j i)),
  ext;
  rw vec_mul;
  rw dot_product;
  rw dot_product;
  rw matrix_conj;
  simp only;
  rw vector_conj;
  simp only;
  simp_rw vector_conj,
  rw vm,
  ext;
  rw vector_conj;
  rw vector_conj;
  dsimp only;
  rw vec_mul;
  rw dot_product_conj;
  repeat {rw vector_conj},
end

lemma mul_vec_conj (v : n → ℂ) (M : matrix n n ℂ) : vector_conj (mul_vec M v) = mul_vec (matrix_conj M) (vector_conj v) :=
begin
  have mv : mul_vec (matrix_conj M) (vector_conj v) = λ i , dot_product (vector_conj v) (λ j, conj (M i j)),
  ext;
  rw mul_vec;
  rw dot_product;
  rw dot_product;
  rw matrix_conj;
  simp only;
  rw vector_conj;
  simp only;
  simp_rw mul_comm,
  rw mv,
  ext;
  rw vector_conj;
  rw vector_conj;
  dsimp only;
  rw mul_vec;
  rw dot_product_conj;
  repeat {rw vector_conj};
  simp_rw dot_product;
  simp_rw mul_comm,
end

lemma vector_conj_conj (v : n → ℂ) : vector_conj (vector_conj v) = v := 
begin
  apply funext,
  rw vector_conj,
  intro x,
  rw vector_conj,
  change conj (conj (v x)) = v x,
  rw complex.conj_conj,
end  

lemma matrix_conj_conj (M : matrix n n ℂ) : matrix_conj (matrix_conj M) = M := 
begin
  apply funext,
  rw matrix_conj,
  rw matrix_conj,
  intro x,
  change vector_conj (vector_conj (M x)) = M x,
  rw vector_conj_conj,
end 

lemma vec_smul_conj (v : n → ℂ) (x : ℂ) : vector_conj (x • v) = (conj x) • (vector_conj v) :=
begin
  repeat {rw vector_conj},
  simp only [pi.smul_apply, algebra.id.smul_eq_mul, map_mul],
  simp_rw mul_conj,
  refl,
end

lemma mat_smul_conj (M : matrix n n ℂ) (x : ℂ) : matrix_conj (x • M) = (conj x) • (matrix_conj M):=
begin
  repeat {rw matrix_conj},
  funext,
  dsimp,
  rw vec_smul_conj,
  rw pi.smul_apply,
  rw algebra.id.smul_eq_mul,
end

lemma mat_add_conj (M : matrix n n ℂ) (N : matrix n n ℂ ) : matrix_conj (M + N) = matrix_conj M + matrix_conj N :=
begin
  funext,
  repeat {rw matrix_conj},
  dsimp,
  repeat {rw vector_conj},
  dsimp,
  rw map_add,
end

lemma mat_sub_conj (M : matrix n n ℂ) (N : matrix n n ℂ ) : matrix_conj (M - N) = matrix_conj M - matrix_conj N :=
begin
  funext,
  repeat {rw matrix_conj},
  dsimp,
  repeat {rw vector_conj},
  dsimp,
  rw map_sub,
end

lemma mul_vec_trans (M : matrix n n ℂ ) (v : n → ℂ ) : (mul_vec Mᵀ v) = (vec_mul v M) :=
begin
  ext;
  rw mul_vec;
  rw vec_mul;
  rw dot_product;
  rw dot_product;
  simp_rw matrix.transpose;
  rw finset.sum_congr,
  refl,
  intros _ _,
  rw mul_comm,
  refl,
  intros _ _,
  rw mul_comm,
end

lemma vec_mul_trans (M : matrix n n ℂ) (v : n → ℂ ) :  (vec_mul v Mᵀ ) = mul_vec M v :=
begin
  have h : M.mul_vec v = Mᵀᵀ.mul_vec v,
  rw transpose_transpose,
  rw h,
  rw mul_vec_trans,
end

lemma matrix_trans_conj (M : matrix n n ℂ) : (matrix_conj Mᵀ) = (matrix_conj M)ᵀ :=
begin
  funext,
  rw matrix_conj,
  rw transpose_apply,
  dsimp,
  rw vector_conj,
  rw matrix_conj,
  dsimp,
  rw vector_conj,
end 

lemma vector_zero_iff_magnitude_zero (v : n → ℂ) : vector_magnitude v = 0 ↔ v=0 := 
begin
  rw vector_magnitude,
  split,
  intro prod,
  rw dot_product at prod,
  have gez : ∀ i : n, v i * vector_conj v i ≥ 0 :=
  begin
    intro i,
    rw vector_conj,
    dsimp,
    rw ge_iff_le,
    rw complex.le_def,
    split,
    rw complex.mul_re,
    simp only [complex.zero_re, complex.conj_re, complex.conj_im, mul_neg, sub_neg_eq_add],
    nlinarith,
    rw complex.mul_im,
    rw complex.conj_im,
    rw complex.conj_re,
    simp only [complex.zero_im, mul_neg],
    rw mul_comm,
    rw add_left_neg,
  end,
  have important : finset.univ.sum(λ i , v i * vector_conj v i ) = 0 ↔ ∀ i ∈ finset.univ, v i * vector_conj v i = 0,
  apply finset.sum_eq_zero_iff_of_nonneg,
  intros i _,
  specialize gez i,
  rw ge_iff_le at gez,
  exact gez,
  simp_rw mul_comm at prod,
  rw prod at important,
  simp only [eq_self_iff_true, finset.mem_univ, mul_eq_zero, forall_true_left, true_iff] at important,
  funext i,
  specialize important i,
  cases important with vz vcz,
  rw vz,
  refl,
  rw vector_conj at vcz,
  dsimp at vcz,
  have vczc := congr_arg conj vcz,
  rw [complex.conj_conj] at vczc,
  simp only [map_zero] at vczc,
  rw vczc, 
  refl,
  intro ez,
  rw ez,
  rw dot_product_comm,
  rw zero_dot_product,
end

theorem hermitian_real_eigenvalues (M : matrix n n ℂ) (h : is_hermitian M) (e : ℂ) (ev : has_eigenvalue M e) : e.im = 0 :=
begin
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases ep with nz mul,
  rw is_hermitian at h,
  have mul_0 : dot_product (vector_conj v) (M.mul_vec v) = dot_product (vector_conj v) (e • v) := 
  begin
    rw mul,
  end,
  have mul_1 : dot_product (vector_conj v) (e • v) = e * (vector_magnitude v) :=
  begin
    rw vector_magnitude,
    simp only [dot_product_smul, algebra.id.smul_eq_mul],
  end,
  have mul_2 : dot_product v (e • (vector_conj v)) = e * vector_magnitude v :=
  begin
    rw dot_product_comm,
    rw vector_magnitude,
    rw dot_product,
    rw dot_product,
    rw finset.mul_sum,
    rw finset.sum_congr,
    refl,
    intros _ _,
    simp only [pi.smul_apply, algebra.id.smul_eq_mul,mul_assoc],
  end,
  have mul_3 : dot_product (vector_conj v) (mul_vec (Mᵀ.matrix_conj) v) = (conj e) * vector_magnitude v :=
  begin
    rw dot_product_mul_vec,
    rw matrix_trans_conj,
    rw vec_mul_trans,
    rw ← mul_vec_conj,
    rw mul,
    rw vec_smul_conj,
    rw vector_magnitude,
    simp only [smul_dot_product, algebra.id.smul_eq_mul],
  end,
  rw h at mul_3,
  rw mul at mul_3,
  rw mul_1 at mul_3,
  rw ne at nz,
  rw ← vector_zero_iff_magnitude_zero at nz,
  rw vector_magnitude at nz,
  rw ← vector_magnitude at nz,
  rw mul_eq_mul_right_iff at mul_3,
  simp only [nz] at mul_3,
  rw or_false at mul_3,
  have e_im := congr_arg complex.im mul_3,
  rw complex.conj_im at e_im,
  rw eq_neg_iff_add_eq_zero at e_im,
  rw add_self_eq_zero at e_im,
  exact e_im,
end

theorem pos_def_pos_eigenvalues (M : matrix n n ℂ) (e : ℂ) (h : M.is_pos_def) (ev : has_eigenvalue M e) : e > 0 := 
begin
  rw is_pos_def at h,
  have ev_prop := ev,
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases h with herm mul,
  have herm_prop := herm,
  rw is_hermitian at herm,
  cases ep with vnz vmul,
  specialize mul v,
  simp only [vnz, ne.def, not_false_iff, forall_true_left] at mul,
  rw vmul at mul,
  rw dot_product_smul at mul,
  rw ← vector_magnitude at mul,
  rw smul_eq_mul at mul,
  have vmgz : vector_magnitude v > 0,
  rw gt_iff_lt,
  rw lt_iff_le_and_ne,
  split,
  rw ← ge_iff_le,
  simp only [vector_magnitude_geq_zero],
  rw ne.def,
  rw eq_comm,
  rw vector_zero_iff_magnitude_zero,
  rw ← ne.def,
  exact vnz,
  rw vector_magnitude_real at mul,
  rw vector_magnitude_real at vmgz,
  have e_re : e = e.re,
  ext,
  rw complex.of_real_re,
  rw complex.of_real_im,
  apply hermitian_real_eigenvalues M herm_prop e,
  exact ev_prop,
  rw e_re at mul,
  rw e_re,
  have key : 0 < (e.re) * ((vector_magnitude v).re) / ((vector_magnitude v).re),
  apply div_pos,
  cases mul with mul_re mul_im,
  simp only [complex.zero_re, complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero] at mul_re,
  exact mul_re,
  rw ← gt_iff_lt,
  simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
  rwa gt_iff_lt,
  rw mul_div_cancel at key,
  simp only [key, gt_iff_lt, complex.zero_lt_real],
  rw ne.def,
  by_contra vz,
  rw vz at vmgz,
  simp only [complex.of_real_zero, gt_iff_lt, lt_self_iff_false] at vmgz,
  exact vmgz,
end

theorem pos_semidef_nonneg_eigenvalues (M : matrix n n ℂ) (e : ℂ) (h : M.is_pos_semidef) (ev : has_eigenvalue M e) : e ≥ 0 := 
begin
  rw is_pos_semidef at h,
  have ev_prop := ev,
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases h with herm mul,
  have herm_prop := herm,
  rw is_hermitian at herm,
  cases ep with vnz vmul,
  specialize mul v,
  simp only [vnz, ne.def, not_false_iff, forall_true_left] at mul,
  rw vmul at mul,
  rw dot_product_smul at mul,
  rw ← vector_magnitude at mul,
  rw smul_eq_mul at mul,
  have vmgz : vector_magnitude v > 0,
  rw gt_iff_lt,
  rw lt_iff_le_and_ne,
  split,
  rw ← ge_iff_le,
  simp only [vector_magnitude_geq_zero],
  rw ne.def,
  rw eq_comm,
  rw vector_zero_iff_magnitude_zero,
  rw ← ne.def,
  exact vnz,
  rw vector_magnitude_real at mul,
  rw vector_magnitude_real at vmgz,
  have e_re : e = e.re,
  ext,
  rw complex.of_real_re,
  rw complex.of_real_im,
  apply hermitian_real_eigenvalues M herm_prop e,
  exact ev_prop,
  rw e_re at mul,
  rw e_re,
  have key : 0 ≤ (e.re) * ((vector_magnitude v).re) / ((vector_magnitude v).re),
  apply div_nonneg,
  cases mul with mul_re mul_im,
  simp only [complex.zero_re, complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero] at mul_re,
  exact mul_re,
  rw ← ge_iff_le,
  simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
  rw ge_iff_le,
  rw lt_iff_le_and_ne at vmgz,
  cases vmgz with vge vne,
  exact vge,
  rw mul_div_cancel at key,
  simp only [key, ge_iff_le, complex.zero_le_real],
  rw ne.def,
  by_contra vz,
  rw vz at vmgz,
  simp only [complex.of_real_zero, gt_iff_lt, lt_self_iff_false] at vmgz,
  exact vmgz,
end

theorem herm_iff_neg_herm (M : matrix n n ℂ) : is_hermitian M ↔ is_hermitian (-M) :=
begin
  repeat {rw is_hermitian},
  have key : (-M)ᵀ.matrix_conj = -(Mᵀ.matrix_conj),
  funext,
  rw matrix_conj,
  rw matrix_conj,
  dsimp,
  rw vector_conj,
  rw vector_conj,
  dsimp,
  ext,
  simp only [complex.neg_re, complex.conj_re],
  simp only [complex.neg_im, complex.conj_im],
  rw key,
  rw neg_inj,
end

theorem neg_def_iff_neg_pos_def (M : matrix n n ℂ) : is_neg_def M ↔ is_pos_def (-M) :=
begin

  have important : ∀ v : n → ℂ ,  dot_product (vector_conj v) ((-M).mul_vec v) = -dot_product (vector_conj v) (M.mul_vec v),
  intro v,
  rw dot_product,
  rw dot_product,
  rw ← finset.sum_neg_distrib,
  rw finset.sum_congr,
  refl,
  intros _ _,
  rw neg_mul_vec,
  rw pi.neg_apply,
  rw mul_neg,

  rw is_neg_def,
  rw is_pos_def,
  rw ← herm_iff_neg_herm,
  rw and.congr_right_iff,
  intro herm,
  
  split;
  
  intro prop;
  intro v;
  intro vnz;
  specialize prop v;
  simp only [vnz, ne.def, not_false_iff, forall_true_left, gt_iff_lt] at prop;
  specialize important v,
  rw important,
  simp only [prop, right.neg_pos_iff],
  rw important at prop,
  rw right.neg_pos_iff at prop,
  rw gt_iff_lt,
  exact prop,
end 

theorem neg_semidef_iff_neg_pos_semidef (M : matrix n n ℂ) : is_neg_semidef M ↔ is_pos_semidef (-M) :=
begin

  have important : ∀ v : n → ℂ ,  dot_product (vector_conj v) ((-M).mul_vec v) = -dot_product (vector_conj v) (M.mul_vec v),
  intro v,
  rw dot_product,
  rw dot_product,
  rw ← finset.sum_neg_distrib,
  rw finset.sum_congr,
  refl,
  intros _ _,
  rw neg_mul_vec,
  rw pi.neg_apply,
  rw mul_neg,

  rw is_neg_semidef,
  rw is_pos_semidef,
  rw ← herm_iff_neg_herm,
  rw and.congr_right_iff,
  intro herm,
  
  split;
  
  intro prop;
  intro v;
  intro vnz;
  specialize prop v;
  simp only [vnz, ne.def, not_false_iff, forall_true_left, gt_iff_lt] at prop;
  specialize important v,
  rw important,
  simp only [right.nonneg_neg_iff],
  rwa ← ge_iff_le,
  rw important at prop,
  rw right.nonneg_neg_iff at prop,
  exact prop,
end 

theorem neg_def_neg_eigenvalues (M : matrix n n ℂ) (e : ℂ) (h : M.is_neg_def) (ev : has_eigenvalue M e) : e < 0 := 
begin
  rw neg_def_iff_neg_pos_def at h,
  have ev_prop := ev,
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases ep with vnz vmul,
  rw is_pos_def at h,
  cases h with herm_prop mul,
  rw ← herm_iff_neg_herm at herm_prop,
  specialize mul v,
  simp only [vnz, ne.def, not_false_iff, forall_true_left] at mul,
  have neg_vmul : (-M).mul_vec v = -(e • v),
  rw neg_mul_vec,
  rw neg_inj,
  exact vmul,
  rw neg_vmul at mul,
  simp only [dot_product_neg, dot_product_smul, algebra.id.smul_eq_mul, right.neg_pos_iff] at mul,
  rw ← vector_magnitude at mul,

  have vmgz : vector_magnitude v > 0,
  rw gt_iff_lt,
  rw lt_iff_le_and_ne,
  split,
  rw ← ge_iff_le,
  simp only [vector_magnitude_geq_zero],
  rw ne.def,
  rw eq_comm,
  rw vector_zero_iff_magnitude_zero,
  rw ← ne.def,
  exact vnz,
  rw vector_magnitude_real at mul,
  rw vector_magnitude_real at vmgz,
  have e_re : e = e.re,
  ext,
  rw complex.of_real_re,
  rw complex.of_real_im,
  apply hermitian_real_eigenvalues M herm_prop e,
  exact ev_prop,
  rw e_re at mul,
  rw e_re,
  have key : (e.re) * ((vector_magnitude v).re) / ((vector_magnitude v).re) < 0,
  rw div_neg_iff,
  cases mul with mul_re mul_im,
  simp only [complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero, complex.zero_re] at mul_re,
  simp only,
  right,
  split,
  exact mul_re,
  simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
  exact vmgz,
  rw mul_div_cancel at key,
  rw complex.lt_def,
  split,
  simp only [key, complex.of_real_re, complex.zero_re],
  simp only [complex.of_real_im, complex.zero_im],
  rw ne_iff_lt_or_gt,
  right,
  simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
  rwa gt_iff_lt, 
end

theorem neg_semidef_nonpos_eigenvalues (M : matrix n n ℂ) (e : ℂ) (h : M.is_neg_semidef) (ev : has_eigenvalue M e) : e ≤ 0 := 
begin
  rw neg_semidef_iff_neg_pos_semidef at h,
  have ev_prop := ev,
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases ep with vnz vmul,
  rw is_pos_semidef at h,
  cases h with herm_prop mul,
  rw ← herm_iff_neg_herm at herm_prop,
  specialize mul v,
  simp only [vnz, ne.def, not_false_iff, forall_true_left] at mul,
  have neg_vmul : (-M).mul_vec v = -(e • v),
  rw neg_mul_vec,
  rw neg_inj,
  exact vmul,
  rw neg_vmul at mul,
  simp only [dot_product_neg, dot_product_smul, algebra.id.smul_eq_mul, right.neg_pos_iff] at mul,
  rw ← vector_magnitude at mul,

  have vmgz : vector_magnitude v > 0,
  rw gt_iff_lt,
  rw lt_iff_le_and_ne,
  split,
  rw ← ge_iff_le,
  simp only [vector_magnitude_geq_zero],
  rw ne.def,
  rw eq_comm,
  rw vector_zero_iff_magnitude_zero,
  rw ← ne.def,
  exact vnz,
  rw vector_magnitude_real at mul,
  rw vector_magnitude_real at vmgz,
  have e_re : e = e.re,
  ext,
  rw complex.of_real_re,
  rw complex.of_real_im,
  apply hermitian_real_eigenvalues M herm_prop e,
  exact ev_prop,
  rw e_re at mul,
  rw e_re,
  have key : (e.re) * ((vector_magnitude v).re) / ((vector_magnitude v).re) ≤ 0,
  rw div_nonpos_iff,
  cases mul with mul_re mul_im,
  simp only [complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero, complex.zero_re] at mul_re,
  simp only,
  right,
  split,
  simp only [complex.neg_re, complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero, right.nonneg_neg_iff] at mul_re,
  exact mul_re,
  simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
  rw lt_iff_le_and_ne at vmgz,
  cases vmgz with vmge vne,
  exact vmge,
  rw mul_div_cancel at key,
  rw complex.le_def,
  split,
  simp only [key, complex.of_real_re, complex.zero_re],
  simp only [complex.of_real_im, complex.zero_im],
  rw ne_iff_lt_or_gt,
  right,
  simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
  rwa gt_iff_lt, 
end

theorem herm_real_smul_herm (M : matrix n n ℂ) (a : ℂ) : a=a.re →  (a=0 ∨ is_hermitian M ↔ is_hermitian (a • M)):=
begin
  intro a_re,
  rw is_hermitian,
  rw is_hermitian,
  rw transpose_smul,
  rw mat_smul_conj Mᵀ a,
  nth_rewrite 1 a_re,
  simp only [is_R_or_C.conj_of_real, complex.coe_smul],
  split,
  intro h,
  cases h with az m_herm,
  rw az,
  rw zero_smul,
  rw complex.zero_re,
  rw zero_smul,
  rw m_herm,
  rw a_re,
  simp only [complex.of_real_re, complex.coe_smul],
  intro h,
  rw or_iff_not_and_not,
  by_contra h_1,
  cases h_1 with anz mnh,
  apply mnh,
  rw ← sub_eq_zero at h,
  rw a_re at h,
  simp only [complex.of_real_re, complex.coe_smul] at h,
  rw ← smul_sub at h,
  rw smul_eq_zero at h,
  rw a_re at anz,
  rw complex.of_real_eq_zero at anz,
  simp only [anz, false_or] at h,
  rw sub_eq_zero at h,
  exact h,
end

lemma herm_sum (M : matrix n n ℂ) (N : matrix n n ℂ) (hm : is_hermitian M) (hn : is_hermitian N) : is_hermitian (M + N) :=
begin
  rw is_hermitian,
  rw is_hermitian at hm,
  rw is_hermitian at hn,
  funext,
  rw matrix_conj,
  dsimp,
  rw vector_conj,
  dsimp,
  nth_rewrite 1 ← hm,
  nth_rewrite 1 ← hn,
  repeat {rw matrix_trans_conj},
  dsimp,
  repeat {rw matrix_conj},
  dsimp,
  repeat {rw vector_conj},
  dsimp,
  rw map_add,
end

theorem matrix_decomposition_hermitian (M : matrix n n ℂ) : ∃ A : matrix n n ℂ, ∃ B : matrix n n ℂ, is_hermitian A ∧ is_hermitian B ∧ M = A + complex.I • B :=
begin
  have h := herm_real_smul_herm, 

  have trivial : (1/2) = ((complex.re(1/2)):ℂ) :=
  begin
    ext,
    rw complex.of_real_re,
    rw complex.of_real_im,
    simp only [one_div, complex.inv_im, complex.bit0_im, complex.one_im, bit0_zero, neg_zero', zero_div],
  end,

  have trivial_2 : ((1:ℂ)/2) = 0 = false :=
  begin
    simp only [eq_iff_iff, iff_false],
    by_contra,
    simp only [one_div, inv_eq_zero, bit0_eq_zero, one_ne_zero] at h,
    exact h,
  end,

  have trivial_3 : (1:ℂ)/2 + (1:ℂ)/2 = 1 :=
  begin
    rw ← sub_eq_zero,
    rw ← two_mul,
    rw mul_div_comm,
    rw div_self,
    rw mul_one,
    rw sub_self,
    by_contra,
    rw ← one_add_one_eq_two at h,
    rw add_self_eq_zero at h,
    have h_1 := one_ne_zero,
    rw ne at h_1,
    apply h_1,
    exact h,
    exact infinite.nontrivial ℂ,
  end,

  --have m12_herm : is_hermitian (((1:ℂ)/2) • M):= 
  --begin
  --  specialize h M,
  --  specialize h (1/2),
  --  rw ← trivial at h,
  --  rw eq_self_iff_true at h,
  --  simp only [false_or, forall_true_left] at h,
  --  rw trivial_2 at h,
  --  rw false_or at h,
  --end,
  use ((1:ℂ)/2) • (M + (matrix_conj Mᵀ)),
  use (complex.I/2) • ((matrix_conj Mᵀ) - M),
  split,
  rw ← herm_real_smul_herm,
  rw trivial_2,
  rw false_or,
  rw is_hermitian,
  rw transpose_add,
  rw mat_add_conj,
  nth_rewrite 1 add_comm,
  rw add_left_cancel_iff,
  rw matrix_trans_conj,
  rw matrix_conj_conj,
  rw transpose_transpose,
  exact trivial,
  split,
  
  rw is_hermitian,
  rw smul_sub,
  rw matrix_trans_conj,
  rw mat_sub_conj,
  rw matrix_trans_conj,
  rw mat_smul_conj,
  simp only [transpose_sub, transpose_smul],
  rw matrix_trans_conj,
  rw transpose_transpose,
  rw matrix_conj_conj,

  have conj_i : conj(complex.I/2) = -complex.I/2:=
  begin
    ext,
    rw complex.conj_re,
    rw neg_div,
    rw complex.neg_re,
    rw eq_neg_iff_add_eq_zero,
    rw add_self_eq_zero,
    rw complex.div_re,
    rw complex.I_re,
    simp only [zero_mul, zero_div, complex.bit0_im, complex.one_im, bit0_zero, mul_zero, add_zero],
    rw complex.conj_im,
    rw neg_div,
    rw complex.neg_im,
  end,

  rw conj_i,
  rw neg_div,
  nth_rewrite 1 ← neg_add_eq_sub,
  rw neg_smul,
  rw sub_eq_add_neg,
  rw add_right_inj,
  rw mat_smul_conj,
  rw conj_i,
  rw transpose_smul,
  rw neg_div,
  rw neg_smul,
  rw neg_neg,

  rw smul_add,
  rw ← smul_assoc,
  rw smul_sub,
  rw smul_eq_mul,
  rw mul_div,
  rw complex.I_mul_I,
  rw neg_div,
  rw neg_smul,
  rw neg_smul,
  rw neg_sub_neg,
  rw add_add_sub_cancel,
  rw ← add_smul,
  rw trivial_3,
  rw one_smul,
  exact n,
  exact _inst_1,
  exact _inst_3,
end

lemma vector_eq_conj_iff_real (v : n → ℂ) : (∃ u : n → ℝ, v = u) ↔ v = vector_conj v :=
begin
  split,
  intro h,
  cases h with u veq,
  funext,
  rw vector_conj,
  dsimp,
  rw veq,
  rw eq_comm,
  rw complex.eq_conj_iff_real,
  use u x,
  refl,
  intro veq,
  use (λ i , (v i).re ),
  funext,
  have vx_re : v x = (v x).re,
  ext,
  rw complex.of_real_re,
  rw complex.of_real_im,
  rw ← add_self_eq_zero,
  nth_rewrite 0 veq,
  rw vector_conj,
  dsimp,
  rw add_left_neg,
  rw vx_re,
  refl,
end

lemma matrix_eq_conj_iff_real (M : matrix n n ℂ) : (∃ N : matrix n n ℝ, M = N) ↔ M = matrix_conj M :=
begin
  split,
  intro h,
  cases h with N eq,
  rw eq,
  funext,
  rw matrix_conj,
  simp_rw vector_conj,
  rw eq_comm,
  rw complex.eq_conj_iff_real,
  use N i j,
  refl,
  
  intro meq,
  use (λ (i_1 i_2 : n), (M i_1 i_2).re),
  funext i j,
  have mij_conj : M i j = conj (M i j) :=
  begin
    nth_rewrite 0 meq,
    rw matrix_conj,
    dsimp,
    rw vector_conj,
  end,
  have mij_re : M i j = (M i j).re,
  ext,
  rw complex.of_real_re,
  rw complex.of_real_im,
  rw ← add_self_eq_zero,
  nth_rewrite 0 mij_conj,
  rw complex.conj_im,
  rw add_left_neg,

  rw eq_comm at mij_conj,
  rw mij_re,
  refl,
end

lemma matrix_conj_add_real (M : matrix n n ℂ) : ∃ N : matrix n n ℝ , (matrix_conj M + M) = N :=
begin
  rw matrix_eq_conj_iff_real,
  rw mat_add_conj,
  rw matrix_conj_conj,
  rw add_comm, 
end

theorem matrix_decomposition_symm_skew_symm (M : matrix n n ℂ) (herm : is_hermitian M) : ∃ A : matrix n n ℝ , ∃ B : matrix n n ℂ, is_symm A ∧ is_skew_symmetric B ∧ M = A + complex.I • B:=
begin

  have complex_two_nez : (2:ℂ) ≠ (0:ℂ) :=
  begin
    rw ← one_add_one_eq_two,
    rw ne.def,
    rw add_self_eq_zero,
    rw ← ne.def,
    exact one_ne_zero,
  end,

  have h_1 : (matrix_conj M + M) = matrix_conj (matrix_conj M + M),
  rw mat_add_conj,
  rw matrix_conj_conj,
  rw add_comm,
  rw ← matrix_eq_conj_iff_real at h_1,
  cases h_1 with N hN,
  existsi ((1:ℝ)/2)•N,
  existsi (complex.I/(2:ℂ)) • (matrix_conj M - M),
  split,
  rw is_symm,
  rw transpose_smul,
  rw is_hermitian at herm,
  have h_2 : Nᵀ = N :=
  begin
    ext,
    rw ← complex.of_real_inj,
    
    have h_3 : ∀ (i_1 i_2 : n ), (N:matrix n n ℂ) i_1 i_2 = ((N i_1 i_2):ℂ),
    intros i_1 i_2,
    refl,

    have n_ji : (N:matrix n n ℂ) j i = ((N j i):ℂ),
    specialize h_3 j i,
    rw h_3,

    have n_ij : (N:matrix n n ℂ) i j = ((N i j):ℂ),
    specialize h_3 i j,
    rw h_3,

    rw ← n_ji,
    rw ← n_ij,

    rw ← hN,
    dsimp,
    nth_rewrite 0 ← herm,
    rw matrix_conj_conj,
    rw transpose,
    nth_rewrite 2 ← herm,
    rw matrix_conj_conj,
    rw transpose,
    rw add_comm,
  end,

  rw h_2,
  split,
  rw is_skew_symmetric,
  rw smul_sub,
  simp only [transpose_sub, transpose_smul, neg_sub],
  rw is_hermitian at herm,
  rw ← matrix_trans_conj,
  rw herm,
  nth_rewrite 1 ← herm,
  rw matrix_trans_conj,
  rw transpose_transpose,

  rw smul_sub,
  rw smul_sub,
  rw ← smul_assoc,
  rw smul_eq_mul,
  rw ← mul_div_assoc,
  rw complex.I_mul_I,
  rw ← smul_assoc,
  rw smul_eq_mul,
  rw ← mul_div_assoc,
  rw complex.I_mul_I,
  rw neg_div,
  rw add_sub,
  rw neg_smul,
  rw neg_smul,
  rw sub_neg_eq_add,
  
  have mul_2 : ∀ (X Y : matrix n n ℂ) , X = Y ↔ (2 : ℂ) • X = (2 : ℂ) • Y :=
  begin
    intros X Y,
    split,
    intro xey,
    rw xey,
    intro xey_2,
    funext,
    repeat{rw two_smul at xey_2},
    
    have mul_2_scalar : (X + X) x x_1 = (Y+Y) x x_1,
    rw xey_2,

    simp only [dmatrix.add_apply] at mul_2_scalar,
    repeat {rw ← two_mul at mul_2_scalar},
    rw mul_eq_mul_left_iff at mul_2_scalar,
    simp only [bit0_eq_zero, one_ne_zero, or_false] at mul_2_scalar,
    exact mul_2_scalar,
  end,

  have mul_3 := mul_2,

  specialize mul_2 M,
  specialize mul_2 (↑(((1:ℝ) / 2) • N) + -(((1:ℂ) / 2) • M.matrix_conj) + ((1:ℂ) / 2) • M),
  rw mul_2,
  repeat {rw smul_add},
  rw ← smul_assoc,
  simp only [neg_nsmul, nsmul_eq_mul, nat.cast_bit0, nat.cast_one, mul_inv_cancel_of_invertible, one_smul],
  rw two_smul,
  rw smul_eq_mul,
  rw mul_div_cancel',
  rw one_smul,
  rw add_left_inj,
  rw smul_neg,
  rw ← smul_assoc,
  rw smul_eq_mul,
  rw mul_div_cancel',
  rw one_smul,
  rw ← sub_eq_iff_eq_add,
  rw sub_neg_eq_add,
  rw add_comm,
  rw hN,

  have n_smul : (N:(matrix n n ℂ)) = (2:ℂ) • ( ((1:ℂ)/2) • (N:(matrix n n ℂ))),
  simp only [one_div, smul_inv_smul₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff],
  rw n_smul,
  repeat {rw two_smul},
  simp only [one_div],

  specialize mul_3 ((2:ℂ)⁻¹ • (N:matrix n n ℂ)),
  specialize mul_3 ↑((2:ℝ)⁻¹ • N),
  repeat{rw two_smul at mul_3},

  rw ← mul_3,
  funext i j,
  rw pi.smul_apply,
  rw pi.smul_apply,

  -- unfold coe,
  -- unfold lift_t,
  -- unfold has_lift_t.lift,
  -- unfold coe_t,
  -- unfold has_coe_t.coe,
  -- unfold coe_b,
  -- unfold has_coe.coe,

  change (2 : ℂ)⁻¹ • ({re := N i j, im := 0} : ℂ) = {re := (2 : ℝ)⁻¹ • N i j, im := 0},
  rw smul_eq_mul,
  ext,
  rw complex.mul_re,
  simp only [complex.bit0_re, complex.one_re, mul_zero, sub_zero, algebra.id.smul_eq_mul, mul_eq_mul_right_iff],
  left,

  have two_inv_real : (2:ℂ)⁻¹.re = (2:ℝ)⁻¹:=
  begin
    simp only [complex.inv_re, complex.bit0_re, complex.one_re],
    rw eq_comm,
    apply eq_div_of_mul_eq,
    simp only [ne.def, monoid_with_zero_hom.map_eq_zero, bit0_eq_zero, one_ne_zero, not_false_iff],
    rw complex.norm_sq,
    dsimp,
    simp only [complex.bit0_im, complex.one_im, bit0_zero, mul_zero, add_zero, inv_mul_cancel_left₀, ne.def, bit0_eq_zero,
    one_ne_zero, not_false_iff],
  end,

  rw two_inv_real,
  rw smul_eq_mul,
  simp only [complex.mul_im, mul_zero, complex.inv_im, complex.bit0_im, complex.one_im, bit0_zero, neg_zero', zero_div, zero_mul,
  add_zero],

  exact complex_two_nez,
  exact complex_two_nez,
end

lemma hermitian_real_symm  (M : matrix n n ℝ) (herm : is_hermitian (M:matrix n n ℂ)) : M.is_symm:=
begin
  rw is_hermitian at herm,
  rw is_symm,
  
  have herm_1 : ∀ (i j : n), ((M : matrix n n ℂ)ᵀ.matrix_conj) i j = M i j,
  intros i j,
  rw herm,
  refl,

  funext i j,
  specialize herm_1 i j,
  rw matrix_trans_conj at herm_1,
  rw transpose_apply at herm_1,
  rw matrix_conj at herm_1,
  simp_rw vector_conj at herm_1,
  unfold coe at herm_1,
  unfold lift_t at herm_1,
  unfold has_lift_t.lift at herm_1,
  unfold coe_t at herm_1,
  unfold has_coe_t.coe at herm_1,
  unfold coe_b at herm_1,
  unfold has_coe.coe at herm_1,
  have trivial : ((conj (({re := M j i, im := 0}):ℂ)):ℂ) = (({re := M j i, im := 0}):ℂ),
  ext,
  rw complex.conj_re,
  rw complex.conj_im,
  unfold complex.im,
  rw neg_zero',

  rw trivial at herm_1,
  rw transpose_apply,
  have trivial_re := congr_arg complex.re herm_1,
  unfold complex.re at trivial_re,
  exact trivial_re,
end

lemma eigenvalue_prod (M : matrix n n ℂ) (N : matrix n n ℂ) 
(v : n → ℂ) (e : ℂ)  (hme : has_eigenpair M e v) (hne : has_eigenpair N e v):
has_eigenpair (M ⬝ N) (e * e) v :=
begin
  cases hme with ve hme,
  cases hne with ve hne,
  rw has_eigenpair,
  split,
  exact ve,
  rw ← mul_vec_mul_vec,
  rw hne,
  rw mul_vec_smul,
  rw hme,
  rw ← smul_assoc,
  rw ← smul_eq_mul,
end

lemma smul_magnitude (x : ℂ) (v: n → ℂ ) (h : x.im = 0): vector_magnitude (x • v) = (x * x) * vector_magnitude v :=
begin
  rw vector_magnitude,
  rw vec_smul_conj,
  
  simp only [dot_product_smul, smul_dot_product, algebra.id.smul_eq_mul, monoid_with_zero_hom.coe_mk, complex.of_real_add,
  complex.of_real_mul],
  rw ← vector_magnitude,
  rw ← mul_assoc,
  
  rw star_ring_end_apply,
  suffices x_star : star x = x,
  rw x_star,

  unfold star,
  ext,
  refl,
  rw h,
  rw neg_zero,
end

lemma mat_conj_apply (M : matrix n n ℂ) (i j : n): M.matrix_conj i j = (conj (M i j)) :=
begin
  simp_rw matrix_conj,
  rw vector_conj,
end

lemma mat_mul_conj (M N : matrix n n ℂ) : (M ⬝ N).matrix_conj = M.matrix_conj ⬝ N.matrix_conj :=
begin
  funext,
  rw matrix.mul_apply,
  rw mat_conj_apply,
  rw matrix.mul,
  simp_rw dot_product,
  rw conj_sum,
  simp_rw mul_conj,
  simp_rw mat_conj_apply,
end 

lemma prod_transpose_symm (M : matrix n n ℂ) : (M⬝Mᵀ)=(M⬝Mᵀ)ᵀ :=
begin
  funext i j,
  rw transpose_apply,
  rw matrix.mul,
  simp_rw dot_product,
  apply finset.sum_congr,
  refl,
  intros _ _,
  repeat {rw transpose_apply},
  rw mul_comm,
end

lemma sub_mul_vec (M N : matrix n n ℂ) (v : n → ℂ ) : (M-N).mul_vec v = M.mul_vec v - N.mul_vec v:=
begin
  repeat {rw sub_eq_add_neg},
  rw add_mul_vec,
  rw add_right_inj,
  funext,
  repeat{rw mul_vec},
  simp only [pi.neg_apply],
  rw mul_vec,
  simp_rw dot_product,
  rw ← finset.sum_neg_distrib,
  rw finset.sum_congr,
  refl,
  intros _ _,
  rw neg_mul,
end

lemma forall_left_dot_prod_zero_zero (u : n → ℂ) : (∀ v : (n → ℂ) , dot_product u v = 0) ↔ u = 0:=
begin
  split,
  intro dpz,
  funext,
  specialize dpz (λ i , if i = x then 1 else 0),
  rw dot_product at dpz,
  
  have key : finset.univ.sum (λ (i : n), u i * ite (i = x) 1 0) = finset.univ.sum (λ (i : n), ite (i = x) (u i) 0):=
  begin
    rw finset.sum_congr,
    refl,
    intros _ _,
    rw mul_ite,
    rw mul_one,
    rw mul_zero,
  end,

  rw key at dpz,
  rw finset.sum_ite at dpz,
  simp only [finset.sum_const_zero, add_zero] at dpz,

  have eq_x : (λ (x_1 : n), x_1 = x) = eq x,
  funext,
  rw eq_iff_iff,
  rw eq_comm,

  simp_rw eq_x at dpz,

  simp only at dpz,
  rw finset.filter_eq at dpz,
  simp only [finset.mem_univ, if_true, finset.sum_singleton] at dpz,
  rw dpz,
  rw pi.zero_apply,

  intro uz,
  intro v,
  rw uz,
  rw zero_dot_product,
end

lemma forall_right_dot_prod_zero_zero (u : n → ℂ) : (∀ v : (n → ℂ) , dot_product v u = 0) ↔ u = 0:=
begin
  simp_rw dot_product_comm,
  rw forall_left_dot_prod_zero_zero,
end

lemma eigenvalue_zero_det (M : matrix n n ℂ) (e : ℂ ) :
has_eigenvalue M e  ↔ ( (M - e • (1 : matrix n n ℂ)).det = 0) :=
begin

  have eigenvector_mul_eq_zero : ∀ (v : n → ℂ), M.mul_vec v = e • v ↔  (M - e • 1).mul_vec v = 0 :=
  begin
    intro v,
    rw sub_mul_vec,
    split,
    intro mul,
    rw mul,
    rw smul_mul_vec_assoc,
    nth_rewrite 0 ← one_mul_vec v,
    rw sub_eq_zero,

    intro sub_zero,
    rw sub_eq_zero at sub_zero,
    rw sub_zero,
    rw smul_mul_vec_assoc,
    rw one_mul_vec,
  end,

  rw  ← not_iff_not,
  rw ← ne.def,
  split,
  swap,
  intro dnz,
  by_contra ev,
  rw has_eigenvalue at ev,
  cases ev with v ev,
  rw has_eigenpair at ev,
  cases ev with vnz mul,
  specialize eigenvector_mul_eq_zero v,
  rw eigenvector_mul_eq_zero at mul,
  have vec_zero := eq_zero_of_mul_vec_eq_zero dnz mul,
  apply vnz,
  exact vec_zero,

  intro n_ev,
  rw has_eigenvalue at n_ev,

  rw ne,
  by_contra,

  have det_t : ((M - e • 1)ᵀ).det = 0 :=
  begin
    rw det_transpose,
    exact h,
  end,

  have nn : ¬¬((M - e • 1).det = 0) ↔ (M - e • 1).det = 0,
  rw not_not,

  rw ← nn at h,

  apply h,
  rw ← ne,

  rw ← nondegenerate_iff_det_ne_zero,
  rw nondegenerate,
  
  intro u,
  --exact nondegenerate.eq_zero_of_ortho,
  intro for_all,

  by_contra unz,

  simp_rw dot_product_mul_vec at for_all,
  rw forall_left_dot_prod_zero_zero at for_all,
  rename for_all vmu,
  have dpz := congr_arg (dot_product (vector_conj u)) vmu,

  rw dot_product_zero at dpz,

  have nn_t : ¬¬((M - e • 1)ᵀ.det = 0) ↔ (M - e • 1)ᵀ.det = 0,
  rw not_not,

  rw ← nn_t at det_t,
  apply det_t, 
  rw ← ne,

  rw ← nondegenerate_iff_det_ne_zero,
  rw nondegenerate,

  intro v,
  intro for_all_t,
  simp_rw dot_product_mul_vec at for_all_t,
  rw forall_left_dot_prod_zero_zero at for_all_t,
  rw vec_mul_trans at for_all_t,
  rw ← eigenvector_mul_eq_zero at for_all_t,
  rw not_exists at n_ev,
  specialize n_ev v,
  by_contra,
  apply n_ev,
  rw has_eigenpair,
  split,
  rwa ne,
  exact for_all_t,
end 

theorem eigenpair_right_trans (M : matrix n n ℂ) (v : n → ℂ) (e : ℂ):
has_eigenpair M e v ↔ has_right_eigenpair Mᵀ e v:=
begin
  rw has_eigenpair,
  rw has_right_eigenpair,
  rw vec_mul_trans,
end

theorem left_eigenvalue_right_eigenvalue (M : matrix n n ℂ) (e : ℂ):
has_eigenvalue M e ↔ has_right_eigenvalue M e :=
begin

  have right_eigenvalue_trans : has_right_eigenvalue M e ↔ has_eigenvalue Mᵀ e:=
  begin
    rw has_eigenvalue,
    rw has_right_eigenvalue,
    
    split;
    intro x;
    cases x with v ep;
    use v,
    rw ← transpose_transpose M at ep,
    rw ← eigenpair_right_trans at ep,
    exact ep,
    rw eigenpair_right_trans at ep,
    rw transpose_transpose at ep,
    exact ep,
  end,

  nth_rewrite 0 right_eigenvalue_trans,
  repeat {rw eigenvalue_zero_det},
  
  have tr : (Mᵀ - e • 1) = (M - e • 1)ᵀ,
  simp only [transpose_sub, transpose_smul, transpose_one],

  rw tr,
  rw det_transpose,
end

lemma eigenvectors_linearly_independent (M : matrix n n ℂ) (u v : n → ℂ) (e r : ℂ)
(ep_1 : has_eigenpair M e u) (ep_2 : has_eigenpair M r v) (neq : e ≠ r) :
∀ (a b : ℂ), a ≠ 0 → b ≠ 0 → a • u + b • v ≠ 0 :=
begin
  intros a b anz bnz,
  rw ne,
  by_contra lcz,
  rw has_eigenpair at ep_1 ep_2,
  cases ep_1 with unz mul_1,
  cases ep_2 with vnz mul_2,
  have m_mul := congr_arg M.mul_vec lcz,
  rw mul_vec_zero at m_mul,
  rw mul_vec_add at m_mul,
  repeat {rw mul_vec_smul at m_mul},
  rw [mul_1,mul_2] at m_mul,
  rw add_eq_zero_iff_eq_neg at lcz,
  rw smul_comm at m_mul,
  rw lcz at m_mul,
  rw smul_neg at m_mul,
  rw add_comm at m_mul,
  rw tactic.ring.add_neg_eq_sub at m_mul,
  rw smul_comm at m_mul,
  rw ← sub_smul at m_mul,
  rw smul_eq_zero at m_mul,
  cases m_mul with reqe dot_zero,
  rw ne at neq,
  apply neq,
  rw sub_eq_zero at reqe,
  rwa eq_comm,
  rw smul_eq_zero at dot_zero,
  cases dot_zero with bz vz,
  rw ne at bnz, apply bnz, exact bz,
  rw ne at vnz, apply vnz, exact vz,
end   

theorem independent_eigenvectors_linear_combination_not_eigenvector (M : matrix n n ℂ) (u v : n → ℂ) (e r : ℂ) (neq : e ≠ r)
(ep_1 : has_eigenpair M e u) (ep_2 : has_eigenpair M r v) : ∀ (a b : ℂ), a ≠ 0 → b ≠ 0 → ¬(has_eigenvector M (a•u+b•v)) :=
begin
  have epeu := ep_1,
  have eprv := ep_2,
  intros a b anz bnz,
  rw ne at anz bnz neq,
  by_contra ev,
  rw has_eigenvector at ev,
  cases ev with t ep,
  rw has_eigenpair at ep,
  cases ep with lc mul,
  rw mul_vec_add at mul,
  rw smul_add at mul,
  repeat {rw mul_vec_smul at mul},

  rw has_eigenpair at ep_1 ep_2,
  cases ep_1 with unz mul_1,
  cases ep_2 with vnz mul_2,
  rw ne at unz vnz,
  
  rw [mul_1,mul_2] at mul,

  have helper_lemma : a • (e - t) • u + b • (r - t) • v = 0,
  repeat {rw sub_smul},
  repeat {rw smul_sub},
  rw sub_add_sub_comm,
  rw sub_eq_zero,
  nth_rewrite 2 smul_comm,
  nth_rewrite 3 smul_comm,
  exact mul,

  have lin_ind := eigenvectors_linearly_independent M u v e r epeu eprv neq,
  specialize lin_ind (a • (e - t)) (b • (r - t)),

  have ent : ¬(e - t)=0 :=
  begin
    by_contra eeqt,
    rw eeqt at helper_lemma,
    rw [zero_smul, smul_zero, zero_add] at helper_lemma,
    rw smul_eq_zero at helper_lemma,
    cases helper_lemma, 
    apply bnz,
    exact helper_lemma,
    rw smul_eq_zero at helper_lemma,
    cases helper_lemma,
    rw sub_eq_zero at eeqt helper_lemma,
    apply neq,
    rw [helper_lemma,eeqt],
    apply vnz,
    exact helper_lemma,
  end,

  have rnt : ¬(r - t)=0 :=
  begin
    by_contra reqt,
    rw reqt at helper_lemma,
    rw [zero_smul, smul_zero, add_zero] at helper_lemma,
    rw smul_eq_zero at helper_lemma,
    cases helper_lemma,
    apply anz,
    exact helper_lemma,
    rw smul_eq_zero at helper_lemma,
    cases helper_lemma,
    apply ent,
    exact helper_lemma,
    apply unz,
    exact helper_lemma,
  end,

  have aemtnz : a • (e - t) ≠ 0,
  rw smul_ne_zero,
  split,
  rwa ne,
  rwa ne,

  have brmtnz : b • (r - t) ≠ 0,
  rw smul_ne_zero,
  split,
  rwa ne,
  rwa ne,

  have lin_ind_2 := lin_ind aemtnz brmtnz,
  repeat {rw smul_assoc at lin_ind_2},
  rw ne at lin_ind_2,
  apply lin_ind_2,
  exact helper_lemma,
  recover,
  refine punit.smul_comm_class,
  exact n,
  exact n,
  refine punit.smul_comm_class,
  exact n,
  exact n,
end

end definite

end matrix