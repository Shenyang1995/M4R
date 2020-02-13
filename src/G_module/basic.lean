import algebra.group -- for is_add_group_hom
import group_theory.subgroup -- for kernels
import algebra.module
import tactic.linarith
import tactic.omega
import tactic.fin_cases
import add_group_hom.basic
import algebra.pi_instances

class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends  has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)

attribute [simp] G_module.linear G_module.mul

@[simp] lemma G_module.G_neg {G : Type*} [group G] {M : Type*} [add_comm_group M]
  [G_module G M]
  (g : G) (m : M) : g • (-m) = -(g • m) := 
  begin
  -- h1: g • (m+(-m))=(0:M),
  --norm_num,
 -- have h: g• (0:M)+g• (0:M)=g• ((0:M)+(0:M)),
  --rw G_module.linear,
 -- rw add_zero at h,
  --exact add_left_eq_self.mp h,
  --rw G_module.linear at h1,
  --have h2:g • m + g • -m -(g• m)= -(g• m),
 -- exact add_left_eq_self.mpr h1,
 -- have h3:g • m + g • -m -(g• m)= g • -m,
 -- exact add_sub_cancel' _ _,
 -- exact (eq.congr rfl h2).mp (eq.symm h3),
 have h:g • -m +g • m= -(g • m)+g • m,
 rw <-G_module.linear,
 norm_num,
 have h: g• (0:M)+g• (0:M)=g• ((0:M)+(0:M)),
 rw G_module.linear,
 rw add_zero at h,
 exact add_left_eq_self.mp h,
 exact (add_right_inj (g • m)).mp h,
  end


lemma G_module.G_sum_smul {G : Type*} [group G] {M : Type*} [add_comm_group M]
[G_module G M] (n:ℕ )(g : G)(f: ℕ → M):finset.sum  (finset.range (n+1))(λ (x : ℕ ), g • f x) = g • finset.sum (finset.range(n+1)) f:=
begin 
induction n with d hd,
norm_num,
rw finset.sum_range_succ,
rw hd,
rw <-G_module.linear,
rw <-finset.sum_range_succ _ (d+1),
end

lemma G_module.neg_one_pow_mul_comm {G : Type*} [group G] {M : Type*} [add_comm_group M]
[G_module G M] (n:ℕ  )(g:G)(m:M): (-1:ℤ )^n • g • m = g • (-1:ℤ)^n • m:=
begin
induction n with d hd,
norm_num,
rw nat.succ_eq_add_one,
rw pow_add,
norm_num,
exact hd,
end