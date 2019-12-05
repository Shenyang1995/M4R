import algebra.group -- for is_add_group_hom
import group_theory.subgroup -- for kernels
import algebra.module
import tactic.linarith

class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends  has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)

def cochain(n:ℕ)(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] := 
(fin n → G) → M

def F{n:ℕ}(j:ℕ) {G : Type*}[group G](g:fin (n+1)→ G):fin n→ G
:= λ k,  if k.val < j then g ⟨k.val, lt_trans k.2 $ lt_add_one _⟩ else 
         if k.val=j then g ⟨k.val, lt_trans k.2 $ lt_add_one _⟩ *g ⟨k.val+1, add_lt_add_right k.2 1⟩  
         else g  ⟨k.val+1, add_lt_add_right k.2 1⟩  


def XYZ (n : ℕ): fin n → fin (n + 1) := coe
example : XYZ 3 ⟨2,by linarith⟩ = ⟨2, by linarith⟩ := rfl

--set_option pp.all true
theorem degenerate{n:ℕ}{j:ℕ}{k:ℕ}{G : Type*}[group G](h:j≤ k)(g:fin (n+2)→ G): 
F j (F (k+1) g) = F k (F j g):=
begin
unfold F,
funext t,
cases t with t ht,
-- I got this line by typing "dsimp"
show ite (t < j) (ite (t < k + 1) (g ⟨t, _⟩) (ite (t = k + 1) (g ⟨t, _⟩ * g ⟨t + 1, _⟩) (g ⟨t + 1, _⟩)))
      (ite (t = j)
         (ite (t < k + 1) (g ⟨t, _⟩) (ite (t = k + 1) (g ⟨t, _⟩ * g ⟨t + 1, _⟩) (g ⟨t + 1, _⟩)) *
            ite (t + 1 < k + 1) (g ⟨t + 1, _⟩)
              (ite (t + 1 = k + 1) (g ⟨t + 1, _⟩ * g ⟨t + 1 + 1, _⟩) (g ⟨t + 1 + 1, _⟩)))
         (ite (t + 1 < k + 1) (g ⟨t + 1, _⟩)
            (ite (t + 1 = k + 1) (g ⟨t + 1, _⟩ * g ⟨t + 1 + 1, _⟩) (g ⟨t + 1 + 1, _⟩)))) =
    ite (t < k) (ite (t < j) (g ⟨t, _⟩) (ite (t = j) (g ⟨t, _⟩ * g ⟨t + 1, _⟩) (g ⟨t + 1, _⟩)))
      (ite (t = k)
         (ite (t < j) (g ⟨t, _⟩) (ite (t = j) (g ⟨t, _⟩ * g ⟨t + 1, _⟩) (g ⟨t + 1, _⟩)) *
            ite (t + 1 < j) (g ⟨t + 1, _⟩)
              (ite (t + 1 = j) (g ⟨t + 1, _⟩ * g ⟨t + 1 + 1, _⟩) (g ⟨t + 1 + 1, _⟩)))
         (ite (t + 1 < j) (g ⟨t + 1, _⟩)
            (ite (t + 1 = j) (g ⟨t + 1, _⟩ * g ⟨t + 1 + 1, _⟩) (g ⟨t + 1 + 1, _⟩)))),
by_cases h1 : t < j,
{ rw if_pos h1,
  rw if_pos (lt_trans h1 (nat.lt_succ_of_le h)),
  --rw if_pos (show t < k, from lt_of_lt_of_le h1 h),
  rw if_pos (lt_of_lt_of_le h1 h),
  rw if_pos h1
},
rw if_neg h1,
by_cases h2:t=j,
{ rw if_pos (h2),
  cases h2,
  rw if_pos (nat.lt_succ_of_le h),
  rw le_iff_eq_or_lt at h,
  cases h,
  {cases h,
  rw if_neg (lt_irrefl (j+1)),
  rw if_pos (rfl),
  rw if_neg (lt_irrefl j),
  rw if_pos (rfl),
  rw if_neg (lt_irrefl j),
  rw if_pos (rfl),
  rw if_neg (show ¬ (j+1<j), from mt (le_of_lt) (nat.not_succ_le_self j) ), 
  rw if_neg (show ¬ (j+1=j), from mt (le_of_eq) (nat.not_succ_le_self j) ), 
  rw mul_assoc,
    },
  {rw if_pos (nat.succ_lt_succ h),
  rw if_pos h,
  rw if_neg (lt_irrefl j),
  rw if_pos rfl,
  },
},
rw if_neg h2,
by_cases h3 : t < k, 
{  rw if_pos (nat.lt_succ_iff.2 h3),
   rw if_pos h3,
   rw if_neg h1,
   rw if_neg h2,

},
rw if_neg (mt nat.lt_succ_iff.1 h3),
by_cases h4 : t = k,
{  cases h4,
   rw if_pos rfl,
   rw if_neg (lt_irrefl k),
   rw if_pos rfl,
   rw if_neg h1,
   rw if_neg h2,
   rw if_neg (not_lt_of_le (le_trans h (nat.le_succ k))),
   rw if_neg (ne_of_gt (nat.succ_le_succ h) : ¬ (k + 1 = j)),
},
rw if_neg (mt (nat.succ_inj) h4),
rw if_neg h3,
rw if_neg h4,
have h5: ¬ t+1<j, by linarith,
rw if_neg h5,
have h6: ¬ t+1=j, by linarith,
rw if_neg h6,
-- no goal!
end

--example (j : ℕ) : ¬ (j+1<j) := mt (le_of_lt) (nat.not_succ_le_self j)

theorem neg_one_power(n:ℕ )(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]
: ∀ m : M, ((-1:ℤ)^n  + (-1:ℤ)^(n+1)) • m = 0 := 
begin 
intro m,
induction n with h hd,
norm_num,
rw nat.succ_eq_add_one,
rw pow_add (-1:ℤ ) h 1,
rw pow_add (-1:ℤ ) h (1+1),
norm_num,

end

--open_locale add_group

theorem neg_degenerate (n:ℕ)(j:ℕ)(k:ℕ)(G : Type*)[group G](g:fin (n+2)→ G)(h:j≤ k) (M : Type*) [add_comm_group M] [G_module G M](v:cochain n G M)
: (-1:ℤ)^(j+k+1) • (v (F j (F (k+1) g))) + (-1:ℤ)^(j+k)• (v (F k (F j g)))=0:=
begin 
rw degenerate h,
--show gsmul ((-1) ^ n) (v (F k (F j g))) + gsmul ((-1) ^ (n + 1)) (v (F k (F j g))) = 0,
rw <-add_smul,
--show ((-1 : ℤ) ^ n + (-1) ^ (n + 1)) • (v (F k (F j g))) = 0,
rw add_comm,
rw neg_one_power (j+k) G M,
end

open finset
def finset.sum_smul' {α : Type*} {R : Type*} [semiring R] {M : Type*} [add_comm_monoid M]
  [semimodule R M] (s : finset α) (r : R) (f : α → M) :
    finset.sum s (λ (x : α), (r • (f x))) = r • (finset.sum s f) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [_root_.smul_add] {contextual := tt})

theorem pow_add'(a : ℤ ) (m n : ℕ): a ^ m * a ^ n=a ^ (m + n) :=
begin 
rw pow_add,
end

theorem double_sum_zero (n':ℕ)(G : Type*)[group G](g:fin (n'+3)→ G)(M : Type*) [add_comm_group M] [G_module G M](v:cochain (n'+1) G M):
(range (n'+1)).sum(λ i, (-1:ℤ)^(i+1)• (range i).sum(λ j, (-1:ℤ )^(j+1)• (v (F j (F i g))))) =0:=
begin

simp only [(finset.sum_smul' _ _ _).symm, smul_smul, pow_add],
norm_num,
simp only [pow_add'],
--simp only [degenerate2],
sorry
end


theorem degenerate2{n:ℕ}{j:ℕ}{k:ℕ}{G : Type*}[group G](h:j≤ k)(g:fin (n+2)→ G): 
 F k (F j g)=F j (F (k+1) g) := 
 begin 
 rw degenerate,
 exact h,
 end 

def F2{n:ℕ}{G : Type*}[group G](g:fin (n+2)→ G){M : Type*} [add_comm_group M] [G_module G M](v:cochain n G M): ℕ × ℕ → M:=
λ j, (-1:ℤ)^(j.1+j.2)• v (F (j.2) (F (j.1) g))


theorem F2_degenerate {n:ℕ}(j:ℕ)(k:ℕ)(h:j≤ k){G : Type*}[group G](g:fin (n+2)→ G){M : Type*} [add_comm_group M] [G_module G M](v:cochain n G M):
F2 g v (k+1, j)+F2 g v (j, k)=0:=
begin 
unfold F2,
norm_num,
rw add_comm,
rw <-add_assoc,
rw neg_degenerate,
exact h,
end

def invo : ℕ × ℕ → ℕ × ℕ :=
λ jk, if jk.1 ≤ jk.2 then ⟨jk.2 + 1, jk.1⟩ else ⟨jk.2, jk.1 - 1⟩

--example (n:ℕ )(x:ℕ){G : Type*}[group G](g:fin (n+2)→ G)(M : Type*) [add_comm_group M] [G_module G M](v:cochain n G M):F2 g v(x,x)=v (F (x) (F (x) g)):=rfl
#print prod
#check finset.product
#check finset.range
theorem double_sum_zero1 (n':ℕ)(G : Type*)[group G](g:fin (n'+3)→ G)(M : Type*) [add_comm_group M] [G_module G M](v:cochain (n'+1) G M):
(range (n'+1)).sum(λ i, (range (n')).sum(λ j, (F2 g v (i,j)))) =0:=
begin
  rw <-sum_product,
  apply sum_involution (λ jk h, invo jk),
  { sorry },
  { sorry },
  { sorry },
  { sorry }
end

#check @finset.product
#check @finset.sum_bij
#check @finset.sum_bind
#check @finset.sum_smul
#check finset.bind
--example (a b:ℤ )(M : Type*) [add_comm_group M](c:M):(a+b) • c=a• c+b• c :=begin library_search end
--example (a b:ℕ) :(-a:ℤ ) + (-b:ℤ )=-(a+b) := begin library_search end
--#example (n:ℕ ): (-1:ℤ)^n  + (-1:ℤ)^(n+1)=0 := begin library_search end
#exit 


funext t,
conv begin
  to_lhs,
  simp only [F],
end,
split_ifs;try {refl}; try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith};
--rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *,
--change t.val < k + 1 at h_2,
unfold F,
{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
swap,
{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},


--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},




--split_ifs; try {refl}; try {rw (show (t : fin(n + 1)).val = t.val, by refl) at *},
--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},





end

#exit
def d(n:ℕ)(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]:
(cochain n G M)→ (cochain (n+1) G M):= λ fin (n+1) → G, 
def cocycle (n:ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
{f : G → M // ∀  : G, }



def coboundary (n:ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
  {f : cocycle G M | ∃ m : M, ∀ g : G, }