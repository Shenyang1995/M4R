import algebra.group -- for is_add_group_hom
import group_theory.subgroup -- for kernels
import algebra.module
import tactic.linarith
import tactic.omega
import tactic.fin_cases
import add_group_hom.basic
import algebra.pi_instances
import G_module.basic

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

--theorem double_sum_zero (n':ℕ)(G : Type*)[group G](g:fin (n'+3)→ G)(M : Type*) [add_comm_group M] [G_module G M](v:cochain (n'+1) G M):
--(range (n'+1)).sum(λ i, (-1:ℤ)^(i+1)• (range i).sum(λ j, (-1:ℤ )^(j+1)• (v (F j (F i g))))) =0:=
--begin

--simp only [(finset.sum_smul' _ _ _).symm, smul_smul, pow_add],
--norm_num,
--simp only [pow_add'],
----simp only [degenerate2],
--sorry
--end


theorem degenerate2{n:ℕ}{j:ℕ}{k:ℕ}{G : Type*}[group G](h:j≤ k)(g:fin (n+2)→ G): 
 F k (F j g)=F j (F (k+1) g) := 
 begin 
 rw degenerate,
 exact h,
 end 

def F2{n:ℕ}{G : Type*}[group G](g:fin (n+2)→ G){M : Type*} [add_comm_group M] [G_module G M](v:cochain n G M): ℕ × ℕ → M:=
λ j, (-1:ℤ)^(j.1+j.2)• v (F (j.2) (F (j.1) g))


theorem F2_degenerate {n:ℕ}{j:ℕ}{k:ℕ}(h:j≤ k){G : Type*}[group G](g:fin (n+2)→ G){M : Type*} [add_comm_group M] [G_module G M](v:cochain n G M):
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

lemma invo_def1 {jk : ℕ × ℕ} (h : jk.1 ≤ jk.2) :
  invo jk = ⟨jk.2 + 1, jk.1⟩ := if_pos h

lemma invo_ineq1 {jk : ℕ × ℕ}
  (h : jk.1 ≤ jk.2) :
  ¬(invo jk).1 ≤ (invo jk).2 :=
begin
  unfold invo,
  rw if_pos h,
  exact not_le.2 (nat.lt_succ_of_le h),
end

lemma invo_ineq2 {jk : ℕ × ℕ}
  (h : ¬jk.1 ≤ jk.2) :
  (invo jk).1 ≤ (invo jk).2 :=
begin
  unfold invo,
  rw if_neg h,
  rw not_le at h,
  exact nat.pred_le_pred h,
end

lemma invo_aux {j k : ℕ} (h : ¬j ≤ k) : j - 1 + 1 = j :=
nat.succ_pred_eq_of_pos $ lt_of_le_of_lt (zero_le _) (lt_of_not_ge h)

lemma invo_invo (jk : ℕ × ℕ) : invo (invo jk) = jk :=
begin
  unfold invo,
  split_ifs,
  { exfalso, linarith},
  { ext, refl, simp},
  { ext, dsimp, exact invo_aux h, refl},
  { exfalso, 
    rw not_le at h_1, 
    rw nat.lt_iff_add_one_le at h_1,
    rw invo_aux h at h_1, 
    linarith,}
end

--example (n:ℕ )(x:ℕ){G : Type*}[group G](g:fin (n+2)→ G)(M : Type*) [add_comm_group M] [G_module G M](v:cochain n G M):F2 g v(x,x)=v (F (x) (F (x) g)):=rfl
--#print prod
--#check finset.product
--#check finset.range
theorem double_sum_zero1 (n':ℕ)(G : Type*)[group G](g:fin (n'+3)→ G)(M : Type*) [add_comm_group M] [G_module G M](v:cochain (n'+1) G M):
(range (n'+3)).sum(λ i, (range (n'+2)).sum(λ j, (F2 g v (i,j)))) =0:=
begin
  rw <-sum_product,
  apply sum_involution (λ jk h, invo jk),
  { intros jk hjk,
    let j := jk.1,
    let k := jk.2,
    -- do we need these next three lines?
    --cases mem_product.1 hjk with hj hk,
    --replace hj : j < n' + 1 := mem_range.1 hj,
    --replace hk : k < n' := mem_range.1 hk,
    by_cases hin : j ≤ k,
    { rw add_comm,
      convert F2_degenerate hin g v,
      exact invo_def1 hin},
    { convert F2_degenerate (invo_ineq2 hin) g v,
      unfold invo,
      rw if_neg hin,
      ext,
        exact (invo_aux hin).symm,
      refl,
    }
  },
  { intros jk hjk _ h,
    dsimp at h,
    by_cases hin : jk.1 ≤ jk.2,
    { apply invo_ineq1 hin,
      rwa h},
    { have h2 := invo_ineq2 hin,
      apply hin,
      rwa h at h2}},
  { intros jk hjk,
    dsimp,
    exact invo_invo jk, },
  { intros jk hjk,

    dsimp, 
    unfold invo,
    let j := jk.1,
    let k := jk.2,
    -- do we need these next three lines?
    cases mem_product.1 hjk with hj hk,
    replace hj : j < n' + 3 := mem_range.1 hj,
    replace hk : k < n'+ 2 := mem_range.1 hk,
    rw finset.mem_product,
    split_ifs,
    split,
    show k+1∈ range(n'+3),
    rw mem_range,
    linarith,
    show j∈ range(n'+2),
    rw mem_range,
    exact lt_of_le_of_lt h hk,
    split,
    show k∈ range(n'+3),
    rw mem_range,
    linarith,
    show j-1∈ range(n'+2),
    rw mem_range,
    rw nat.sub_lt_left_iff_lt_add,
    linarith,
    rw not_le at h, 
    exact nat.one_le_of_lt h,}
end


--#check @finset.product
--#check @finset.sum_bij
--#check @finset.sum_bind
--#check @finset.sum
--#check finset.bind

--example (a b:ℤ )(M : Type*) [add_comm_group M](c:M):(a+b) • c=a• c+b• c :=begin library_search end
--example (a b:ℕ) :(-a:ℤ ) + (-b:ℤ )=-(a+b) := begin library_search end
--#example (n:ℕ ): (-1:ℤ)^n  + (-1:ℤ)^(n+1)=0 := begin library_search end



--funext t,
--conv begin
--  to_lhs,
 -- simp only [F],
--end,
--split_ifs;try {refl}; try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith};
--rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *,
--change t.val < k + 1 at h_2,
--unfold F,
--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
--swap,
--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},


--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},

--split_ifs; try {refl}; try {rw (show (t : fin(n + 1)).val = t.val, by refl) at *},
--{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},
--end

def F_first{n:ℕ} {G : Type*}[group G](g:fin (n+1)→ G):fin n→ G
:= λ k,   g  ⟨k.val+1, add_lt_add_right k.2 1⟩ 

def d.to_fun {n:ℕ}{G : Type*} [group G] {M : Type*} [add_comm_group M] [G_module G M]
(φ: cochain n G M): (cochain (n+1) G M):= λ(gi: fin (n+1) → G), 
gi ⟨0, (by simp)⟩ • φ (λ i, gi ⟨i.val + 1, add_lt_add_right i.2 1⟩)
+(range (n+1)).sum(λ j,(-1:ℤ  )^(j+1)• φ (F j gi))

example (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]
(φ : cochain 1 G M) (hφ : d.to_fun φ = (λ i, 0)) (g h : G) : φ (λ _, g * h) = φ (λ _, g) + g • φ (λ _, h) :=
begin
  unfold d.to_fun at hφ,
  let glist : fin 2 → G := λ i, if i.val = 0 then g else if i.val = 1 then h else 1,
  have h2 : (λ (gi : fin (1 + 1) → G),
       gi ⟨0, _⟩ • φ (λ (i : fin 1), gi ⟨i.val + 1, _⟩) +
         finset.sum (finset.range (1 + 1)) (λ (j : ℕ), (-1: ℤ) ^ (j + 1) • φ (F j gi))) glist = 0,
    rw hφ,
  dsimp at h2,
  change g • φ (λ (i : fin 1), glist ⟨i.val + 1, _⟩) +
      finset.sum (finset.range (1 + 1)) (λ (j : ℕ), (-1 : ℤ) ^ (j + 1) • φ (F j glist)) =
    0 at h2,
  rw finset.sum_range_succ at h2,
  rw finset.sum_range_succ at h2,
  rw finset.sum_range_zero at h2,
  have H : (-1 : ℤ) ^ (1 + 1) = 1,
    norm_num,
  rw H at h2,
  rw one_smul at h2,
  rw ←add_assoc at h2,
  rw add_zero at h2,
  clear H,
  have H : (-1 : ℤ) ^ (0 + 1) = -1,
    norm_num,
  rw H at h2,
  rw neg_one_smul at h2,
  clear H,
  rw add_neg_eq_zero at h2,
  rw eq_comm at h2,
  rw add_comm at h2,
  convert h2,
  {
    ext,
    cases x with x hx,
    cases (nat.sub_eq_zero_of_le hx),
    refl,
  },
  { ext,
    cases x with x hx,
    cases (nat.sub_eq_zero_of_le hx),
    refl,
  },
  { ext,
    cases x with x hx,
    cases (nat.sub_eq_zero_of_le hx),
    refl,
  }
end
--theorem lt_succ_self{n j:ℕ }{H:j=nat.succ n}:n<j:=begin rw H, exact nat.lt_succ_self n,end 
theorem add_one_finset{n:ℕ }{n'=nat.succ n}{j:fin n }:j.1+1<n'+1:=begin 
have h2: n<n',
rw H, 
exact nat.lt_succ_self n,
--rw H, exact lt_add_one n,
--have h3: j.val<n',
--exact lt.trans j.is_lt h2,
norm_num,
exact lt.trans j.is_lt h2,
end

--example {a b c d:ℕ }{h1:a<c}{h2:b<d} : (a+b) < (c+b) := begin library_search end 
theorem F_0_0(n':ℕ){G : Type*}[group G](g:fin (n'+1+1+1)→ G):F 0 g ⟨0, nat.succ_pos (n'+1)⟩ = g⟨ 0, nat.succ_pos (n'+1+1) ⟩ *g⟨ 1,nat.lt_of_sub_eq_succ rfl⟩ :=
begin 
refl,
end

theorem F_0_j{n':ℕ}{j:fin (n'+1)}{G : Type*}[group G](g:fin (n'+1+1+1)→ G):F 0 g⟨ j.val+1,nat.lt_succ_iff.mpr j.is_lt

--norm_num,
--have h3:1<2,
--exact nat.lt_succ_self 1,
--exact add_lt_add (lt.trans j.is_lt h2) h3,
--end
⟩ =g⟨ j.val+2, add_lt_add_right j.is_lt 2⟩:=
begin
refl,
end

theorem F_x_0(n' x:ℕ)(h:x>0){G : Type*}[group G](g:fin (n'+1+1+1)→ G):F x g ⟨0, nat.succ_pos (n'+1)⟩ = g⟨ 0, nat.succ_pos (n'+1+1) ⟩:=
begin 
unfold F,
rw if_pos h,
end

theorem F_x_j(n' x:ℕ){G : Type*}[group G](g:fin (n'+1+1+1)→ G):F x (λ (j:fin (n'+1+1)), g ⟨j.val+1, nat.lt_succ_iff.mpr j.is_lt,⟩ ) 
= λ (j:fin (n'+1)), F (x+1) g⟨j.1+1, nat.lt_succ_iff.mpr j.is_lt,⟩:=
begin 
unfold F,
funext,
split_ifs,
{refl},
{exfalso,linarith},
{exfalso,linarith},
{exfalso,linarith},
{refl},
{have h5: k.val+1=x+1,
rw h_1,
contradiction,
},
{exfalso,linarith},
{have h5: k.val=x,
exact nat.succ_inj h_3,
contradiction},
{refl},
end
--example {n m:ℕ }(h:n+1=m+1):n=m:=by library_search

theorem sum_range_first{β : Type*} [_inst_1 : add_comm_monoid β] (f : ℕ → β) (n': ℕ): 
sum (range (n'+1)) f = f 0 + sum (range n') (λ i, f (i+1)):=
begin 
--induction n' with d hd,
--{refl},
--rw sum_range_suc
rw sum_range_succ', 
rw add_comm,
end

theorem sum_add_eq_add_sum {β : Type*} [_inst_1 : add_comm_monoid β] (f g: ℕ → β) (n: ℕ): sum (range n) (λ x, f x+g x)=sum (range n) f+sum(range n) g:=
begin 
exact sum_add_distrib,
end 

--#check @finset.sum_range_succ'
theorem d_square_zero{n:ℕ}{G : Type*} [group G] {M : Type*} [add_comm_group M] [G_module G M]
(φ: cochain n G M):d.to_fun (d.to_fun φ )=λ(gi: fin (n+2) → G), 0:=
begin
  unfold d.to_fun,
  funext,
  dsimp,
  norm_num,
  cases n with n',
  { norm_num,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_zero,
    norm_num,
    unfold F,
    split_ifs,
      cases h_1,
      { clear h h_1,
        let f : fin 0 → G := λ ⟨i, hi⟩, false.elim (by cases hi),
        have hf0 : ∀ f' : fin 0 → G, f' = f,
          intro f',
          ext i,
          cases i.2,
        have hf1 : ∀ f' : fin 0 → G, φ f' = φ f,
          intro f', rw hf0 f',
        conv begin
          to_lhs,
          congr,
            rw hf1,
            skip,
          congr,
            rw hf1,
            skip,
          congr,
            rw hf1,
            skip,
          congr,
            rw hf1,
            skip,
          congr,
            rw hf1,
            skip,
          congr,
            skip,
          rw hf1,
        end,
        simp,
      },
      cases h_1,
      cases h_1,
      cases h_2,
      dsimp at h, exfalso, apply h, norm_num,
  },

--  cases n with 0 n',
rw ←double_sum_zero1 n' G gi _ φ,
unfold F2,
dsimp,
simp only [smul_add],
rw sum_add_eq_add_sum,
rw sum_range_succ' _ (n'+2),
rw F_0_0,
simp only [F_0_j],
rw [zero_add, pow_one, neg_one_smul],
rw <-sub_eq_add_neg,
rw sub_add_eq_add_sub,
apply add_eq_of_eq_sub',
convert sub_add_cancel _ _,
  show _ = sum (range (n' + 2))
        ((λ (x : ℕ),
              (-(1 : ℤ )) ^ (x + 1 + 1) • F (x + 1) gi ⟨0, _⟩ • φ (λ (i : fin (nat.succ n')), F (x + 1) gi ⟨i.val + 1, _⟩)))+_,
simp only [F_x_0 _ _ (nat.succ_pos _)],
simp only [(F_x_j n' _ gi).symm],
rw sub_eq_add_neg,
convert add_comm _ _,
{
  simp only [(pow_add' _ _ _).symm, nat.succ_eq_add_one],
  simp only [(G_module.G_sum_smul _ _ _).symm],
  norm_num,
  simp only [G_module.neg_one_pow_mul_comm],
},
{
  simp only [(finset.sum_smul' _ _ _).symm],
  simp only [nat.succ_eq_add_one, smul_smul,pow_add'],
  simp only [(add_assoc _ _ _).symm,(pow_add' _ _ _).symm],
  norm_num,
},              
 
end
--#check neg_one_pow_eq_pow_mod_two

variables (n : ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]

instance: add_comm_group (cochain n G M):=
by unfold cochain; apply_instance

lemma sum_cochain {x y :cochain n G M}{F: fin n → G}: (x+y)(F)=x(F)+y(F):=
begin 
refl,
end

lemma zero_cochain {v :cochain n G M}: v=0 → ∀ {F: fin n → G}, v(F)=(0:M):=
begin 
intros,
exact congr_fun a F,
end

lemma G_module.zero{G : Type*} [group G] {M : Type*} [add_comm_group M]
  [G_module G M]
  :∀ g : G, g• (0:M) = 0:= begin
  intros,
  have h: g• (0:M)+g• (0:M)=g• ((0:M)+(0:M)),
  rw G_module.linear,
  rw add_zero at h,
  exact add_left_eq_self.mp h,
  end

lemma G_module.neg_one_linear (G : Type*) [group G] {M : Type*} [add_comm_group M]
[G_module G M] (n:ℕ )(m l: M):(-1:ℤ )^(n+1) • (m+l) = (-1:ℤ )^(n+1) • m + (-1:ℤ )^(n+1) • l:=
begin

induction n with d hd,
norm_num,
rw nat.succ_eq_add_one,
rw pow_add,
norm_num,
rw hd,
norm_num,
end

lemma G_module.neg_one_linear_applied {G : Type*}[group G] {M : Type*} [add_comm_group M]
[G_module G M] (i:ℕ )(gi:fin(n+1)→ G)(x y: cochain n G M): (-1:ℤ )^(i+1) • (x(F i gi)+y(F i gi)) = (-1:ℤ )^(i+1) • x(F i gi) + (-1:ℤ )^(i+1) • y(F i gi):=
begin
--have h:(-1:ℤ )^(n+1) • (m+l) = (-1:ℤ )^(n+1) • m + (-1:ℤ )^(n+1) • l,
--exact G_module.neg_one_linear G n m l, 
simp only [G_module.neg_one_linear G _ (x(F i gi)) _],
end

def d : add_group_hom (cochain n G M) (cochain (n + 1) G M) :=
{ to_fun := d.to_fun,
  map_zero' := begin 
    unfold d.to_fun, 
    funext,
    have h1: (0:cochain n G M)=0, refl,
    have h2: (0:cochain (n+1) G M)=0, refl,
    simp only [zero_cochain n G M h1],
    rw zero_cochain (n+1) G M h2,
    norm_num,
    rw G_module.zero,
  end,
  
  map_add' := begin
    unfold d.to_fun,
    intros,
    funext,
    simp only [sum_cochain, G_module.linear, G_module.neg_one_linear_applied, sum_add_distrib],
    rw [add_left_comm, <-add_assoc, add_left_comm, <-add_assoc,add_assoc],
 
  end }

theorem d_square_zero2 :d (n + 1) G M ∘ d n G M = 0 :=
begin
funext,
--dsimp,
show d.to_fun (d.to_fun x) gi=0,
rw d_square_zero x,
end 

example {β : Type*} [_inst_1 : add_comm_monoid β] (f g: ℕ → β)(i:ℕ ) :  f i+ g i=((λ (j:ℕ), f j) + λ (j:ℕ ), g j ) i:=rfl
example {β : Type*} [_inst_1 : add_comm_monoid β]{a b c d:β  }:a+b+(c+d)=a+c+(b+d):=
begin 
rw add_left_comm,
rw <-add_assoc,
rw add_left_comm,
rw <-add_assoc,
rw add_assoc,

end
