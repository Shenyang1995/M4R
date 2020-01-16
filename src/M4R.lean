import algebra.group -- for is_add_group_hom
import group_theory.subgroup -- for kernels
import algebra.module
import tactic.linarith
import tactic.omega
import tactic.fin_cases


class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends  has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)

attribute [simp] G_module.linear G_module.mul

@[simp] lemma G_module.G_neg {G : Type*} [group G] {M : Type*} [add_comm_group M]
  [G_module G M]
  (g : G) (m : M) : g • (-m) = -(g • m) := sorry

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
#print prod
#check finset.product
#check finset.range
theorem double_sum_zero1 (n':ℕ)(G : Type*)[group G](g:fin (n'+3)→ G)(M : Type*) [add_comm_group M] [G_module G M](v:cochain (n'+1) G M):
(range (n'+1)).sum(λ i, (range (n')).sum(λ j, (F2 g v (i,j)))) =0:=
begin
  rw <-sum_product,
  apply sum_involution (λ jk h, invo jk),
  { intros jk hjk,
    let j := jk.1,
    let k := jk.2,
    -- do we need these next three lines?
    cases mem_product.1 hjk with hj hk,
    replace hj : j < n' + 1 := mem_range.1 hj,
    replace hk : k < n' := mem_range.1 hk,
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
    replace hj : j < n' + 1 := mem_range.1 hj,
    replace hk : k < n' := mem_range.1 hk,
    rw finset.mem_product,
    split_ifs,
    split,
    show k+1∈ range(n'+1),
    rw mem_range,
    linarith,
    show j∈ range(n'),
    rw mem_range,
    exact lt_of_le_of_lt h hk,
    split,
    show k∈ range(n'+1),
    rw mem_range,
    linarith,
    show j-1∈ range(n'),
    rw mem_range,
    rw nat.sub_lt_left_iff_lt_add,
    linarith,
    rw not_le at h, 
    exact nat.one_le_of_lt h,}
end


#check @finset.product
#check @finset.sum_bij
#check @finset.sum_bind
#check @finset.sum_smul
#check finset.bind
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

def d{n:ℕ}{G : Type*} [group G] {M : Type*} [add_comm_group M] [G_module G M]
(φ: cochain n G M): (cochain (n+1) G M):= λ(gi: fin (n+1) → G), 
gi ⟨0, (by simp)⟩ • φ (λ i, gi ⟨i.val + 1, add_lt_add_right i.2 1⟩)
+(range (n+1)).sum(λ j,(-1:ℤ )^(j+1)• φ (F j gi))

example (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]
(φ : cochain 1 G M) (hφ : d φ = (λ i, 0)) (g h : G) : φ (λ _, g * h) = φ (λ _, g) + g • φ (λ _, h) :=
begin
  unfold d at hφ,
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

theorem d_square_zero{n:ℕ}{G : Type*} [group G] {M : Type*} [add_comm_group M] [G_module G M]
(φ: cochain n G M):d (d φ )=λ(gi: fin (n+2) → G), 0:=
begin
  unfold d,
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
  sorry  
end

#exit 
def cocycle (n:ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
{f : G → M // ∀  : G, }



def coboundary (n:ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
  {f : cocycle G M | ∃ m : M, ∀ g : G, }