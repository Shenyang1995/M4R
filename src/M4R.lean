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
fin n → G → M

def F{n:ℕ}(j:ℕ) {G : Type*}[group G](g:fin (n+1)→ G):fin n→ G
:= λ k,  if k.val < j then g ⟨k.val, lt_trans k.2 $ lt_add_one _⟩ else 
         if k.val=j then g ⟨k.val, lt_trans k.2 $ lt_add_one _⟩ *g ⟨k.val+1, add_lt_add_right k.2 1⟩  
         else g  ⟨k.val+1, add_lt_add_right k.2 1⟩  


def XYZ (n : ℕ): fin n → fin (n + 1) := coe
example : XYZ 3 ⟨2,by linarith⟩ = ⟨2, by linarith⟩ := rfl

--set_option pp.all true
theorem degenerate(n:ℕ)(j:ℕ)(k:ℕ)(G : Type*)[group G](g:fin (n+2)→ G)(h:j≤ k): 
F j (F (k+1) g) = F k (F j g):=
begin 
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


{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},




--split_ifs; try {refl}; try {rw (show (t : fin(n + 1)).val = t.val, by refl) at *},
{split_ifs;try {rw (show (↑t : fin(n + 1)).val = t.val, by refl) at *}; try {exfalso;linarith}; try {refl}; try {simp only [mul_assoc]}; try {finish}},





end

#exit
def d(n:ℕ)(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]:
(cochain n G M)→ (cochain (n+1) G M):= λ fin (n+1) → G, 
def cocycle (n:ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
{f : G → M // ∀  : G, }



def coboundary (n:ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
  {f : cocycle G M | ∃ m : M, ∀ g : G, }