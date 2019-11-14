import algebra.group -- for is_add_group_hom
import group_theory.subgroup -- for kernels
import algebra.module

class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends  has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)

def cochain(n:ℕ)(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] := 
fin n → G → M

def F(n:ℕ)(j:ℕ ) (G : Type*)[group G](g:fin (n+1)→ G):fin n→ G
:= λ k,  if k.val < j then g k else 
         if k.val=j then g k *g (k+1)--⟨k.val+1, add_lt_add_right k.2 1⟩  
         else g (k+1)



theorem degenerate(n:ℕ)(j:ℕ)(k:ℕ)(G : Type*)[group G](g:fin (n+2)→ G)(h:j≤ k): 
F n j G (F (n+1) (k+1) G g) = F n k G (F (n+1) j G g):=sorry  

#exit
def d(n:ℕ)(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]:
(cochain n G M)→ (cochain (n+1) G M):= λ fin (n+1) → G, 
def cocycle (n:ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
{f : G → M // ∀  : G, }



def coboundary (n:ℕ) (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
  {f : cocycle G M | ∃ m : M, ∀ g : G, }