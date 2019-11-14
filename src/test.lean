import algebra.group -- for is_add_group_hom
import group_theory.subgroup -- for kernels
import algebra.module

class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends  has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)

attribute [simp] G_module.linear

definition H0 (G : Type*) [group G] (M : Type*) [add_comm_group M]
[G_module G M]
:= {m : M // ∀ g : G, g • m = m}

variables (G : Type*) [group G] (M : Type*) [add_comm_group M]
[G_module G M]

variables {G} {M}

lemma g_zero (g : G) : g • (0 : M) = 0 :=
begin
  have h : 0 + g • (0 : M) = g • 0 + g • 0,
    calc
    0 + g • (0 : M) = g • 0 : zero_add _
    ...             = g • (0 + 0) : by rw [add_zero (0 : M)]
    ...         = g • 0 + g • 0 : G_module.linear g 0 0,
   symmetry,
   exact add_right_cancel h
end


#check g_zero

lemma g_neg (g : G) (m : M) : g • (-m) = -(g• m) :=
begin
  apply eq_neg_of_add_eq_zero,
  rw ←G_module.linear,
  rw neg_add_self,
  exact g_zero g
end

lemma G_module.map_sub (g : G) (m n : M) : g • (m - n) = g • m - g • n :=
begin
  rw eq_sub_iff_add_eq,
  rw ←G_module.linear,
  congr',
  rw sub_add_cancel
end


theorem H0.add_closed (m n : M)
  (hm : ∀ g : G, g • m = m) (hn : ∀ g : G, g • n = n) :
∀ g : G, g • (m + n) = m + n :=
begin
  intro g,
  rw G_module.linear,
  rw hm,
  rw hn,
end

instance H0.add_comm_group : add_comm_group (H0 G M) :=
{ add := λ x y, ⟨x.1 + y.1, H0.add_closed x.1 y.1 x.2 y.2⟩,
  add_assoc := λ a b c, subtype.eq (add_assoc _ _ _),
  /- begin
    intros a b c,
    apply subtype.eq,
--    show a.val + b.val + c.val = a.val + (b.val + c.val),
    exact add_assoc _ _ _
  end ,-/
  zero := ⟨0,g_zero⟩,
  zero_add := λ a, subtype.eq (zero_add _),
  add_zero := λ a, subtype.eq (add_zero _),
  neg := λ x, ⟨-x.1, λ g, by rw [g_neg g x.1, x.2]⟩,
  add_left_neg := λ a, subtype.eq (add_left_neg _),
  add_comm := λ a b, subtype.eq (add_comm _ _)}

  variables {N : Type*} [add_comm_group N] [G_module G N]

variable (G)

class G_module_hom (f : M → N)  : Prop :=
(add : ∀ a b : M, f (a + b) = f a + f b)
(G_hom : ∀ g : G, ∀ m : M, f (g • m) = g • (f m))

instance G_module_hom.is_add_group_hom (f : M → N) [G_module_hom G f] : 
is_add_group_hom f :=
{map_add := G_module_hom.add G f}

lemma H0.G_module_hom (f : M → N) [G_module_hom G f] (g : G) (m : M)
(hm : ∀ g : G, g • m = m):
g • f m = f m :=
begin
  rw ←G_module_hom.G_hom f,
  rw hm g,
  apply_instance
end

def H0_f (f : M → N) [G_module_hom G f] : H0 G M → H0 G N :=
λ x, ⟨f x.1, λ g, H0.G_module_hom G f g x.1 x.2⟩

instance (f : M → N) [G_module_hom G f] : is_add_group_hom (H0_f G f) 
:= { map_add := 
begin  
  intro a,
  intro b,
  cases a,
  cases b,
  apply subtype.eq,
  show f(a_val + b_val) = f a_val + f b_val,
  apply G_module_hom.add G f
end }

instance id.G_module_hom : G_module_hom G (id : M → M) :=
{ add := 
begin
  intros,
  refl
end,
G_hom :=
begin
  intros,
  refl
end}


open set is_add_group_hom
open function

/-- A->B->C -/
def is_exact {A B C : Type*} [add_comm_group A] [add_comm_group B] [add_comm_group C]
  (f : A → B) (g : B → C) [is_add_group_hom f] [is_add_group_hom g] : Prop :=
range f = ker g 

/-- 0->A->B->C->0 -/
def short_exact {A B C : Type*} [add_comm_group A] [add_comm_group B] [add_comm_group C]
  (f : A → B) (g : B → C) [is_add_group_hom f] [is_add_group_hom g] : Prop :=
  function.injective f ∧ 
  function.surjective g ∧ 
  is_exact f g

lemma H0inj_of_inj {A B : Type*} [add_comm_group A] [G_module G A] 
[add_comm_group B] [G_module G B] (f : A → B) 
(H1 : injective f) [G_module_hom G f] : injective (H0_f G f) := 
begin
  intro x,
  intro y,
  intro H,
  unfold H0_f at H,
  simp at H,
  have H3 : x.val = y.val,
    exact H1 H,
  exact subtype.eq H3    
end

/- H0(G,A) -> H0(G,B) -> H0(G,C) -/
lemma h0_exact {A B C : Type*} [add_comm_group A] [G_module G A] 
[add_comm_group B] [G_module G B] [add_comm_group C] [G_module G C]
  (f : A → B) (g : B → C)  (H1 : injective f) [G_module_hom G f]
  [G_module_hom G g] (H2 : is_exact f g) : is_exact (H0_f G f) (H0_f G g) :=
  begin
    change range f = ker g at H2,
    apply subset.antisymm,
    { /- intro x,
      cases x with x h,
      intro h2,
      cases h2 with a ha,
      cases a with a propa,
      -/
      rintros ⟨x,h⟩ ⟨⟨a, _⟩, ha⟩,
      rw mem_ker,
      apply subtype.eq,
      show g x = 0,
      rw [←mem_ker g, ←H2],
      use a,
      injection ha,
    },
    { rintros ⟨x,h⟩ hx,
      rw mem_ker at hx,
      unfold H0_f at hx,
      injection hx with h2,
      change g x = 0 at h2,
      rw ← mem_ker g at h2,
      rw ← H2 at h2,
      cases h2 with a ha,
      have h2a : ∀ g : G, g • a = a,
      { intro g,
      apply H1,
      rw G_module_hom.G_hom f,
      rw ha,
      exact h g,
      apply_instance,},
      use ⟨a, h2a⟩,
      apply subtype.eq,
      unfold H0_f,
      exact ha,
    }
  end