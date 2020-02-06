/-additive group homomorphisms
-/

import algebra.group.hom group_theory.subgroup


@[reducible] def add_group_hom (G : Type*) (H : Type*) [add_group G] [add_group H] :=
  add_monoid_hom G H

def add_group_hom.mk {G : Type*} [add_group G] {H : Type*} [add_group H] (f : G → H)
(h : ∀ a b : G, f(a + b) = f a + f b) : add_group_hom G H :=
{ to_fun := f,
  map_zero' := begin
    sorry
  end,
  map_add' := h }

structure add_subgroup (G : Type*) [add_group G] :=
(carrier : set G)
(is_add_subgroup : is_add_subgroup carrier) 

namespace add_group_hom

variables {G : Type*} {H : Type*} [add_group G] [add_group H]

def ker (f : add_group_hom G H) : add_subgroup G :=
{ carrier := {x : G | f x = 0},
  is_add_subgroup := { 
    zero_mem := f.map_zero,
    add_mem := begin
      intros a b ha hb,
      change f a = 0 at ha,
      change f b = 0 at hb,
      show f (a + b) = 0,
      rw [f.map_add, ha, hb, add_zero],
    end,
    neg_mem := begin
      sorry
    end
  }
}

def im (f : add_group_hom G H) : add_subgroup H :=
{ carrier := set.range f,
  is_add_subgroup := { 
    zero_mem := begin
      use 0,
      exact f.map_zero
    end,
    add_mem := begin
      sorry
    end,
    neg_mem := begin
      intro b,
      intro hb,
      cases hb with a ha,
--      unfold set.range,
--      unfold has_mem.mem set.mem set_of,
      use -a,
      rw [f.map_neg, ha],
    end
  }
}

end add_group_hom
