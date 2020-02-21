/-additive group homomorphisms
-/

import algebra.group.hom group_theory.subgroup


@[reducible] def add_group_hom (G : Type*) (H : Type*) [add_group G] [add_group H] :=
  add_monoid_hom G H

def add_group_hom.mk {G : Type*} [add_group G] {H : Type*} [add_group H] (f : G → H)
(h : ∀ a b : G, f(a + b) = f a + f b) : add_group_hom G H :=
{ to_fun := f,
  map_zero' := begin
    have h1: f (0:G) + f 0=f((0:G)+(0:G)), 
    rw h,
    norm_num at h1,
    exact h1,
  end,
  map_add' := h }

structure add_subgroup (G : Type*) [add_group G] :=
(carrier : set G)
(is_add_subgroup : is_add_subgroup carrier) 

instance foo (G : Type*) [add_group G] (H : add_subgroup G) :
  is_add_subgroup H.carrier := H.is_add_subgroup

instance (G : Type*) [add_group G] : has_le (add_subgroup G) :=
⟨λ H K, H.carrier ⊆ K.carrier⟩

instance (G : Type*) [add_group G] : has_subset (add_subgroup G) :=
⟨λ H K, H.carrier ⊆ K.carrier⟩

instance (G : Type*) [add_group G] : has_mem G (add_subgroup G) :=
⟨λ g H, g ∈ H.carrier⟩

namespace add_subgroup

variables {G : Type*} [add_group G] (H : add_subgroup G)

def zero_mem : (0 : G) ∈ H :=
begin
  exact _root_.is_add_submonoid.zero_mem H.carrier,
end

def neg_mem {g : G} : g ∈ H → -g ∈ H :=
begin
  intro h,
  show -g ∈ H.carrier,
  exact _root_.is_add_subgroup.neg_mem h,
end

def add_mem {g h : G} : g ∈ H → h ∈ H → g + h ∈ H :=
begin
  intros H1 H2,
  show g + h ∈ H.carrier,
  exact _root_.is_add_submonoid.add_mem H1 H2,
end

end add_subgroup

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
      intros a ha,
      change f a = 0 at ha,
      show f (-a ) = 0,
      have h2: f (a+(-a))=0,
      norm_num,
      --have h3: f(a)+f(-a)=0,
      rw f.map_add at h2,
      rw ha at h2,
      rw zero_add at h2, exact h2,
    end
  }
}

def range (f : add_group_hom G H) : add_subgroup H :=
{ carrier := set.range f,
  is_add_subgroup := { 
    zero_mem := begin
      use 0,
      exact f.map_zero
    end,
    add_mem := begin
      intros a b ha hb,
      cases ha with c hc,
      cases hb with d hd,
      use c+d,
      rw [f.map_add, hc, hd],
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

structure add_subquotient (G : Type*) [add_group G] :=
(bottom : add_subgroup G)
(top : add_subgroup G)
(incl : bottom ≤ top)

variables (G : Type*) [add_group G]

instance : has_coe_to_sort (add_subquotient G) :=
{ S := _,
  coe := λ H, quotient (
    { r := λ s t, (s : G) - t ∈ H.bottom,
    iseqv := ⟨
      begin
        intro g,
        rw sub_self,
        exact H.bottom.zero_mem,
      end, 
      begin
        intros a b,
        intro h,
        rw ←neg_sub,
        exact H.bottom.neg_mem h,
      end, 
      begin
        intros a b c,
        intros h1 h2,
        suffices : ((a : G) - b) + (b - c) ∈ H.bottom,
          convert this,
          simp,
        apply H.bottom.add_mem h1 h2,
      end⟩ 
    } : setoid H.top.carrier) }
