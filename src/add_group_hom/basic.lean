/-additive group homomorphisms
-/

import add_subgroup.basic

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

namespace add_subgroup

def quotient.lift {A : Type*} [add_comm_group A] {C : Type*} [add_comm_group C]
  (f : A →+ C) (B : add_subgroup A) (hB : B ⊆ add_group_hom.ker f) :
B.quotient →+ C :=
{ to_fun := λ q, q.lift_on' ⇑f begin
    intros a₁ a₂ h,
    change (-a₁) + a₂ ∈ B at h,
    have h2 : f (-a₁ + a₂) = 0 := hB h,
    rwa [f.map_add, f.map_neg, neg_add_eq_iff_eq_add,
      add_zero, eq_comm] at h2,
  end,
  map_zero' := sorry,
  map_add' := sorry }

def quotient.map {A₁ : Type*} [add_comm_group A₁] {A₂ : Type*} [add_comm_group A₂]
  (B₁ : add_subgroup A₁) (B₂ : add_subgroup A₂) (f : A₁ →+ A₂) (hf : B₁.map f ⊆ B₂) :
quotient B₁ → quotient B₂ := sorry -- use quotient.lift on induced group hom A₁ → A₂/B₂

end add_subgroup
