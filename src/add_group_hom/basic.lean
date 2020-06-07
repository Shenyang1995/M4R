/-additive group homomorphisms
-/

import add_subgroup.basic

@[reducible] def add_group_hom (G : Type*) (H : Type*) [add_group G] [add_group H] :=
  add_monoid_hom G H

def add_group_hom.comp {G : Type*} {H : Type*} {K : Type*}
  [add_group G] [add_group H] [add_group K]
    (f : add_group_hom H K) (g : add_group_hom G H): 
  add_group_hom G K := add_monoid_hom.comp f g


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

def map {G₁ : Type*} [add_group G₁] {G₂ : Type*} [add_group G₂]
  (f : add_group_hom G₁ G₂) (H : add_subgroup G₁) : add_subgroup G₂ :=
{ carrier := (f : G₁ → G₂) '' H.carrier,
  is_add_subgroup := { 
    zero_mem := ⟨0, H.zero_mem, f.map_zero⟩,
    add_mem := begin rintros _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩,
      exact ⟨c + d, H.add_mem hc hd, f.map_add c d⟩ end,
    neg_mem := begin rintros _ ⟨c, hc, rfl⟩, exact ⟨-c, H.neg_mem hc, f.map_neg c⟩ end
  } 
}

def comap {G₁ : Type*} [add_group G₁] {G₂ : Type*} [add_group G₂]
  (f : add_group_hom G₁ G₂) (H : add_subgroup G₂) : add_subgroup G₁ :=
{ carrier := (f : G₁ → G₂) ⁻¹' H.carrier,
  is_add_subgroup := { 
    zero_mem := begin
      show f 0 ∈ H,
      rw f.map_zero,
      exact H.zero_mem
    end,
    add_mem := begin
      intros a b ha hb,
      show f (a + b) ∈ H,
      rw f.map_add,
      exact H.add_mem ha hb,
    end,
    neg_mem := begin
      intros a ha,
      show f (-a) ∈ H,
      rw f.map_neg,
      exact H.neg_mem ha
    end
  } 
}

lemma comap_comp {G₁ : Type*} [add_group G₁] {G₂ : Type*} [add_group G₂]
  {G₃ : Type*} [add_group G₃] (f : add_group_hom G₁ G₂) (g : add_group_hom G₂ G₃)
  (H : add_subgroup G₃) :
  add_group_hom.comap (g.comp f) H = add_group_hom.comap f (add_group_hom.comap g H)
  := rfl

-- this works:
--def ker (f : add_monoid_hom G H) : add_submonoid G := f.comap ⊥

def ker (f : add_group_hom G H) : add_subgroup G := add_group_hom.comap f ⊥

lemma mem_ker (f : add_group_hom G H) (g : G) : g ∈ ker f ↔ f g = 0 :=
iff.rfl

-- but f.comap ⊥ doesn't :-/

def range (f : add_group_hom G H) : add_subgroup H := add_group_hom.map f ⊤ 

def induced {f : add_group_hom G H} {G₁ : add_subgroup G}
  {H₁ : add_subgroup H} (h : f '' G₁ ⊆ H₁) :
add_group_hom G₁ H₁ :=
{ to_fun := λ g, ⟨f g.1, h ⟨g.1, g.2, rfl⟩⟩,
  map_zero' := begin 
  rw subtype.ext,
  simp,
  convert f.map_zero,
  end,
  map_add' :=  begin
  intros,
  simp [subtype.ext],
  apply f.map_add,
  end }
end add_group_hom

/- quotients -/

namespace add_subgroup

variables {A : Type*} [add_comm_group A]

@[derive add_comm_group]
def quotient (B : add_subgroup A) := quotient_add_group.quotient B.carrier

variable (B : add_subgroup A)

def quotient.mk : add_group_hom A B.quotient :=
{ to_fun := quotient.mk',
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

lemma quotient.ker_mk : add_group_hom.ker (quotient.mk B) = B :=
begin
  rw ←ext_iff,
  intro g,
  rw add_group_hom.mem_ker,
  show quotient.mk' g = quotient.mk' 0 ↔ _,
  rw quotient.eq',
  show -g + 0 ∈ B ↔ _,
  rw add_zero,
  rw neg_mem_iff,
end

def quotient.lift {A : Type*} [add_comm_group A] {C : Type*} [add_comm_group C]
  (f : add_group_hom A C) (B : add_subgroup A) (hB : B ≤ add_group_hom.ker f) :
add_group_hom B.quotient C :=
{ to_fun := λ q, q.lift_on' ⇑f begin
    intros a₁ a₂ h,
    change (-a₁) + a₂ ∈ B at h,
    have h2 : f (-a₁ + a₂) = 0 := (f.mem_ker _).1 (hB h),
    rwa [f.map_add, f.map_neg, neg_add_eq_iff_eq_add,
      add_zero, eq_comm] at h2,
  end,
  map_zero' := begin
  show f 0= 0,
  exact f.map_zero,
  end,
  map_add' := begin 
  intros x y,
  apply quotient.induction_on₂' x y,
  exact f.map_add,
  
  end }

def quotient.map {A₁ : Type*} [add_comm_group A₁] {A₂ : Type*} [add_comm_group A₂]
  (B₁ : add_subgroup A₁) (B₂ : add_subgroup A₂) (f : add_group_hom A₁ A₂)
  (hf : B₁ ≤ add_group_hom.comap f B₂) :
  add_group_hom (quotient B₁) (quotient B₂) :=
{ to_fun := quotient.lift ((quotient.mk B₂).comp f) B₁ $ le_trans hf begin
  unfold add_group_hom.ker,
  rw add_group_hom.comap_comp,
  apply le_of_eq _,
  congr',
  symmetry,
  apply quotient.ker_mk,
end,
  map_zero' := begin
    apply add_monoid_hom.map_zero,
  end,
  map_add' := by apply add_monoid_hom.map_add }

end add_subgroup
