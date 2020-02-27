import algebra.group.hom group_theory.subgroup group_theory.quotient_group

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

instance : has_coe_to_sort (add_subgroup G) :=
{ S := _,
  coe := λ H, {g : G // g ∈ H.carrier }
}

def map {G₁ : Type*} [add_group G₁] {G₂ : Type*} [add_group G₂]
  (H : add_subgroup G₁) (f : G₁ →+ G₂) : add_subgroup G₂ :=
{ carrier := (f : G₁ → G₂) '' H.carrier,
  is_add_subgroup := { 
    zero_mem := ⟨0, H.zero_mem, f.map_zero⟩,
    add_mem := begin rintros _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩,
      exact ⟨c + d, H.add_mem hc hd, f.map_add c d⟩ end,
    neg_mem := begin rintros _ ⟨c, hc, rfl⟩, exact ⟨-c, H.neg_mem hc, f.map_neg c⟩ end
  } 
}

instance (H : add_subgroup G) : add_group ↥H :=
{ add := λ h₁ h₂, ⟨h₁.1 + h₂.1, H.add_mem h₁.2 h₂.2⟩,
  add_assoc := λ a b c, subtype.ext.2 $ add_assoc _ _ _,
  zero := ⟨0, H.zero_mem⟩,
  zero_add := λ a, subtype.ext.2 $ zero_add _,
  add_zero := λ a, subtype.ext.2 $ add_zero _,
  neg := λ h, ⟨-h.1, H.neg_mem h.2⟩,
  add_left_neg := λ a, subtype.ext.2 $ add_left_neg _ 
}

variables {A : Type*} [add_comm_group A]

instance (B : add_subgroup A) : add_comm_group ↥B :=
{ add_comm := λ a b, subtype.ext.2 $ add_comm _ _,
  ..add_subgroup.add_group B}

@[derive add_comm_group]
def quotient (B : add_subgroup A) := quotient_add_group.quotient B.carrier



end add_subgroup
