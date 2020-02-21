import algebra.group.hom group_theory.subgroup

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