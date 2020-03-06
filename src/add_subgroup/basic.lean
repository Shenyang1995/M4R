import algebra.group.hom group_theory.subgroup group_theory.quotient_group

structure add_subgroup (G : Type*) [add_group G] :=
(carrier : set G)
(is_add_subgroup : is_add_subgroup carrier) 

namespace add_subgroup

variables (G : Type*) [add_group G]

instance foo (H : add_subgroup G) :
  _root_.is_add_subgroup H.carrier := H.is_add_subgroup

instance : has_coe (add_subgroup G) (set G) :=
⟨add_subgroup.carrier⟩

instance : has_mem G (add_subgroup G) :=
⟨λ g H, g ∈ (H : set G)⟩

theorem ext' {G : Type*} [add_group G] {H K : add_subgroup G} (h : (H : set G) = K) : H = K :=
by cases H; cases K; congr'

@[ext] theorem ext_iff {G : Type*} [add_group G] {H K : add_subgroup G} :
  (∀ g : G, g ∈ H ↔ g ∈ K) ↔ H = K :=
begin
  split,
  { intro h,
    apply ext',
    exact set.ext h
  },
  intro h, rw h, intro g, refl,
end



/- Lattice stuff -/

instance : partial_order (add_subgroup G) :=
partial_order.lift (coe : add_subgroup G → set G) (λ a b, ext') (by apply_instance)

open set

universe u

def bot {G : Type u} [add_group G] : add_subgroup G :=
{ carrier := {0},
  is_add_subgroup := { zero_mem := mem_singleton _,
  add_mem := λ a b ha hb, begin
    rw mem_singleton_iff at ha hb,
    rw [ha, hb, add_zero, mem_singleton_iff],
  end,
  neg_mem := λ a ha, begin
    rw mem_singleton_iff at ha,
    rw [ha, neg_zero, mem_singleton_iff],
  end } }

instance : lattice.has_bot (add_subgroup G) := ⟨bot⟩

def top {G : Type u} [add_group G] : add_subgroup G :=
{ carrier := univ,
  is_add_subgroup := { 
    zero_mem := mem_univ _,
    add_mem := λ _ _ _ _, mem_univ _,
    neg_mem := λ _ _, mem_univ _ } 
}

instance : lattice.has_top (add_subgroup G) := ⟨top⟩

instance : has_subset (add_subgroup G) := ⟨has_le.le⟩



variable {G} 

variables (H : add_subgroup G)

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



-- could prove that these are Galois connections and that add_subgroup G
-- is a complete lattice.

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

end add_subgroup
