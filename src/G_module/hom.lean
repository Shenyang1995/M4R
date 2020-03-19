import G_module.basic

variables (G : Type*) [group G]
variables (M : Type*) [add_comm_group M] [G_module G M]
variables (N : Type*) [add_comm_group N] [G_module G N]

structure G_module_hom :=
(f : M →+ N)
(smul : ∀ g : G, ∀ m : M, f (g • m) = g • (f m))

instance : has_coe (G_module_hom G M N) (add_group_hom M N) := ⟨G_module_hom.f⟩

notation M ` →[`:25 G:25 `] `:0 N:0 := G_module_hom G M N

namespace G_module_hom

variables {G} {M} {N}

def zero : M →[G] N := sorry

def id : M →[G] M := sorry

variables {P : Type*} [add_comm_group P] [G_module G P]

def comp (α : M →[G] N) (β : N →[G] P) : M →[G] P := sorry

lemma id_comp {α : M →[G] N} : comp id α = α := sorry

lemma comp_id {α : M →[G] N} : comp α id = α := sorry

variables {Q : Type*} [add_comm_group Q] [G_module G Q]

lemma comp_assoc {α : M →[G] N} {β : N →[G] P} {γ : P →[G] Q} :
  comp (comp α β) γ = comp α (comp β γ) := sorry

-- could do zero_comp, comp_zero

variable (α : M →[G] N)

example : ⇑α = α.f.to_fun := rfl

lemma map_add {m n : M} : (α : M → N) (m + n) = (α : M → N) m + (α : M → N) n := 
add_monoid_hom.map_add (α.f) m n

lemma map_smul {g : G} {m : M} : (α : M → N) (g • m) = g • ((α : M → N) m) := 
G_module_hom.smul α g m

lemma map_sum (I : Type*) (φ : I → M) (s : finset I) :
    α (finset.sum s φ) = finset.sum s (λ (x : I), α (φ x)) :=
add_monoid_hom.map_sum α.f φ s 

end G_module_hom

