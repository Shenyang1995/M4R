import G_module.hom
import cochain
import algebra.pi_instances
import add_group_hom.basic
import add_subquotient.basic

variables (n:ℕ )(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]
(N : Type*) [add_comm_group N] [G_module G N]

def cocycle := (add_group_hom.ker (d (n+1) G M))

def coboundary := add_group_hom.range (d n G M)

theorem cob_sub_of_coc: coboundary n G M ≤ cocycle n G M:=
range_d_sub_ker_d _ G M

def cohomology : add_subquotient (cochain (n + 1) G M) :=
{bottom := coboundary n G M,
top := cocycle n G M,
incl := cob_sub_of_coc n G M}


/-

Need:

If M → P is a G-module map then there's an induced map H^n(M) → H^n(P)


-/

def cocycle.map (f : M →[G] N) : cocycle n G M →+ cocycle n G N :=
{ to_fun := λ c, ⟨cochain.map f c.1, begin
    show d.to_fun (cochain.map f c.val) = 0,
    rw ←d_map,
    have h0 : d.to_fun c.val = 0,
      exact c.property,
    rw h0,
    ext i,
    apply add_monoid_hom.map_zero,
  end⟩,
  map_zero' := sorry,
  map_add' := sorry }


def coboundary.map (f : M →[G] N) : coboundary n G M →+ coboundary n G N:=
{ to_fun := λ c, ⟨cochain.map f c.1, begin 
  sorry
  end⟩,
  map_zero' := sorry,
  map_add' := sorry }


-- next: show (cochain.map f)(cocycle) = cocycle
-- (cochain.map f)(coboundary) = coboundary




