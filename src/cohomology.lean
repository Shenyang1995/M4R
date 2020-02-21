import G_module.basic
import cochain
import algebra.pi_instances
import add_group_hom.basic
import add_subquotient.basic

variables (n:ℕ )(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]

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
If M → M


-/
