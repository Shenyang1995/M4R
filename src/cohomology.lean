import G_module.basic
import cochain
import algebra.pi_instances
import add_group_hom.basic


variables (n:ℕ )(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]

def cocycle := (add_group_hom.ker (d (n+1) G M))

def coboundary := add_group_hom.im (d n G M)

#check cocycle n G M
#check coboundary


theorem cob_sub_of_coc: coboundary n G M ≤ cocycle n G M:=
begin 
assume x,
unfold cocycle,
unfold add_group_hom.ker,
unfold coboundary,
unfold add_group_hom.im,
--dsimp,
--unfold set.range,
--show (∃ (y : cochain n G M), d.to_fun y = x )→  d.to_fun x=0,
simp,
intros y h,
rw <-h,
exact d_square_zero y,

end

def cohomology : add_subquotient (cochain (n + 1) G M) :=
{bottom := coboundary n G M,
top := cocycle n G M,
incl := cob_sub_of_coc n G M}

#check cohomology n G M

