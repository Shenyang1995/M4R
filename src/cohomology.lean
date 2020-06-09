--import G_module.hom
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

def h0 : add_subquotient (cochain 0 G M):=
{bottom := ⊥ ,
top := (add_group_hom.ker (d 0 G M)),
incl := begin 
show  ⊥ ⊆ add_group_hom.ker (d 0 G M),
intro a,
intro ha,
rw add_subgroup.mem_coe, 
have h1:a=0,
exact ha,
rw add_group_hom.mem_ker,
rw h1,
show d.to_fun 0=0,
exact (d 0 G M).map_zero',
end}

--def H_n : add_subquotient (cochain n G M):= if n=0 then h0 G M else cohomology (n-1) G M
