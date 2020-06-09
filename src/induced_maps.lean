import cohomology
import G_module.hom

variables {G : Type*} [group G]
variables {M : Type*}[add_comm_group M] [G_module G M]
variables {N : Type*} [add_comm_group N] [G_module G N]
variables {n : ℕ}
def cochain.map (f : M →[G] N) : cochain n G M → cochain n G N :=
λ b c, f (b c)

theorem d_map (f : M →[G] N) (c : cochain n G M) :
cochain.map f (d.to_fun c) = d.to_fun (cochain.map f c) :=
begin
  ext gs,
  unfold d.to_fun,
  unfold cochain.map,
  rw f.map_add,
  rw f.map_smul,
  rw f.map_sum,
  congr',
  ext x,
  show (f.f) _ = _,
  exact add_monoid_hom.map_gsmul _ _ _,
end


def cocycle.map (f : M →[G] N) : cocycle n G M → cocycle n G N :=
λ c, ⟨cochain.map f c.1, begin
    show d.to_fun (cochain.map f c.val) = 0,
    rw ←d_map,
    have h0 : d.to_fun c.val = 0,
      exact c.property,
    rw h0,
    ext i,
    apply add_monoid_hom.map_zero,
  end⟩


def coboundary.map (f : M →[G] N) : coboundary n G M → coboundary n G N:=
 λ c, ⟨cochain.map f c.1, begin 
  unfold coboundary, 
unfold add_group_hom.range,
unfold add_group_hom.map,
dsimp,
rw set.mem_image,
have h0: ∃ (x : cochain n G M), d.to_fun x = c.val,
sorry,
rcases h0 with ⟨ y, hy1⟩,
use cochain.map f y,
split,
trivial,
rw <-hy1,
exact (d_map f y).symm,
  end⟩

def cochain.hom (f : M →[G] N) : cochain n G M →+ cochain n G N :=
{ to_fun := cochain.map f,
  map_zero' := begin unfold cochain.map, ext, apply add_monoid_hom.map_zero, end,
  map_add' := begin intros, unfold cochain.map, funext, apply add_monoid_hom.map_add,end }

lemma cocycle.map_incl (f : M →[G] N): set.image (cochain.hom f).to_fun (cohomology n G M).top.carrier ⊆ (cohomology n G N).top.carrier:= begin 
unfold cochain.hom,
unfold cohomology,
unfold set.image,
intros  x hx,
show d.to_fun x = 0,
cases hx with a ha,
have h2: cochain.map f a=x, exact and.right ha, 
rw <-h2,
rw ←d_map,
have h0 : d.to_fun a = 0,
exact and.left ha,
rw h0,
ext i,
apply add_monoid_hom.map_zero,
end

lemma coboundary.map_incl (f : M →[G] N): set.image (cochain.hom f).to_fun (cohomology n G M).bottom.carrier ⊆ (cohomology n G N).bottom.carrier:= 
begin
unfold cochain.hom,
unfold cohomology,
unfold set.image,
dsimp, 
rintros x ⟨ a, ha1, h2⟩ ,
rw <-h2,

unfold coboundary, 
unfold add_group_hom.range,
unfold add_group_hom.map,
dsimp,
rw set.mem_image,

unfold coboundary at ha1,
unfold add_group_hom.range at ha1,
unfold add_group_hom.map at ha1,
dsimp at ha1,
rw set.mem_image at ha1,
rcases ha1 with ⟨ y, hy1, hy2⟩,
use cochain.map f y,
split,
trivial,
rw <-hy2,
exact (d_map f y).symm,
end

def cohomology.map (f : M →[G] N) : cohomology n G M →+ cohomology n G N:=
add_subquotient.to_add_monoid_hom (cocycle.map_incl f) (coboundary.map_incl f)

/-

Need:

If M → P is a G-module map then there's an induced map H^n(M) → H^n(P)

this is cohomology.map (what about n)
-/