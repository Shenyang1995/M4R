import add_group_hom.basic
import data.set.basic
import group_theory.quotient_group

structure add_subquotient (A : Type*) [add_comm_group A] :=
(bottom : add_subgroup A)
(top : add_subgroup A)
(incl : bottom ≤ top)

namespace add_subquotient 

variables {A : Type*} [add_comm_group A] (Q : add_subquotient A)

instance add_subquotient.add_comm_group.top : add_comm_group Q.top := by apply_instance

instance add_subquotient.add_comm_group.bottom : add_comm_group Q.bottom := by apply_instance

def top.bottom_add_subgroup (Q : add_subquotient A) : add_subgroup (Q.top) :=
{ carrier := {b : ↥Q.top | b.1 ∈ Q.bottom},
  is_add_subgroup := { 
    zero_mem := Q.bottom.zero_mem,
    add_mem := λ a b, Q.bottom.add_mem,
    neg_mem := λ a, Q.bottom.neg_mem
  }
}

instance : has_coe_to_sort (add_subquotient A) :=
{ S := _,
  coe := λ H, (add_subquotient.top.bottom_add_subgroup H).quotient }
  
instance (B : add_subquotient A) : add_comm_group (↥B) := by apply_instance

def to_add_monoid_hom {A B : Type*}[add_comm_group A] [add_comm_group B]
{f : A →+ B} {Q : add_subquotient A} {R : add_subquotient B}
(H1 : set.image f.to_fun Q.top.carrier ⊆ R.top.carrier)
(H2 : set.image f.to_fun Q.bottom.carrier ⊆ R.bottom.carrier) :
↥Q →+ ↥R := add_subgroup.quotient.map _ _ (add_group_hom.induced H1) begin
  intros x hx,
  apply H2,
  use x,
  split,
    exact hx,
  refl,
end

end add_subquotient
