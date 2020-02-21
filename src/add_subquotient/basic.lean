import add_group_hom.basic
import data.set.basic

structure add_subquotient (A : Type*) [add_comm_group A] :=
(bottom : add_subgroup A)
(top : add_subgroup A)
(incl : bottom ≤ top)

variables (A : Type*) [add_comm_group A]

instance : has_coe_to_sort (add_subquotient A) :=
{ S := _,
  coe := λ H, quotient (
    { r := λ s t, (s : A) - t ∈ H.bottom,
    iseqv := ⟨
      begin
        intro g,
        rw sub_self,
        exact H.bottom.zero_mem,
      end, 
      begin
        intros a b,
        intro h,
        rw ←neg_sub,
        exact H.bottom.neg_mem h,
      end, 
      begin
        intros a b c,
        intros h1 h2,
        suffices : ((a : A) - b) + (b - c) ∈ H.bottom,
          convert this,
          simp,
        apply H.bottom.add_mem h1 h2,
      end⟩ 
    } : setoid H.top.carrier) }

instance (B : add_subquotient A) : add_comm_group (↥B) :=
sorry

def hi (A B : Type*) [add_comm_group A] [add_comm_group B]
(f : A →+ B) (Q : add_subquotient A) (R : add_subquotient B)
(H1 : set.image f.to_fun Q.top.carrier ⊆ R.top.carrier)
(H2 : set.image f.to_fun Q.bottom.carrier ⊆ R.bottom.carrier) :
↥Q →+ ↥R := sorry
