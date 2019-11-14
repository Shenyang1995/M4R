inductive mylist(X:Type)
|nil:mylist
|cons: X→ mylist→ mylist

namespace mylist
def map(X Y:Type)(f:X→ Y): mylist X → mylist Y
|(nil X):=nil Y
|(cons x L):= cons (f x) (map L)

def L : mylist ℕ := mylist.cons 2 $ mylist.cons 4 $ mylist.nil ℕ

#reduce L
#reduce map ℕ ℕ (λ n, n ^ 2) L

#reduce list.map (λ n, n^2) [1,2,3] 
list.range(n)

algebra.pi_instances

def sum {G:Type} [add_group G]: mylist G → G 
|(nil G):=0
|(cons x L):= x+(sum L)

def M : mylist ℤ  := mylist.cons 2 $ mylist.cons 4 $ mylist.nil ℤ 

#check sum
#reduce sum M

end mylist