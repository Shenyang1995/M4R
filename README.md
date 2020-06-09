# M4R : Group Cohomology in Lean

This is my MSCi research project at Imperial College London in 2019-2020, with special thanks to my supervisor Kevin Buzzard.

This project successfully formalizes a general definition for n cohomology group in Lean. 

Some basic explanations on the structure of the files:

     - cochain.lean contains definitions of cochain and differential, and the proof of the most important lemma d^2=0. 

     - cohomology.lean contains definitions of cocycle, coboundary, and cohomology
     
     - induced_maps.lean contains work towards the long exact sequence. Already done: induced homomorphism on cochain, commutative diagram
     and induced homomorphism on cohomology. 
     
     - G_module contains bundled G_module.basic and bundled G_module_hom. 
     
     - add_subgroup.basic bundle has definition of add_subgroup, its properties, and special examples of add_subgroup.
     
     - add_group_hom.basic bundle has definition of add_group_hom, its properties, and definition of kernel and range.
     
     - add_subquotient bundle has definition of add_subquotient, its properties and definition of induced map on add_subquotient.


Some Future Work: 

     - There are still some sorry to fill. But none of these affect the content of this project itself.
     
     - Most of the code are still uncommented. 
     
     - Next goals: definition of exactness, induced long exact sequence of group cohomology ......
