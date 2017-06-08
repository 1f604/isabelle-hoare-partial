(*  Title:      min.thy
    Author:     1f604
    Date:       8 June 2017

Find min of 2 numbers
*)

theory min imports Hoare_Logic  begin
 
lemma min:  "VARS X Y Z a b
 {True}
X := a;
Y := b;
Z := 0; 
 WHILE X ≠ 0 ∧ Y ≠ 0
 INV {Z + min X Y = min a b ∧ 0≤X ∧ 0≤Y }
 DO X := X - (1::nat); Y := Y - (1::nat); Z := Z+(1::nat) OD
 {Z = min a b}"  
  apply vcg_simp
    apply auto  
done
 
end
