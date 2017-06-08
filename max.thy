(*  Title:      max.thy
    Author:     1f604
    Date:   8 Jun 2017

Proof for max-element search in non-zero length array
*)

theory max imports Hoare_Logic    begin
 
    
(* Search for the maximum element *)
lemma max_search: "VARS m A i
 {True} 
 i := 1;
 m := A!0;
 WHILE i < length(A::(int)list) 
 INV {(∀j. (j::nat)<(i::nat) ⟶ A!j ≤ (m::int)) ∧ ( ∃k. (k::nat)< length A ⟶ A!k = (m::int))  }
 DO 
  IF m < A!i THEN m := A!i ELSE m := m FI;
  i := i+1 
 OD 
 {(∀j. (j::nat)< length A --> A!j ≤ (m::int)) ∧ ( ∃k. (k::nat)< length A ⟶ A!k = (m::int)) }"
  apply vcg_simp
    apply auto
  using less_Suc_eq by auto 

 
end
