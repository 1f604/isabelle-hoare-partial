(*  Title:      triangular.thy
    Author:     1f604
    Date:   6 June 2017

Triangular numbers.
*)

theory triangular imports Hoare_Logic  begin
 
   
lemma test:"k * (-1::int) = -k"    
    apply auto
  done
  
lemma diff_mult_distrib2: "k * (m - n) = (k * m) - (k * n)"
  for k m n :: int
  by (fact right_diff_distrib')
     
    
lemma obvious: "a = b ⟹ b = a"
  apply auto
  done

lemma diff_mult_distrib5: "k * (k + n) = (k * k) + (k * n) ⟹ (k * k) + (k * n) = k * (k + n)"
  for k m n :: nat
  by (fact obvious)
     
lemma obvious3: "k * (k-  (1::int)) = (k *k) - (k *  (1::int))"
  for k n :: int 
  apply (rule diff_mult_distrib2)
  done
    
lemma obvious4: " (k *k) - (k *  (1::int)) = k * k - k"
  apply auto
  done
    
lemma power: "a = b ⟹ a div 2 = b div 2 "
  apply auto
  done
    
lemma obvious6: "k * (k-  (1::int)) = k * k - k"
  for k :: int
  apply (simp add: obvious3 obvious4)
    done
    
lemma obvious7: "k * (k-  (1::int)) div 2 = (k * k - k) div 2"
  apply (rule power)
    apply (rule obvious6)
  done 
 
lemma t0: "a div (2::int) + c = (a + (2::int) * c) div  (2::int)"
  apply (rule obvious)
    apply auto 
done
    
lemma l1: " (k * k - k) div  (2::int) + k = (k *k - k + (2::int) * k) div (2::int) "
  apply auto
  done
    
lemma t1: " (k *k - k + (2::int) * k) = (k*k + k)"
  apply auto
  done
    
lemma l2: " (k *k - k + (2::int) * k) div  (2::int) = (k*k + k) div  (2::int)"
  apply auto
  done
    
lemma l3: " (k * k - k) div (2::int) + k = (k*k + k) div (2::int)"
  for k :: int
  apply (simp add: l1 l2)
  done 
    
lemma l4: "k * (k-  (1::int)) div (2::int) + k = (k*k + k) div (2::int)"
  apply (simp add: obvious6)
  done
    
lemma t2: "(k * k + k) = (k + 1) * k"
  for k::int  
  apply (rule  Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(2))
    done
  
lemma l5: " (k * k + k) div 2 = (k + 1) * k div 2"
  for k::int 
  apply (rule power)
    apply (rule t2)
    done
     
    
lemma triangular: "VARS s k n
 {n > 0}
s := (0::int); 
k := (1::int);
 WHILE k < n
 INV {s = k * (k- (1::int)) div (2::int) & k ≤ n}
 DO s := s + k; k := k + (1::int) OD
 {s = n * (n- (1::int)) div (2::int)}" 
  for k::int
  apply vcg_simp
    apply auto
    apply (simp add: l4 l5)
  done
    
 

end
