theory Exercise4_2 imports Main begin

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof
  let ?n = "(length xs + 1) div 2"
  
  show "\<exists>zs. xs = take ?n xs @ zs \<and> 
        (length (take ?n xs) = length zs \<or> length (take ?n xs) = length zs + 1)"
  proof
    let ?zs = "drop ?n xs"
    
    show "xs = take ?n xs @ ?zs \<and>
         (length (take ?n xs) = length ?zs \<or> 
          length (take ?n xs) = length ?zs + 1)"
    proof
      show "xs = take ?n xs @ ?zs" by fastforce
      
      show "length (take ?n xs) = length ?zs \<or> length (take ?n xs) = length ?zs + 1"
      proof -
        have take_len: "length (take ?n xs) = ?n" by force
        have drop_len: "length ?zs = length xs - ?n" by force
        
        have "?n = (length xs + 1) div 2" by simp
        
        have "even (length xs) \<or> odd (length xs)" by simp
        thus ?thesis
        proof
          assume "even (length xs)"
          hence "length xs = 2 * (length xs div 2)" by simp
          hence "?n = length xs div 2" by simp
          with drop_len have "length ?zs = length xs div 2" by linarith
          with take_len show ?thesis by linarith
        next
          assume "odd (length xs)"
          hence "length xs = 2 * (length xs div 2) + 1" by force
          hence "?n = length xs div 2 + 1" by fastforce
          with drop_len have "length ?zs = length xs div 2" by linarith
          with take_len show ?thesis by linarith
        qed
      qed
    qed
  qed
qed

end